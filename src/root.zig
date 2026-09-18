const std = @import("std");

var max_leaf: usize = 4;
var max_children: usize = 2;

pub const Summary = struct {
    bytes: usize,
    lines: usize,

    pub const zero: Summary = .{ .bytes = 0, .lines = 0 };

    pub fn add(a: Summary, b: Summary) Summary {
        return .{ .bytes = a.bytes + b.bytes, .lines = a.lines + b.lines };
    }
};

fn summarizeBytes(bytes: []const u8) Summary {
    var lines: usize = 0;
    for (bytes) |b| {
        if (b == '\n') lines += 1;
    }
    return .{ .bytes = bytes.len, .lines = lines };
}

fn recomputeSummary(children: []const *Node) Summary {
    var s: Summary = .zero;
    for (children) |child| s = Summary.add(s, child.summary);
    return s;
}

pub const DeltaOp = union(enum) {
    copy: struct { start: usize, end: usize },
    insert: []const u8,
};

pub const Delta = struct {
    ops: []DeltaOp,
    base_len: usize,

    fn deinit(self: Delta, allocator: std.mem.Allocator) void {
        allocator.free(self.ops);
    }

    const Edit = struct { start: usize, end: usize, text: []const u8 };

    fn fromEdits(allocator: std.mem.Allocator, base_len: usize, edits: []const Edit) !Delta {
        var ops: std.ArrayList(DeltaOp) = .empty;
        var pos: usize = 0;

        for (edits) |e| {
            std.debug.assert(e.start >= pos and e.end <= base_len);
            if (e.start > pos) try ops.append(allocator, .{ .copy = .{ .start = pos, .end = e.start } });
            if (e.text.len > 0) try ops.append(allocator, .{ .insert = e.text });
            pos = e.end;
        }

        if (pos < base_len) try ops.append(allocator, .{ .copy = .{ .start = pos, .end = base_len } });
        return .{ .ops = try ops.toOwnedSlice(allocator), .base_len = base_len };
    }
};

pub const Transformer = struct {
    delta: Delta,

    fn transform(self: Transformer, old_pos: usize) usize {
        var new_cursor: usize = 0;
        var old_cursor: usize = 0;

        for (self.delta.ops) |op| {
            switch (op) {
                .copy => |c| {
                    if (old_pos >= c.start and old_pos < c.end) return new_cursor + (old_pos - c.start);
                    new_cursor += c.end - c.start;
                    old_cursor = c.end;
                },
                .insert => |text| {
                    if (old_pos == old_cursor) return new_cursor + text.len;
                    new_cursor += text.len;
                },
            }
        }

        return new_cursor;
    }
};

pub const Node = struct {
    refs: std.atomic.Value(usize) = .init(1),
    height: usize,
    summary: Summary,
    body: union(enum) {
        leaf: []u8,
        internal: []*Node,
    },

    pub fn createLeaf(allocator: std.mem.Allocator, bytes: []u8) !*Node {
        const node = try allocator.create(Node);
        node.* = .{
            .height = 0,
            .summary = summarizeBytes(bytes),
            .body = .{ .leaf = bytes },
        };
        return node;
    }

    pub fn createInternal(allocator: std.mem.Allocator, children: []*Node, height: usize) !*Node {
        const node = try allocator.create(Node);
        node.* = .{
            .height = height,
            .summary = recomputeSummary(children),
            .body = .{ .internal = children },
        };
        return node;
    }

    pub fn retain(self: *Node) *Node {
        _ = self.refs.fetchAdd(1, .monotonic);
        return self;
    }

    pub fn release(self: *Node, allocator: std.mem.Allocator) void {
        if (self.refs.fetchSub(1, .acq_rel) != 1) return;

        switch (self.body) {
            .leaf => |bytes| allocator.free(bytes),
            .internal => |children| {
                for (children) |child| child.release(allocator);
                allocator.free(children);
            },
        }
        allocator.destroy(self);
    }
};

const UTF8_LEAD_BITS_MASK: u8 = 0xC0;
const UTF8_CONTINUATION_BITS: u8 = 0x80;
fn isUtf8Continuation(byte: u8) bool {
    return (byte & UTF8_LEAD_BITS_MASK == UTF8_CONTINUATION_BITS);
}

fn isCrlfBoundary(text: []const u8, end: usize) bool {
    return end > 0 and text[end - 1] == '\r' and text[end] == '\n';
}

const EditResult = union(enum) {
    single: *Node,
    split: struct { left: *Node, right: *Node },
};

const DeleteResult = union(enum) {
    kept: *Node,
    removed: void,
};

fn editLeaf(allocator: std.mem.Allocator, node: *Node, start: usize, end: usize, insert: []const u8) !EditResult {
    const bytes = node.body.leaf;
    const new_len = bytes.len - (end - start) + insert.len;

    const buf = try allocator.alloc(u8, new_len);
    @memcpy(buf[0..start], bytes[0..start]);
    @memcpy(buf[start .. start + insert.len], insert);
    @memcpy(buf[start + insert.len ..], bytes[end..]);

    if (new_len <= max_leaf) {
        if (node.refs.load(.acquire) == 1) {
            allocator.free(bytes);
            node.body = .{ .leaf = buf };
            node.summary = summarizeBytes(buf);
            return .{ .single = node };
        } else {
            const new_node = try Node.createLeaf(allocator, buf);
            node.release(allocator);
            return .{ .single = new_node };
        }
    } else {
        var i = @divFloor(new_len, 2);
        while (i > 0) : (i -= 1) {
            if (!isUtf8Continuation(buf[i]) and !(i > 0 and buf[i] == '\n' and buf[i - 1] == '\r')) break;
        }

        const l = try Node.createLeaf(allocator, try allocator.dupe(u8, buf[0..i]));
        const r = try Node.createLeaf(allocator, try allocator.dupe(u8, buf[i..]));
        allocator.free(buf);
        node.release(allocator);
        return .{ .split = .{ .left = l, .right = r } };
    }
}

fn editAt(allocator: std.mem.Allocator, node: *Node, node_start: usize, start: usize, end: usize, insert: []const u8) !?EditResult {
    switch (node.body) {
        .leaf => return try editLeaf(allocator, node, start - node_start, end - node_start, insert),
        .internal => |children| {
            var offset = node_start;
            for (children, 0..) |child, i| {
                const child_end = offset + child.summary.bytes;
                if (start >= offset and end <= child_end) {
                    const shared = node.refs.load(.acquire) > 1;
                    const child_ref = if (shared) child.retain() else child;
                    // TODO: handle multi leaf edit (the editAt -> null case)
                    const child_result = try editAt(allocator, child_ref, offset, start, end, insert) orelse {
                        if (shared) child.release(allocator);
                        return null;
                    };

                    switch (child_result) {
                        .single => |new_child| {
                            if (!shared) {
                                children[i] = new_child;
                                node.summary = recomputeSummary(children);
                                return .{ .single = node };
                            } else {
                                const new_children = try allocator.alloc(*Node, children.len);
                                for (children, 0..) |c, j| {
                                    new_children[j] = if (j == i) new_child else c.retain();
                                }
                                node.release(allocator);
                                return .{ .single = try Node.createInternal(allocator, new_children, node.height) };
                            }
                        },
                        .split => |s| {
                            const height = node.height;

                            var new_children = try allocator.alloc(*Node, children.len + 1);
                            for (children[0..i], 0..) |c, j| {
                                new_children[j] = if (shared) c.retain() else c;
                            }
                            new_children[i] = s.left;
                            new_children[i + 1] = s.right;
                            for (children[i + 1 ..], 0..) |c, j| {
                                new_children[i + j + 2] = if (shared) c.retain() else c;
                            }

                            if (shared) {
                                node.release(allocator);
                            } else {
                                allocator.free(children);
                            }

                            if (new_children.len <= max_children) {
                                if (shared) {
                                    return .{ .single = try Node.createInternal(allocator, new_children, height) };
                                } else {
                                    node.body = .{ .internal = new_children };
                                    node.summary = recomputeSummary(new_children);
                                    return .{ .single = node };
                                }
                            }

                            const mid = @divFloor(new_children.len, 2);
                            const left_children = try allocator.dupe(*Node, new_children[0..mid]);
                            const right_children = try allocator.dupe(*Node, new_children[mid..]);
                            allocator.free(new_children);
                            if (!shared) allocator.destroy(node);

                            return .{
                                .split = .{
                                    .left = try Node.createInternal(allocator, left_children, height),
                                    .right = try Node.createInternal(allocator, right_children, height),
                                },
                            };
                        },
                    }
                }
                offset = child_end;
            }
            return null;
        },
    }
}

fn deleteRange(allocator: std.mem.Allocator, node: *Node, node_start: usize, del_start: usize, del_end: usize) !DeleteResult {
    if (del_start <= node_start and del_end >= node_start + node.summary.bytes) {
        node.release(allocator);
        return .removed;
    }

    switch (node.body) {
        .leaf => {
            const result = try editLeaf(allocator, node, del_start - node_start, del_end - node_start, "");
            return .{ .kept = result.single };
        },
        .internal => |children| {
            var offset = node_start;
            var start_i: usize = 0;
            var end_i: usize = 0;
            var start_offset: usize = 0;
            var end_offset: usize = 0;
            var start_child_end: usize = 0;
            for (children, 0..) |child, i| {
                const child_end = offset + child.summary.bytes;

                if (del_start >= offset and del_start < child_end) {
                    start_i = i;
                    start_offset = offset;
                    start_child_end = child_end;
                }
                if (del_end - 1 >= offset and del_end - 1 < child_end) {
                    end_i = i;
                    end_offset = offset;
                }

                offset = child_end;
            }

            const shared = node.refs.load(.acquire) > 1;

            var new_children: std.ArrayList(*Node) = .empty;
            defer new_children.deinit(allocator);

            for (children[0..start_i]) |child| {
                try new_children.append(allocator, if (shared) child.retain() else child);
            }

            const start_child_ref = if (shared) children[start_i].retain() else children[start_i];
            switch (try deleteRange(allocator, start_child_ref, start_offset, del_start, @min(del_end, start_child_end))) {
                .kept => |n| try new_children.append(allocator, n),
                .removed => {},
            }

            if (end_i > start_i) {
                for (children[start_i + 1 .. end_i]) |child| child.release(allocator);

                const end_child_ref = if (shared) children[end_i].retain() else children[end_i];
                switch (try deleteRange(allocator, end_child_ref, end_offset, @max(del_start, end_offset), del_end)) {
                    .kept => |n| try new_children.append(allocator, n),
                    .removed => {},
                }
            }

            for (children[end_i + 1 ..]) |child| {
                try new_children.append(allocator, if (shared) child.retain() else child);
            }

            if (shared) {
                node.release(allocator);
            } else {
                allocator.free(children);
            }

            const result_children = try new_children.toOwnedSlice(allocator);

            if (result_children.len == 0) {
                allocator.free(result_children);
                if (!shared) allocator.destroy(node);
                return .removed;
            }
            if (result_children.len == 1) {
                const only_child = result_children[0];
                allocator.free(result_children);
                if (!shared) allocator.destroy(node);
                return .{ .kept = only_child };
            }

            if (shared) {
                return .{ .kept = try Node.createInternal(allocator, result_children, node.height) };
            } else {
                node.body = .{ .internal = result_children };
                node.summary = recomputeSummary(result_children);
                return .{ .kept = node };
            }
        },
    }
}

pub const Tree = struct {
    allocator: std.mem.Allocator,
    root: *Node,

    fn fromText(allocator: std.mem.Allocator, text: []const u8) !Tree {
        var leaves: std.ArrayList(*Node) = .empty;
        defer leaves.deinit(allocator);
        var i: usize = 0;

        while (i < text.len) {
            var end = @min(i + max_leaf, text.len);
            if (end < text.len) {
                while (end > i and (isUtf8Continuation(text[end]) or isCrlfBoundary(text, end))) : (end -= 1) {}
            }

            const owned = try allocator.dupe(u8, text[i..end]);
            try leaves.append(allocator, try Node.createLeaf(allocator, owned));
            i = end;
        }

        if (leaves.items.len == 0) {
            const empty = try allocator.dupe(u8, "");
            try leaves.append(allocator, try Node.createLeaf(allocator, empty));
        }

        var level = try leaves.toOwnedSlice(allocator);
        var height: u8 = 0;
        while (level.len > 1) {
            var next: std.ArrayList(*Node) = .empty;
            var j: usize = 0;
            while (j < level.len) {
                const n = @min(max_children, level.len - j);
                const children = try allocator.dupe(*Node, level[j .. j + n]);
                try next.append(allocator, try Node.createInternal(allocator, children, height + 1));
                j += n;
            }
            allocator.free(level);
            level = try next.toOwnedSlice(allocator);
            height += 1;
        }

        const root = level[0];
        allocator.free(level);
        return .{ .allocator = allocator, .root = root };
    }

    fn deinit(self: Tree) void {
        self.root.release(self.allocator);
    }

    fn len(self: Tree) usize {
        return self.root.summary.bytes;
    }

    fn lineCount(self: Tree) usize {
        return self.root.summary.lines;
    }

    fn clone(self: Tree) Tree {
        return .{ .allocator = self.allocator, .root = self.root.retain() };
    }

    fn toText(self: Tree) ![]u8 {
        return collectText(self.allocator, self.root);
    }

    fn edit(self: *Tree, start: usize, end: usize, insert: []const u8) !void {
        const height = self.root.height;
        if (try editAt(self.allocator, self.root, 0, start, end, insert)) |new_root| {
            switch (new_root) {
                .single => |node| self.root = node,
                .split => |s| {
                    const new_children = try self.allocator.dupe(*Node, &.{ s.left, s.right });
                    self.root = try Node.createInternal(self.allocator, new_children, height + 1);
                },
            }
            return;
        }

        const del_result = try deleteRange(self.allocator, self.root, 0, start, end);
        switch (del_result) {
            .kept => |n| self.root = n,
            .removed => self.root = try Node.createLeaf(self.allocator, try self.allocator.dupe(u8, "")),
        }

        if (insert.len > 0) {
            if (try editAt(self.allocator, self.root, 0, start, start, insert)) |new_root| {
                switch (new_root) {
                    .single => |node| self.root = node,
                    .split => |s| {
                        const new_children = try self.allocator.dupe(*Node, &.{ s.left, s.right });
                        self.root = try Node.createInternal(self.allocator, new_children, self.root.height + 1);
                    },
                }
                return;
            }
        }
    }

    fn chunkAtOffset(self: Tree, byte_offset: usize) struct { text: []const u8, chunk_start: usize, steps: usize } {
        var node = self.root;
        var steps: usize = 0;
        var offset: usize = 0;
        while (true) {
            steps += 1;

            switch (node.body) {
                .leaf => |bytes| return .{ .text = bytes, .chunk_start = offset, .steps = steps },
                .internal => |children| {
                    var acc = offset;
                    for (children, 0..) |child, i| {
                        if (byte_offset < acc + child.summary.bytes or i == children.len - 1) {
                            node = child;
                            offset = acc;
                            break;
                        }
                        acc += child.summary.bytes;
                    }
                },
            }
        }
    }

    fn byteOfLineStart(self: Tree, target_line: usize) usize {
        if (target_line == 0) return 0;

        var node = self.root;
        var byte_offset: usize = 0;
        var lines_before: usize = 0;

        while (true) {
            switch (node.body) {
                .leaf => |bytes| {
                    var seen = lines_before;
                    for (bytes, 0..) |b, i| {
                        if (b == '\n') {
                            seen += 1;
                            if (seen == target_line) return byte_offset + i + 1;
                        }
                    }
                    return byte_offset + bytes.len;
                },
                .internal => |children| {
                    for (children) |c| {
                        if (lines_before + c.summary.lines >= target_line) {
                            node = c;
                            break;
                        }

                        lines_before += c.summary.lines;
                        byte_offset += c.summary.bytes;
                    }
                },
            }
        }
    }

    fn applyDelta(self: *Tree, delta: Delta) !void {
        std.debug.assert(delta.base_len == self.len());
        const old = try self.toText();
        defer self.allocator.free(old);

        var out: std.ArrayList(u8) = .empty;
        defer out.deinit(self.allocator);
        for (delta.ops) |op| {
            switch (op) {
                .copy => |c| try out.appendSlice(self.allocator, old[c.start..c.end]),
                .insert => |t| try out.appendSlice(self.allocator, t),
            }
        }

        self.root.release(self.allocator);
        self.* = try Tree.fromText(self.allocator, out.items);
    }
};

fn collectText(allocator: std.mem.Allocator, node: *Node) ![]u8 {
    switch (node.body) {
        .leaf => |bytes| return try allocator.dupe(u8, bytes),
        .internal => |children| {
            var out: std.ArrayList(u8) = .empty;
            defer out.deinit(allocator);

            for (children) |child| {
                const child_text = try collectText(allocator, child);
                defer allocator.free(child_text);
                try out.appendSlice(allocator, child_text);
            }

            return out.toOwnedSlice(allocator);
        },
    }
}

test "toText prints correct text" {
    const alloc = std.testing.allocator;

    const tree = try Tree.fromText(alloc, "abcdefgh\nijklmnoprst");
    defer tree.deinit();

    const text = try tree.toText();
    defer alloc.free(text);

    try std.testing.expectEqualStrings("abcdefgh\nijklmnoprst", text);
}

test "fromText accepts empty string" {
    const alloc = std.testing.allocator;

    const tree = try Tree.fromText(alloc, "");
    defer tree.deinit();

    try std.testing.expectEqual(0, tree.len());
}

test "no leaf size overflow edit" {
    const alloc = std.testing.allocator;

    max_leaf = 2;

    var tree = try Tree.fromText(alloc, "abcdef");
    defer tree.deinit();

    try tree.edit(2, 4, "CD");

    const text = try tree.toText();
    defer alloc.free(text);

    try std.testing.expectEqualStrings("abCDef", text);
}

test "leaf size overflow edit" {
    const alloc = std.testing.allocator;

    max_leaf = 2;

    var tree = try Tree.fromText(alloc, "abcdef");
    defer tree.deinit();

    try tree.edit(2, 4, "CDE");

    const text = try tree.toText();
    defer alloc.free(text);

    try std.testing.expectEqualStrings("abCDEef", text);
}

test "two leaves edit" {
    const alloc = std.testing.allocator;

    max_leaf = 2;

    var tree = try Tree.fromText(alloc, "abcdef");
    defer tree.deinit();

    try tree.edit(2, 5, "CDE");

    const text = try tree.toText();
    defer alloc.free(text);

    try std.testing.expectEqualStrings("abCDEf", text);
}

test "multi-level split, tree grows in height" {
    const alloc = std.testing.allocator;

    max_children = 2;
    max_leaf = 2;

    var tree = try Tree.fromText(alloc, "abcd");
    defer tree.deinit();
    const height = tree.root.height;

    try tree.edit(2, 4, "cdef");

    const text = try tree.toText();
    defer alloc.free(text);

    try std.testing.expectEqualStrings("abcdef", text);
    try std.testing.expectEqual(height + 1, tree.root.height);
}

test "delete text" {
    const alloc = std.testing.allocator;

    max_leaf = 2;

    var tree = try Tree.fromText(alloc, "abcdef");
    defer tree.deinit();

    try tree.edit(2, 4, "");

    const text = try tree.toText();
    defer alloc.free(text);

    try std.testing.expectEqualStrings("abef", text);
}

test "merge on delete" {
    const alloc = std.testing.allocator;

    max_leaf = 2;

    var tree = try Tree.fromText(alloc, "abcdef");
    defer tree.deinit();

    try tree.edit(2, 4, "");

    try std.testing.expectEqual(1, tree.root.height);
}

test "utf8 break guard" {
    const alloc = std.testing.allocator;

    max_leaf = 4;
    max_children = 2;

    const tree = try Tree.fromText(alloc, "abc∂ef");
    defer tree.deinit();

    const text = try tree.toText();
    defer alloc.free(text);

    try std.testing.expectEqualStrings("abc", tree.chunkAtOffset(0).text);
    try std.testing.expectEqualStrings("∂e", tree.chunkAtOffset(3).text);
    try std.testing.expectEqualStrings("f", tree.chunkAtOffset(7).text);

    try std.testing.expectEqualStrings("abc∂ef", text);
}

test "crlf break guard" {
    const alloc = std.testing.allocator;

    max_leaf = 4;
    max_children = 2;

    const tree = try Tree.fromText(alloc, "abc\r\ndef");
    defer tree.deinit();

    const text = try tree.toText();
    defer alloc.free(text);

    try std.testing.expectEqualStrings("abc", tree.chunkAtOffset(0).text);
    try std.testing.expectEqualStrings("\r\nde", tree.chunkAtOffset(3).text);
    try std.testing.expectEqualStrings("f", tree.chunkAtOffset(7).text);

    try std.testing.expectEqualStrings("abc\r\ndef", text);
}

test "clone copy-on-write" {
    const alloc = std.testing.allocator;

    max_leaf = 2;

    var tree = try Tree.fromText(alloc, "abcdef");
    defer tree.deinit();

    var tree_clone = tree.clone();
    defer tree_clone.deinit();

    try tree.edit(4, 6, "EF");
    try tree_clone.edit(2, 4, "CD");

    const text = try tree.toText();
    defer alloc.free(text);
    try std.testing.expectEqualStrings("abcdEF", text);

    const text_clone = try tree_clone.toText();
    defer alloc.free(text_clone);
    try std.testing.expectEqualStrings("abCDef", text_clone);
}
