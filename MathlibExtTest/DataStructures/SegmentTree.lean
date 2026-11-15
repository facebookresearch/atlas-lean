/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.DataStructures.SegmentTree

@[expose] public section

/-- A two-leaf tree has 3 nodes and satisfies the bound. -/
example : (SegTree.node (SegTree.leaf 1) (SegTree.leaf 2)).size + 1
    ≤ 2 * (SegTree.node (SegTree.leaf 1) (SegTree.leaf 2)).leaves :=
  SegTree.size_add_one_le _

end
