/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.KdTree.Planar
public import Mathlib.Data.String.Basic
public meta import CSLibExt.Algorithms.Lean.DataStructures.KdTree.Planar
public meta import Mathlib.Data.String.Basic

/-! # Planar rank-index tests -/

public meta section

namespace Cslib.Algorithms.Lean.KdTree.Planar.Tests

private def pts : List (Int × Int) := [(9, 2), (1, 4), (7, 8), (3, 0), (5, 6)]
private def idx := (preprocess pts).1

-- The x and y orders disagree. Five points split into two and three; the three
-- split into one and two. Both dictionaries persist after construction.
#guard idx.byX == #[(1, 4), (3, 0), (5, 6), (7, 8), (9, 2)] && idx.byY == #[0, 2, 4, 6, 8]
#guard idx.tree.toList.map (fun p => (p 0, p 1)) == [(2, 0), (0, 4), (8, 2), (4, 6), (6, 8)]
#guard idx.tree.storedNodes == 9 && (preprocess pts).2 == 116

-- Contains every leaf: all nine constructors and all five output lookups count.
#guard idx.query (0, 0) (10, 10) == ([(3, 0), (1, 4), (9, 2), (5, 6), (7, 8)], 29)
-- Zero-width query at the root median x; zero-height query at its right child's median y.
#guard idx.query (5, 0) (5, 9) == ([(5, 6)], 21)
#guard idx.query (0, 6) (10, 6) == ([(5, 6)], 24)
#guard idx.query (7, 8) (7, 8) == ([(7, 8)], 21)
-- Partial overlap; cut coordinates need not be input keys.
#guard idx.query (2, 1) (8, 7) == ([(5, 6)], 27)
-- Both axis intervals contain a key, but their intersection has no point.
#guard idx.query (5, 2) (5, 2) == ([], 18)
-- A disjoint interval and a reversed one are rejected before tree traversal.
#guard idx.query (20, 1) (30, 7) == ([], 15)
#guard idx.query (4, 0) (3, 9) == ([], 14)

#guard (preprocess ([] : List (Int × Int))).1.query (0, 0) (0, 0) == ([], 5)
#guard (preprocess ([(2, 8)] : List (Int × Int))).1.query (2, 8) (2, 8) == ([(2, 8)], 11)
-- Occurrences are not deduplicated, even for this example outside general position.
#guard (preprocess ([(1, 1), (1, 1), (1, 2)] : List (Int × Int))).1.query (1, 1) (1, 1) ==
  ([(1, 1), (1, 1)], 19)

-- Ordered nonnumeric keys: neither x endpoint occurs in the stored dictionary.
#guard ((preprocess [("aa", "z"), ("cc", "a"), ("ee", "c")]).1.query ("bb", "a") ("dd", "y")).1 ==
  [("cc", "a")]

end Cslib.Algorithms.Lean.KdTree.Planar.Tests
