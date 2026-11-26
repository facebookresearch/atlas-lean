/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.RectangleCapacityNondecreasingWords

open MetaMathlibExt

-- The finite bounds in the capacity definition also specify the width-zero case.
example : rectangleCapacity 2 0 [1, 3] = 10 := by decide

-- A window wider than the word has no placements.
example : nondecreasingRectangleTotal 3 1 3 2 = 0 := by decide

-- This count includes overlapping windows and multiple vertical placements.
example : nondecreasingRectangleTotal 3 2 2 3 = 15 := by decide

-- A height larger than every letter gives zero at every admissible length.
example (n : ℕ) (hn : 2 ≤ n) : (nondecreasingRectangleTotal 2 4 2 n : ℤ) = 0 := by
  simpa using (nondecreasingRectangleTotal_r_by_s 2 4 2 (by decide) (by decide) (by decide)).2 n hn

-- At width one the higher numerator coefficients vanish.
example : (nondecreasingRectangleTotal 3 2 1 3 : ℤ) = 30 := by
  rw [(nondecreasingRectangleTotal_r_by_s 3 2 1 (by decide) (by decide) (by decide)).2 3
    (by decide)]
  decide

-- With one letter, the unique word has one placement at each possible starting position.
example (s n : ℕ) (hs : 1 ≤ s) (hn : s ≤ n) :
    (nondecreasingRectangleTotal 1 1 s n : ℤ) = ((n - s + 1 : ℕ) : ℤ) := by
  simpa [Nat.add_comm 1 s] using (nondecreasingRectangleTotal_one_by_s 1 s le_rfl hs).2 n hn

-- At length four both terms of the signed sum contribute for width two over two letters.
example : (nondecreasingRectangleTotal 2 1 2 4 : ℤ) = 21 := by
  rw [(nondecreasingRectangleTotal_one_by_s 2 2 (by decide) (by decide)).2 4 (by decide)]
  decide
