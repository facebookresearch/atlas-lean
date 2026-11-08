/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.CompositionIndexSets

namespace MetaMathlibExt

-- Boundary characteristics at `n = 0`.
example : compositionHalfIndexSet 5 0 3 = ∅ := compositionHalfIndexSet_zero 5 3
example : compositionIndexSet 5 0 3 = ∅ := compositionIndexSet_zero 5 3

-- Concrete membership: `T(5, 6, 1)` contains `0` and `5`, but not `1`.
example : (5 : ℕ) ∈ compositionIndexSet 5 6 1 := by
  rw [mem_compositionIndexSet]; decide
example : (0 : ℕ) ∈ compositionIndexSet 5 6 1 := by
  rw [mem_compositionIndexSet]; decide
example : (1 : ℕ) ∉ compositionIndexSet 5 6 1 := by
  rw [mem_compositionIndexSet]; decide

-- Concrete membership: `S(5, 7, 1)` contains `3` (`2·3 ≡ 6 (mod 5)`, `6 < 7`).
example : (3 : ℕ) ∈ compositionHalfIndexSet 5 7 1 := by
  rw [mem_compositionHalfIndexSet]; decide

-- The doubling identity (Bowman Lemma 18), at a concrete instance and in general.
example : compositionHalfIndexSet 6 10 2 = compositionIndexSet 3 5 1 :=
  compositionHalfIndexSet_double 3 5 1
example (m n q : ℕ) :
    compositionHalfIndexSet (2 * m) (2 * n) (2 * q) = compositionIndexSet m n q :=
  compositionHalfIndexSet_double m n q

end MetaMathlibExt
