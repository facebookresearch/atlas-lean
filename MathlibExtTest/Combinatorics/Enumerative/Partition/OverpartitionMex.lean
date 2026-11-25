/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.OverpartitionMex

namespace MetaMathlibExt.sigmaMexOverpartition_parity

-- An overline removes only one of two equal parts. The remaining copy still counts toward the mex.
private def twoOnes : Nat.Overpartition 2 :=
  Nat.Overpartition.full (Nat.Partition.ofMultiset {1, 1})

example : nonOverlinedCount twoOnes 1 = 1 := by decide
example : leastGapOverpartition 1 twoOnes = 2 := by
  rw [leastGapOverpartition, dite_eq_right (by decide : 1 ≠ 0), Nat.find_eq_iff]
  decide
example : leastGapOverpartition 2 twoOnes = 1 := by
  rw [leastGapOverpartition, dite_eq_right (by decide : 2 ≠ 0), Nat.find_eq_iff]
  decide
example : leastGapOverpartition 0 twoOnes = 0 := by decide

-- At zero the unique overpartition contributes one, and both parity cases occur at positive sizes.
example : sigmaMexOverpartition 1 0 = 1 := by
  have h : ∀ O : Nat.Overpartition 0, leastGapOverpartition 1 O = 1 := by
    simp only [leastGapOverpartition, dite_eq_right (by decide : 1 ≠ 0), Nat.find_eq_iff]
    decide
  simpa [sigmaMexOverpartition, h, overpartitionCount] using overpartitionCount_zero

example : Nat.ModEq 2 (sigmaMexOverpartition 1 3) 1 :=
  (sigmaMexOverpartition_parity 3 (by decide)).1 ⟨2, rfl⟩

example : Nat.ModEq 2 (sigmaMexOverpartition 1 2) 0 := by
  apply (sigmaMexOverpartition_parity 2 (by decide)).2
  rintro ⟨j, hj⟩
  by_cases h : 2 ≤ j
  · have : 2 * 3 ≤ j * (j + 1) := Nat.mul_le_mul h (by omega)
    omega
  · have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl <;> revert hj <;> decide

end MetaMathlibExt.sigmaMexOverpartition_parity

namespace MetaMathlibExt.sigmaMexOverpartition_eq_D3

-- At the first two sizes the identity gives the counts `3` and `6` of `D3_one` and `D3_two`.
example : sigmaMexOverpartition 1 1 = 3 :=
  (sigmaMexOverpartition_eq_D3 1 (by decide)).trans D3_one

example : sigmaMexOverpartition 1 2 = 6 :=
  (sigmaMexOverpartition_eq_D3 2 (by decide)).trans D3_two

-- At four the identity gives the enumerated value `24`, which the overpartition counts at the
-- triangular shifts `0`, `1` and `3` also sum to.
example : sigmaMexOverpartition 1 4 = 24 :=
  (sigmaMexOverpartition_eq_D3 4 (by decide)).trans (by decide +kernel)

example : D3 4 = overpartitionCount 4 + overpartitionCount 3 + overpartitionCount 1 := by
  rw [← sigmaMexOverpartition_eq_D3 4 (by decide)]
  simpa [Finset.sum_filter, Finset.sum_range_succ] using
    (sigmaMexOverpartition_eq_sum_shifted_count 4 1 le_rfl).symm

-- With the parity theorem, `D3` is odd at the triangular number `10`.
example : Nat.ModEq 2 (D3 10) 1 := by
  rw [← sigmaMexOverpartition_eq_D3 10 (by decide)]
  exact (sigmaMexOverpartition_parity 10 (by decide)).1 ⟨4, rfl⟩

end MetaMathlibExt.sigmaMexOverpartition_eq_D3
