/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.NColorCompositions
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Tests for `MathlibExt.Combinatorics.Enumerative.NColorCompositions` -/

namespace MathlibExtTest.NColorCompositions

open MathlibExt.Combinatorics.Enumerative.NColorCompositionsWanted

-- The first values of `tribNat`: the initial values `1, 0, 1`, then each value is the sum of the
-- three before it.
example : (List.range 12).map tribNat = [1, 0, 1, 2, 3, 6, 11, 20, 37, 68, 125, 230] := by
  decide

-- `trib` agrees with `tribNat` at nonnegative integers and vanishes at negative ones.
example : trib 0 = 1 ∧ trib 1 = 0 ∧ trib 2 = 1 ∧ trib 7 = 20 := by decide

example : trib (-1) = 0 ∧ trib (-2) = 0 ∧ trib (-3) = 0 ∧ trib (-100) = 0 := by decide

example (n : ℤ) (hn : n < 0) : trib n = 0 := by simp [trib, not_le.mpr hn]

-- The zero extension breaks the recurrence at `n = 1`: `t(1) = 0`, but
-- `t(0) + t(-1) + t(-2) = 1`. In the theorem every index is at least `3`.
example : trib 1 ≠ trib 0 + trib (-1) + trib (-2) := by decide

-- The case `k = 1` (`n = 5`): `t(5) + t(3) = 6 + 2 = 2 + 2 t(4)`.
example : trib 5 + trib 3 = 2 + 2 * trib 4 := by
  simpa [Finset.sum_range_one] using trib_add_two_sub_three_mul_add_two 1 le_rfl

-- The case `k = 2` (`n = 8`): `t(8) + t(6) = 2 + 2 (t(7) + t(4)) = 48`.
example : trib 8 + trib 6 = 2 + 2 * (trib 7 + trib 4) ∧ trib 8 + trib 6 = 48 := by
  refine ⟨?_, by decide⟩
  simpa [Finset.sum_range_succ] using trib_add_two_sub_three_mul_add_two 2 (by decide)

-- An independent check by evaluation of the cases `1 ≤ k ≤ 6`.
example : ∀ k : ℕ, k < 7 → 1 ≤ k →
    trib (3 * (k : ℤ) + 2) + trib (3 * (k : ℤ) + 2 - 2) =
      2 + 2 * ∑ i ∈ Finset.range k, trib (3 * (k : ℤ) + 2 - 3 * (i : ℤ) - 1) := by
  decide

-- The identity also holds at `k = 0`, which the theorem excludes: `t(2) + t(0) = 2`.
example : trib (3 * ((0 : ℕ) : ℤ) + 2) + trib (3 * ((0 : ℕ) : ℤ) + 2 - 2) =
    2 + 2 * ∑ i ∈ Finset.range 0, trib (3 * ((0 : ℕ) : ℤ) + 2 - 3 * (i : ℤ) - 1) := by
  decide

-- At `k = 10` the theorem turns the left side `t(32) + t(30)` into a sum of ten values.
example : trib 32 + trib 30 =
    2 + 2 * ∑ i ∈ Finset.range 10, trib (3 * ((10 : ℕ) : ℤ) + 2 - 3 * (i : ℤ) - 1) := by
  simpa using trib_add_two_sub_three_mul_add_two 10 (by decide)

-- At `k = 0` the sole summand uses the two negative indices.
example : trib 0 = 1 + (trib (-1) + trib (-2)) := by
  simpa [Finset.sum_range_one] using trib_three_mul (k := 0)

-- At `k = 2` the sum has two nonnegative index pairs and one negative pair.
example :
    trib 6 = 1 + ((trib 5 + trib 4) + (trib 2 + trib 1) + (trib (-1) + trib (-2))) ∧
      trib 6 = 11 := by
  refine ⟨?_, by decide⟩
  simpa [Finset.sum_range_succ] using trib_three_mul (k := 2)

-- The first admissible values `n = 3, 4`, each with one summand.
example :
    (trib 3 + trib 1 = 2 * trib 2 ∧ trib 4 + trib 2 = 2 * trib 3) ∧
      (trib 3 + trib 1 = 2 ∧ trib 4 + trib 2 = 4) := by
  refine ⟨?_, by decide⟩
  simpa [Finset.sum_range_one] using trib_add_two_sub_three_mul (k := 1) (hk := le_rfl)

-- At `n = 6, 7` each progression adds a second summand, three indices apart.
example :
    (trib 6 + trib 4 = 2 * (trib 5 + trib 2) ∧
      trib 7 + trib 5 = 2 * (trib 6 + trib 3)) ∧
      (trib 6 + trib 4 = 14 ∧ trib 7 + trib 5 = 26) := by
  refine ⟨?_, by decide⟩
  simpa [Finset.sum_range_succ] using trib_add_two_sub_three_mul (k := 2) (hk := by decide)

-- The residue-two identity includes k = 0, with one summand.
example : trib (3 * ((0 : ℕ) : ℤ) + 2) = 1 := by
  rw [trib_three_mul_add_two (k := 0)]
  decide

-- Three pairs contribute to t(8): (t(7)+t(6)), (t(4)+t(3)), (t(1)+t(0)).
example : trib (3 * ((2 : ℕ) : ℤ) + 2) = 37 := by
  rw [trib_three_mul_add_two (k := 2)]
  decide

end MathlibExtTest.NColorCompositions
