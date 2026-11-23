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

-- At the lower endpoint there is one composition of 3 and none of 1.
example : ccoAllowed 3 3 = 1 := by
  have : IsEmpty (ColorCompAllowed 3 1) := by
    constructor
    rintro ⟨_ | ⟨⟨k, c⟩, l⟩, hvalid, hsum⟩
    · simp at hsum
    · have hc := hvalid (k, c) (by simp)
      simp only [List.map_cons, List.sum_cons] at hsum
      omega
  simpa [ccoAllowed, Nat.fib] using ccoAllowed_three_add 3 le_rfl

-- At total 7 the same two colored parts occur in two different orders.
example : (⟨[(3, 3), (4, 4)], by decide⟩ : ColorCompAllowed 3 7) ≠
    ⟨[(4, 4), (3, 3)], by decide⟩ := by decide

-- The color must also fit the size of the part.
example (x : ColorCompAllowed 3 3) : x.val ≠ [(3, 4)] := by
  intro h
  have := x.property.1 (3, 4) (by simp [h])
  omega

-- At total 8 both summands are nonzero.
example : ccoAllowed 3 8 + ccoAllowed 3 6 = 13 := by
  simpa [Nat.fib] using ccoAllowed_three_add 8 (by decide)

end MathlibExtTest.NColorCompositions
