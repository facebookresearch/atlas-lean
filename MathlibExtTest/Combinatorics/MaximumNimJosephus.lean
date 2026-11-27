/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.MaximumNimJosephus
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.Combinatorics.MaximumNimJosephus` -/

namespace MathlibExtTest.MaximumNimJosephus

open MetaMathlibExt

-- Test section: the floor identity. For `k = 3` and `x = 10` the hypotheses are decidable, and
-- both sides equal `6`.
example : 10 - 10 / 3 - 1 = (3 - 1) * 10 / 3 :=
  maximumNim_sub_div_sub_one_eq 3 10 (by decide) (by decide)

example : (3 - 1) * 10 / 3 = 6 := by decide

-- Below `k` the quotient `x / k` is `0`, so for `0 < x < k` the identity reads
-- `x - 1 = (k - 1) * x / k`.
example (k x : ℕ) (hk : 2 ≤ k) (hx : 0 < x) (hxk : x < k) : x - 1 = (k - 1) * x / k := by
  have h := maximumNim_sub_div_sub_one_eq k x hk (Nat.not_dvd_of_pos_of_lt hx hxk)
  rwa [Nat.div_eq_of_lt hxk, Nat.sub_zero] at h

-- For the smallest step `k = 2`, an odd `x` satisfies `x - x / 2 - 1 = x / 2`.
example (x : ℕ) (hx : x % 2 = 1) : x - x / 2 - 1 = x / 2 := by
  have h := maximumNim_sub_div_sub_one_eq 2 x (Nat.le_refl 2) (by omega)
  rwa [show (2 - 1) * x = x from Nat.one_mul x] at h

-- Test section: the hypotheses are needed. At the positive multiple `x = 6` of `k = 3` the left
-- side is `3` and the right side is `4`.
example : 6 - 6 / 3 - 1 ≠ (3 - 1) * 6 / 3 := by decide

-- For `k = 0`, the number `2` is not a multiple of `0`, but `2 / 0 = 0` and `(0 - 1) * 2 / 0 = 0`,
-- so the left side is `1` and the right side is `0`.
example : ¬0 ∣ 2 ∧ 2 - 2 / 0 - 1 ≠ (0 - 1) * 2 / 0 := by decide

-- Test section: the minimum excludant. `maximumNimMex` is the least natural number outside the
-- set: the empty set has mex `0`, and `{0, 1, 3}` has mex `2`.
example : maximumNimMex ∅ = 0 := (maximumNimMex_eq_iff _ _).mpr ⟨by simp, by simp⟩

example : maximumNimMex {0, 1, 3} = 2 := (maximumNimMex_eq_iff _ _).mpr ⟨by decide, by decide⟩

-- Test section: Grundy numbers. For the rule `f(y) = y / 3`, a pile of `2` stones has no move,
-- so its Grundy number is the mex of the empty set.
example : maximumNimGrundy (· / 3) 2 = 0 := by
  rw [maximumNimGrundy_eq, maximumNimMex_eq_iff]
  simp

-- For the smallest divisor and `j = 1`, the largest pile below the divisor is terminal.
example : maximumNimGrundy (· / 2) 1 = 0 :=
  maximumNimGrundy_sub_eq_zero 2 1 (by decide) (by decide) (by decide)

-- An interior value of `j` gives a positive pile strictly below `k`.
example : maximumNimGrundy (· / 7) 4 = 0 :=
  maximumNimGrundy_sub_eq_zero 7 3 (by decide) (by decide) (by decide)

-- At `j = k`, the theorem also covers the empty pile for any permitted divisor.
example (k : ℕ) (hk : 2 ≤ k) : maximumNimGrundy (· / k) 0 = 0 := by
  simpa only [Nat.sub_self] using maximumNimGrundy_sub_eq_zero k k hk (by omega) le_rfl

-- Test section: Grundy numbers at multiples of the divisor. For `k = 3`, the piles `3`, `6` and
-- `9` have Grundy numbers `1`, `2` and `3`.
example : maximumNimGrundy (· / 3) 3 = 1 :=
  maximumNimGrundy_div_eq_of_dvd 3 3 (by decide) (by decide) (by decide)

example : maximumNimGrundy (· / 3) 6 = 2 :=
  maximumNimGrundy_div_eq_of_dvd 3 6 (by decide) (by decide) (by decide)

example : maximumNimGrundy (· / 3) 9 = 3 :=
  maximumNimGrundy_div_eq_of_dvd 3 9 (by decide) (by decide) (by decide)

-- For `k = 2` the theorem gives the value `G(4) = 2` that `maximumNimGrundy_div_two_four`
-- computes from the recursion.
example : maximumNimGrundy (· / 2) 4 = 2 :=
  maximumNimGrundy_div_eq_of_dvd 2 4 (by decide) (by decide) (by decide)

example : maximumNimGrundy (· / 2) 4 = 4 / 2 := maximumNimGrundy_div_two_four

-- In multiplicative form: `G(k * m) = m` for every `k ≥ 2` and `m ≥ 1`.
example (k m : ℕ) (hk : 2 ≤ k) (hm : 1 ≤ m) : maximumNimGrundy (· / k) (k * m) = m := by
  rw [maximumNimGrundy_div_eq_of_dvd k (k * m) hk (Nat.mul_pos (by omega) hm)
      (Nat.dvd_mul_right k m), Nat.mul_div_cancel_left m (by omega)]

-- The divisibility hypothesis is needed: `3` is not a multiple of `2`, and for the halving rule
-- `G(3) = 0`, while `3 / 2 = 1`.
example : maximumNimGrundy (· / 2) 3 ≠ 3 / 2 := by
  rw [maximumNimGrundy_div_two_three]
  decide

-- The hypothesis `1 ≤ x` only excludes the empty pile, where the conclusion holds as well:
-- `G(0) = 0 = 0 / k` for every `k`.
example (k : ℕ) : maximumNimGrundy (· / k) 0 = 0 / k := by
  rw [maximumNimGrundy_eq, maximumNimMex_eq_iff]
  simp

-- At the last allowed step and largest index, the pile size can be just one above a multiple.
example : ¬(7 : ℕ) ∣ 15 :=
  maximumNim_not_dvd_mul_sub_of_lt 7 3 2 1 1 3 (by decide) rfl (by decide) (by decide)
    (by decide) (by decide)

-- At the excluded step `s = t`, the index `i = h` gives a multiple of the same divisor.
example : (7 : ℕ) ∣ 3 * (7 - 2) - 1 := by decide

-- With `8 = 3 * 2 + 2`, the offsets from `16` are positive for `i = 1` and negative for `i = 3`.
example : ¬(8 : ℕ) ∣ 3 * (8 - 2) - 1 :=
  maximumNim_not_dvd_mul_sub_of_ne 8 3 2 2 1 (by decide) (by decide) rfl (by decide)
    (by decide) (by decide) (by decide)

example : ¬(8 : ℕ) ∣ 3 * (8 - 2) - 3 :=
  maximumNim_not_dvd_mul_sub_of_ne 8 3 2 2 3 (by decide) (by decide) rfl (by decide)
    (by decide) (by decide) (by decide)

-- At step three, the quotient stays at zero from input zero to one and rises at input two.
example : maximumNimH 3 0 < maximumNimH 3 1 ∧ maximumNimH 3 1 < maximumNimH 3 2 :=
  ⟨maximumNimH_strictMono 3 0 1 (by decide) (by decide),
   maximumNimH_strictMono 3 1 2 (by decide) (by decide)⟩

-- At `x = 0` the bound is attained, including at the smallest permitted step.
example : 0 < 1 ∧ 1 ≤ maximumNimH 2 0 :=
  maximumNimH_succ_le (k := 2) (x := 0) (hk := le_rfl)

example : maximumNimH 2 0 = 1 := by decide

-- At `k = 3` and `x = 2`, the quotient contributes an additional unit.
example : 2 < 3 ∧ 3 ≤ maximumNimH 3 2 :=
  maximumNimH_succ_le 3 2 (by decide)

example : 3 < maximumNimH 3 2 := by decide

-- Zero iterations leave both real maps at the starting position.
example (x : ℕ) :
    Nat.iterate (fun y : ℝ => y + y / 2) 0 (x : ℝ) = x ∧
      Nat.iterate (fun y : ℝ => y + y / 2 + 1) 0 (x : ℝ) = x := by
  have h := maximumNimH_iterate_bounds (k := 3) (hk := by decide)
  exact ⟨(h.1 0 x).trans (by simp), (h.2.1 0 x).trans (by simp [add_sub_assoc])⟩

-- At the smallest allowed `k`, the two maps are doubling and doubling plus one.
example :
    Nat.iterate (fun y : ℝ => y + y / (2 - 1)) 3 2 = 16 ∧
      Nat.iterate (fun y : ℝ => y + y / (2 - 1) + 1) 3 2 = 23 := by
  have h := maximumNimH_iterate_bounds (k := 2) (hk := by decide)
  exact ⟨(h.1 3 2).trans (by norm_num), (h.2.1 3 2).trans (by norm_num)⟩

-- `8 = 3 * 2 + 2`: the remainder is nonzero, so neither real map equals `h₄(8)`.
example : 8 % (4 - 1) = 2 ∧ maximumNimH 4 8 = 11 := by decide

example : (32 : ℝ) / 3 ≤ (maximumNimH 4 8 : ℝ) ∧
    (maximumNimH 4 8 : ℝ) ≤ (35 : ℝ) / 3 := by
  have h := (maximumNimH_iterate_bounds (k := 4) (hk := by decide)).2.2 8
  change (8 : ℝ) + 8 / (4 - 1) ≤ (maximumNimH 4 8 : ℝ) ∧
    (maximumNimH 4 8 : ℝ) ≤ 8 + 8 / (4 - 1) + 1 at h
  convert h using 2 <;> norm_num

end MathlibExtTest.MaximumNimJosephus
