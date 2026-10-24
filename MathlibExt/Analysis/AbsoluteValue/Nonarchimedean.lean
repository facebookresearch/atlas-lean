/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Nonarchimedean absolute values and natural-number casts

This module ports ATLAS `NumberTheoryI` Lemma 1.4 (Section 1.2,
`v1/Atlas/NumberTheoryI/targets.yaml`): an absolute value on a field is
nonarchimedean if and only if every natural-number cast has absolute value at
most `1`. The forward direction is Mathlib's
`IsNonarchimedean.apply_natCast_le_one`; the converse, proved here via the
binomial expansion, is not in Mathlib.

The companion statements of Corollary 1.5 are already in MathlibExt, in
`MathlibExt/Analysis/AbsoluteValue/FiniteField.lean`
(`AbsoluteValue.isNonarchimedean_of_charP` and
`AbsoluteValue.eq_one_of_ne_zero_of_finite`), so they are not repeated here.
-/

@[expose] public section

namespace AbsoluteValue

variable {K : Type*} [Field K]

/-- Binomial-expansion bound: if every natural-number cast has absolute value
at most `1`, then `v (x + y) ^ n` is at most `(n + 1)` times the `n`-th power
of `max (v x) (v y)`. -/
public theorem add_pow_le_mul_max_pow_of_natCast_le_one (v : AbsoluteValue K ℝ)
    (hv : ∀ n : ℕ, v (n : K) ≤ 1) (x y : K) (n : ℕ) :
    v (x + y) ^ n ≤ (↑n + 1) * (max (v x) (v y)) ^ n := by
  rw [← v.map_pow, add_pow x y n]
  calc v (∑ m ∈ Finset.range (n + 1), x ^ m * y ^ (n - m) * ↑(n.choose m))
      ≤ ∑ m ∈ Finset.range (n + 1), v (x ^ m * y ^ (n - m) * ↑(n.choose m)) :=
        v.sum_le _ _
    _ ≤ ∑ _m ∈ Finset.range (n + 1), (max (v x) (v y)) ^ n := by
        apply Finset.sum_le_sum
        intro m hm
        rw [Finset.mem_range] at hm
        have hmn : m + (n - m) = n := Nat.add_sub_cancel' (by omega)
        calc v (x ^ m * y ^ (n - m) * ↑(n.choose m))
            = v x ^ m * v y ^ (n - m) * v (↑(n.choose m)) := by
              rw [map_mul, map_mul, map_pow, map_pow]
          _ ≤ v x ^ m * v y ^ (n - m) * 1 :=
              mul_le_mul_of_nonneg_left (hv _)
                (mul_nonneg (pow_nonneg (v.nonneg _) _)
                  (pow_nonneg (v.nonneg _) _))
          _ = v x ^ m * v y ^ (n - m) := by ring
          _ ≤ (max (v x) (v y)) ^ m * (max (v x) (v y)) ^ (n - m) :=
              mul_le_mul
                (pow_le_pow_left₀ (v.nonneg _) (le_max_left _ _) _)
                (pow_le_pow_left₀ (v.nonneg _) (le_max_right _ _) _)
                (pow_nonneg (v.nonneg _) _)
                (pow_nonneg (le_max_of_le_left (v.nonneg _)) _)
          _ = (max (v x) (v y)) ^ n := by rw [← pow_add, hmn]
    _ = (↑n + 1) * (max (v x) (v y)) ^ n := by
        simp [Finset.sum_const, Finset.card_range]

/-- If every natural-number cast has absolute value at most `1`, then the
absolute value is nonarchimedean. This is the backward direction of
Lemma 1.4. -/
public theorem isNonarchimedean_of_natCast_le_one (v : AbsoluteValue K ℝ)
    (hv : ∀ n : ℕ, v (n : K) ≤ 1) : IsNonarchimedean v := by
  intro x y
  by_contra hlt
  push Not at hlt
  have hM_pos : 0 < max (v x) (v y) := by
    by_contra h
    push Not at h
    have hx : v x = 0 := le_antisymm ((le_max_left _ _).trans h) (v.nonneg x)
    have hy : v y = 0 := le_antisymm ((le_max_right _ _).trans h) (v.nonneg y)
    simp [v.eq_zero.mp hx, v.eq_zero.mp hy] at hlt
  set M := max (v x) (v y) with hM
  set r := v (x + y) / M with hr
  have hr_gt_one : 1 < r := (one_lt_div hM_pos).mpr hlt
  have hr_bound : ∀ n : ℕ, r ^ n ≤ ↑n + 1 := by
    intro n
    rw [div_pow, div_le_iff₀ (pow_pos hM_pos n)]
    exact v.add_pow_le_mul_max_pow_of_natCast_le_one hv x y n
  obtain ⟨m, hm⟩ := Real.exists_natCast_add_one_lt_pow_of_one_lt hr_gt_one
  linarith [hr_bound m]

/-- An absolute value on a field is nonarchimedean if and only if every
natural-number cast has absolute value at most `1`. This is Lemma 1.4. -/
public theorem isNonarchimedean_iff_natCast_le_one (v : AbsoluteValue K ℝ) :
    IsNonarchimedean v ↔ ∀ n : ℕ, v (n : K) ≤ 1 :=
  ⟨fun hna n =>
    hna.apply_natCast_le_one (by simp [v.map_zero, v.map_one]) v.map_one,
    isNonarchimedean_of_natCast_le_one v⟩

/-- Lemma 1.4 in the book's form, with the bound required only for positive
`n` (the `n = 0` case is `v 0 = 0 ≤ 1` anyway). -/
public theorem isNonarchimedean_iff_natCast_le_one_of_pos
    (v : AbsoluteValue K ℝ) :
    IsNonarchimedean v ↔ ∀ n : ℕ, 0 < n → v (n : K) ≤ 1 := by
  rw [v.isNonarchimedean_iff_natCast_le_one]
  constructor
  · intro h n _
    exact h n
  · intro h n
    rcases n.eq_zero_or_pos with rfl | hn
    · simp [v.map_zero]
    · exact h n hn

end AbsoluteValue

end
