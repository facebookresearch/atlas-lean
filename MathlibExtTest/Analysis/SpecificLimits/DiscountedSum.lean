/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecificLimits.DiscountedSum

/-!
# Tests for the discounted-sum truncation bound

Both theorems applied directly: constant reward `1` at `β = 1/2`, `T = 2`, where the error and
the bound are both `1/2`, so the bound is attained; the `T = 0` case, where the bound `2` equals
the whole discounted value; `β = 0`, where the one-period truncation is exact; and the
present-value form of the bound at `β = 1/2`, `T = 2`, where the present value is `3/2`.
-/

@[expose] public section

namespace MathlibExtTest.Analysis.SpecificLimits.DiscountedSum

open _root_.MathlibExt.DiscountedSum

/-- Test (1a): with constant reward `1`, discount `1/2` and truncation `T = 2`, the
truncation error is exactly `1/2`. -/
theorem test1_value : discountedValue (1/2) (fun _ => 1)
    - truncatedValue (1/2) (fun _ => 1) 2 = 1/2 := by
  have hgeo := tsum_geometric_of_lt_one (r := (1/2 : ℝ)) (by norm_num) (by norm_num)
  have hsum : discountedValue (1/2) (fun _ => 1) = 2 := by
    unfold discountedValue
    simp only [mul_one]
    rw [hgeo]
    norm_num
  have htrunc : truncatedValue (1/2) (fun _ => 1) 2 = 3/2 := by
    have e : (∑ t ∈ Finset.range 2, (1/2 : ℝ) ^ t) = (1/2) ^ 0 + (1/2) ^ 1 := by
      have h1 := Finset.sum_range_succ (fun t => (1/2 : ℝ) ^ t) 1
      have h0 := Finset.sum_range_succ (fun t => (1/2 : ℝ) ^ t) 0
      have hz := Finset.sum_range_zero (fun t => (1/2 : ℝ) ^ t)
      norm_num at h1 h0 hz ⊢
    unfold truncatedValue
    simp only [mul_one]
    rw [e]
    norm_num
  rw [hsum, htrunc]
  norm_num

/-- Test (1b): the theorem's bound `M * β ^ T / (1 - β)` with `M = 1`, `β = 1/2`,
`T = 2` also equals `1/2`, so the bound is attained. -/
theorem test1_bound : (1 : ℝ) * (1/2) ^ 2 / (1 - 1/2) = 1/2 := by norm_num

/-- Test (2): with discount `0`, the `1`-period truncation is exact. -/
theorem test2_zero_discount {M : ℝ} {r : ℕ → ℝ} (_hr : ∀ t, |r t| ≤ M) :
    |discountedValue 0 r - truncatedValue 0 r 1| = 0 := by
  have h1 : discountedValue 0 r = r 0 := by
    have h : (∑' t, (0 : ℝ) ^ t * r t) = (0 : ℝ) ^ 0 * r 0 := by
      apply tsum_eq_single 0
      intro t ht
      rw [zero_pow ht, zero_mul]
    unfold discountedValue
    rw [h, pow_zero, one_mul]
  have h2 : truncatedValue 0 r 1 = r 0 := by
    unfold truncatedValue
    rw [Finset.sum_range_one, pow_zero, one_mul]
  rw [h1, h2, sub_self, abs_zero]

/-- Test (3a): `summable_discounted` applies to the constant reward `1` with
`β = 1/2` and `M = 1`. -/
theorem test3_summable : Summable fun t => (1/2 : ℝ) ^ t * (fun _ => (1 : ℝ)) t :=
  summable_discounted (β := 1/2) (M := 1) (r := fun _ => 1)
    (by norm_num) (by norm_num) (fun t => by norm_num)

/-- Test (3b): the bound from `abs_discountedValue_sub_truncatedValue_le` with
`β = 1/2`, `M = 1`, `T = 2` is attained: both sides equal `1/2`. -/
theorem test3_bound_attained :
    |discountedValue (1/2) (fun _ => 1) - truncatedValue (1/2) (fun _ => 1) 2|
      = (1 : ℝ) * (1/2) ^ 2 / (1 - 1/2) := by
  have hle := abs_discountedValue_sub_truncatedValue_le (β := (1/2 : ℝ)) (M := (1 : ℝ))
    (r := fun _ => 1) (by norm_num) (by norm_num) (fun t => by norm_num) 2
  apply le_antisymm hle
  rw [test1_value, test1_bound]
  norm_num

/-- Test (3c-i): the `T = 0` probe, derived from
`abs_discountedValue_sub_truncatedValue_le` with `T = 0` (the `0`-period
truncation vanishes). -/
theorem test3_T0_le : |discountedValue (1/2) (fun _ => 1)|
    ≤ (1 : ℝ) * (1/2) ^ 0 / (1 - 1/2) := by
  have h := abs_discountedValue_sub_truncatedValue_le (β := (1/2 : ℝ)) (M := (1 : ℝ))
    (r := fun _ => 1) (by norm_num) (by norm_num) (fun t => by norm_num) 0
  have htrunc : truncatedValue (1/2) (fun _ => 1) 0 = 0 := by
    unfold truncatedValue
    simp
  rw [htrunc, sub_zero] at h
  exact h

/-- Test (3c-ii): in the `T = 0` probe, the left-hand side equals `2`. -/
theorem test3_T0_lhs : |discountedValue (1/2) (fun _ => 1)| = 2 := by
  have hgeo := tsum_geometric_of_lt_one (r := (1/2 : ℝ)) (by norm_num) (by norm_num)
  have hsum : discountedValue (1/2) (fun _ => 1) = 2 := by
    unfold discountedValue
    simp only [mul_one]
    rw [hgeo]
    norm_num
  rw [hsum]
  norm_num

/-- Test (3c-iii): in the `T = 0` probe, the right-hand side equals `2`. -/
theorem test3_T0_rhs : (1 : ℝ) * (1/2) ^ 0 / (1 - 1/2) = 2 := by norm_num

/-- Test (4): the present-value bound `abs_discountedValue_sub_presentValue_le` applies with
`β = 1/2`, `M = 1`, `T = 2`, and the present value of the constant reward `1` is `3/2`. -/
theorem test4_presentValue_bound :
    |discountedValue (1/2) (fun _ => 1) -
        MathlibExt.Economics.Finance.presentValue (fun t => (1/2 : ℝ) ^ t)
          (Finset.range 2) (fun _ => 1)| ≤ (1 : ℝ) * (1/2) ^ 2 / (1 - 1/2) ∧
      MathlibExt.Economics.Finance.presentValue (fun t => (1/2 : ℝ) ^ t)
        (Finset.range 2) (fun _ => 1) = 3/2 := by
  refine ⟨?_, ?_⟩
  · exact abs_discountedValue_sub_presentValue_le (β := (1/2 : ℝ)) (M := (1 : ℝ))
      (r := fun _ => 1) (by norm_num) (by norm_num) (fun t => by norm_num) 2
  · rw [← truncatedValue_eq_presentValue]
    unfold truncatedValue
    simp only [mul_one]
    have e : (∑ t ∈ Finset.range 2, (1/2 : ℝ) ^ t) = (1/2) ^ 0 + (1/2) ^ 1 := by
      have h1 := Finset.sum_range_succ (fun t => (1/2 : ℝ) ^ t) 1
      have h0 := Finset.sum_range_succ (fun t => (1/2 : ℝ) ^ t) 0
      have hz := Finset.sum_range_zero (fun t => (1/2 : ℝ) ^ t)
      norm_num at h1 h0 hz ⊢
    rw [e]
    norm_num

end MathlibExtTest.Analysis.SpecificLimits.DiscountedSum
