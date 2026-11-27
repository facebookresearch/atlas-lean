/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Economics.Finance.DiscountedPresentValue

/-! # Present-value specialization of the truncation bound -/

@[expose] public section

namespace MathlibExtTest.Analysis.SpecificLimits.DiscountedSum

open _root_.MathlibExt.DiscountedSum

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
