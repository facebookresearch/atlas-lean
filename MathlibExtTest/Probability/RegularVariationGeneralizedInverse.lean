/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.RegularVariationGeneralizedInverse

@[expose] public section

open Filter
open scoped Topology
open MathlibExt.Probability.RegularVariation

namespace MathlibExtTest.Probability.RegularVariationGeneralizedInverse

/-- The constant function `1` is slowly varying. -/
example : IsSlowlyVarying (fun _ => (1 : ℝ)) := by
  refine ⟨Filter.Eventually.of_forall (fun _ => one_pos), fun _ _ => ?_⟩
  simp

/-- The power function `x ↦ x ^ (-1 : ℝ)` is regularly varying of index `-1`. -/
example : IsRegularlyVarying (fun x : ℝ => x ^ (-1 : ℝ)) (-1) := by
  refine ⟨fun _ => (1 : ℝ), ⟨Filter.Eventually.of_forall (fun _ => one_pos), fun _ _ => ?_⟩, ?_⟩
  · simp
  · exact Filter.Eventually.of_forall fun _ => by simp

/-- The power function `x ↦ x ^ (-2 : ℝ)` is regularly varying of index `-2`. -/
example : IsRegularlyVarying (fun x : ℝ => x ^ (-2 : ℝ)) (-2) := by
  refine ⟨fun _ => (1 : ℝ), ⟨Filter.Eventually.of_forall (fun _ => one_pos), fun _ _ => ?_⟩, ?_⟩
  · simp
  · exact Filter.Eventually.of_forall fun _ => by simp

/-- The generalized-inverse theorem, restated with its exact public signature,
for the power function `x ↦ x ^ (-1 : ℝ)`. -/
example : ∃ a : ℕ → ℝ, (∀ n, 0 < a n) ∧
    Tendsto (fun n => ↑n * (a n) ^ (-1 : ℝ)) atTop (𝓝 1) := by
  apply regularlyVarying_generalized_inverse (fun x : ℝ => x ^ (-1 : ℝ)) 1 (by norm_num)
  · refine ⟨fun _ => (1 : ℝ), ⟨Filter.Eventually.of_forall (fun _ => one_pos), fun _ _ => ?_⟩, ?_⟩
    · simp
    · exact Filter.Eventually.of_forall fun _ => by simp
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx y hy
    exact Real.rpow_le_rpow_of_nonpos hx hy (by norm_num)

/-- The generalized-inverse theorem, restated with its exact public signature,
for the power function `x ↦ x ^ (-2 : ℝ)`. -/
example : ∃ a : ℕ → ℝ, (∀ n, 0 < a n) ∧
    Tendsto (fun n => ↑n * (a n) ^ (-2 : ℝ)) atTop (𝓝 1) := by
  apply regularlyVarying_generalized_inverse (fun x : ℝ => x ^ (-2 : ℝ)) 2 (by norm_num)
  · refine ⟨fun _ => (1 : ℝ), ⟨Filter.Eventually.of_forall (fun _ => one_pos), fun _ _ => ?_⟩, ?_⟩
    · simp
    · exact Filter.Eventually.of_forall fun _ => by simp
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx y hy
    exact Real.rpow_le_rpow_of_nonpos hx hy (by norm_num)

#print axioms regularlyVarying_generalized_inverse

/-- A tail that is negative before the asymptotic range. -/
private noncomputable def modifiedTail (x : ℝ) : ℝ :=
  if x ≤ 1 then -1 else x ^ (-1 : ℝ)

private theorem modifiedTail_regularlyVarying :
    IsRegularlyVarying modifiedTail (-1) := by
  apply (isRegularlyVarying_rpow (-1)).of_eventuallyEq
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  simp [modifiedTail, not_le_of_gt hx]

private theorem modifiedTail_antitone :
    ∀ᶠ x in atTop, ∀ y, x ≤ y → modifiedTail y ≤ modifiedTail x := by
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx y hxy
  have hy : 1 < y := lt_of_lt_of_le hx hxy
  simp only [modifiedTail, ite_eq_right (not_le_of_gt hx), ite_eq_right (not_le_of_gt hy)]
  exact Real.rpow_le_rpow_of_nonpos (lt_trans zero_lt_one hx) hxy (by norm_num)

/-- The importing canonical API accepts a tail modified outside its asymptotic range. -/
private theorem canonical_modified_tail_inverse :
    ∃ a : ℕ → ℝ, (∀ n, 0 < a n) ∧
      Tendsto (fun n => ↑n * modifiedTail (a n)) atTop (𝓝 1) := by
  exact regularlyVarying_generalized_inverse modifiedTail 1 (by norm_num)
    modifiedTail_regularlyVarying modifiedTail_antitone

/-- Eventual positivity permits a negative value at zero. -/
private theorem modifiedTail_zero : modifiedTail 0 = -1 := by
  simp [modifiedTail]

end MathlibExtTest.Probability.RegularVariationGeneralizedInverse
