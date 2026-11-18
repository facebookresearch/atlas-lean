/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.GaussianDistortionAttainment
public import MathlibExt.InformationTheory.GaussianDistortionConverse

@[expose] public section

open MeasureTheory ProbabilityTheory
open _root_.InformationTheory
open MathlibExt.InformationTheory.GaussianDistortionAttainment
  MathlibExt.InformationTheory.GaussianDistortionConverse
  MathlibExt.InformationTheory.GaussianDistortionFeasibility
open scoped ENNReal NNReal

namespace MathlibExtTest.InformationTheory.GaussianDistortionAttainment

private lemma log_four_eq : Real.log (4 : ℝ) = 2 * Real.log 2 := by
  have h4 : (4 : ℝ) = 2 ^ 2 := by norm_num
  rw [h4, Real.log_pow]
  norm_num

private lemma log_two_ne_zero : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'

/-- The product space `N(0, 1) ⊗ N(0, 1)` with `X̂ = fst` and `Z = snd` realizes the hypotheses
of the headline at `σ2 = 2`, `D = 1`. -/
private lemma product_hypotheses :
    HasLaw Prod.fst (gaussianReal 0 (2 - 1))
        ((gaussianReal 0 (2 - 1)).prod (gaussianReal 0 1)) ∧
      HasLaw Prod.snd (gaussianReal 0 1) ((gaussianReal 0 (2 - 1)).prod (gaussianReal 0 1)) ∧
      IndepFun Prod.fst Prod.snd ((gaussianReal 0 (2 - 1)).prod (gaussianReal 0 1)) := by
  refine ⟨⟨measurable_fst.aemeasurable, ?_⟩, ⟨measurable_snd.aemeasurable, ?_⟩, ?_⟩
  · simp [Measure.map_fst_prod]
  · simp [Measure.map_snd_prod]
  · refine (indepFun_iff_map_prod_eq_prod_map_map measurable_fst.aemeasurable
      measurable_snd.aemeasurable).2 ?_
    simp [Measure.map_fst_prod, Measure.map_snd_prod]

/-- The headline on concrete random variables: with `σ2 = 2`, `D = 1`, `X̂ = fst`, `Z = snd`
and `X = X̂ + Z`, the backward channel attains the bound, and the mutual information is exactly
one half bit. -/
example :
    measureMutualInformation
        (pairLaw ((gaussianReal 0 (2 - 1)).prod (gaussianReal 0 1))
          (fun p : ℝ × ℝ => p.1 + p.2) Prod.fst) = ENNReal.ofReal (1 / 2) ∧
      rateDistortion 2 ((1 : ℝ≥0) : ℝ) ≤ ENNReal.ofReal (1 / 2) := by
  obtain ⟨hX, hZ, hI⟩ := product_hypotheses
  obtain ⟨-, -, -, hMI, hR⟩ := backwardChannel_attains 2 1 (by norm_num) (by norm_num)
    ((gaussianReal 0 (2 - 1)).prod (gaussianReal 0 1)) (fun p : ℝ × ℝ => p.1 + p.2) Prod.fst
    Prod.snd hX hZ hI (fun _ => rfl)
  have hval : Real.log (((2 : ℝ≥0) : ℝ) / ((1 : ℝ≥0) : ℝ)) / (2 * Real.log 2) = 1 / 2 := by
    norm_num
    field_simp [log_two_ne_zero]
  rw [hval] at hMI hR
  exact ⟨hMI, hR⟩

/-- The backward channel at `σ2 = 2`, `D = 1` has the Gaussian source marginal and expected
square error exactly `1`. -/
example : (backwardChannelLaw 2 1 : Measure (ℝ × ℝ)).map Prod.fst = gaussianReal 0 2 ∧
    ∫ z, (z.1 - z.2) ^ 2 ∂(backwardChannelLaw 2 1 : Measure (ℝ × ℝ)) = 1 :=
  ⟨backwardChannelLaw_map_fst 2 1 (by norm_num), by
    rw [integral_sq_error_backwardChannelLaw]; norm_num⟩

/-- `D = σ2 / 2` gives exactly one half bit, here at `σ2 = 6`. -/
example : measureMutualInformation (backwardChannelLaw 6 (6 / 2)) = ENNReal.ofReal (1 / 2) :=
  measureMutualInformation_backwardChannelLaw_half 6 (by norm_num)

/-- Combined with the converse, the bound is exact: at source variance `4` and distortion `1`
the Gaussian rate-distortion function is one bit. -/
example : rateDistortion 4 ((1 : ℝ≥0) : ℝ) = ENNReal.ofReal 1 := by
  have hlog : Real.log (((4 : ℝ≥0) : ℝ) / ((1 : ℝ≥0) : ℝ)) / (2 * Real.log 2) = 1 := by
    norm_num
    rw [log_four_eq]
    exact div_self (mul_ne_zero two_ne_zero log_two_ne_zero)
  have hle := rateDistortion_le_ofReal_log_div 4 1 (by norm_num) (by norm_num)
  have hge := rateDistortion_ge_ofReal_log_div 4 1 (by norm_num) (by norm_num)
  rw [hlog] at hle hge
  exact le_antisymm hle hge

/-- Endpoint `D = σ2`: the backward channel is the constant reconstruction, and the bound term
evaluates to `0`. -/
example : backwardChannelLaw 3 3 = constantReconstruction 3 ∧
    rateDistortion 3 ((3 : ℝ≥0) : ℝ) ≤ 0 := by
  refine ⟨backwardChannelLaw_self 3, ?_⟩
  have h := rateDistortion_self_le_ofReal_log_div 3
  rwa [div_self (by norm_num : ((3 : ℝ≥0) : ℝ) ≠ 0), Real.log_one, zero_div,
    ENNReal.ofReal_zero] at h

/-- Endpoint `D = 0`: the backward law has infinite mutual information, while the
zero-denominator formula evaluates to `0`. -/
example : measureMutualInformation (backwardChannelLaw 2 0) = ⊤ :=
  (measureMutualInformation_backwardChannelLaw_zero 2 (by norm_num)).1

/-- Beyond the endpoint, `D = 3 > σ2 = 2`: the truncated backward law is infeasible. -/
example : backwardChannelLaw 2 3 ∉ distortionFeasible 2 ((3 : ℝ≥0) : ℝ) :=
  backwardChannelLaw_not_mem_distortionFeasible 2 3 (by norm_num)

end MathlibExtTest.InformationTheory.GaussianDistortionAttainment
