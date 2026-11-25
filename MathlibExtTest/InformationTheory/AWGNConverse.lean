/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.AWGNConverse

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory
open MathlibExt.InformationTheory.AWGNConverse
open MathlibExt.InformationTheory.ScalarGaussianCoordinates
open scoped ENNReal NNReal

namespace MathlibExtTest.InformationTheory.AWGNConverse

/-- The real Gaussian at an explicitly packaged variance is a probability measure. -/
instance (m s : ℝ) (hs : 0 ≤ s) : IsProbabilityMeasure (gaussianReal m ⟨s, hs⟩) :=
  instIsProbabilityMeasureGaussianReal m ⟨s, hs⟩

/-- Zero power: the zero input, with noise `N(0, 1)` given by the identity on `ℝ`, carries zero
mutual information. -/
example :
    measureMutualInformation
        (⟨(gaussianReal 0 ⟨1, zero_le_one⟩).map (fun x : ℝ => ((0 : ℝ), 0 + x)),
          inferInstance⟩ : ProbabilityMeasure (ℝ × ℝ)) = 0 :=
  measureMutualInformation_scalarAWGN_eq_zero_of_power_zero (X := fun _ => 0) (Z := id)
    measurable_const measurable_id (indepFun_const_left 0 id) one_pos Measure.map_id
    ⟨le_rfl, by simp⟩

/-- Constant input: the input `3`, with noise `N(0, 2)`, meets the power bound at `9` and carries
zero mutual information. -/
example :
    scalarPowerBound (gaussianReal 0 ⟨2, zero_le_two⟩) (fun _ => (3 : ℝ)) (3 ^ 2) ∧
      measureMutualInformation
          (⟨(gaussianReal 0 ⟨2, zero_le_two⟩).map (fun x : ℝ => ((3 : ℝ), 3 + x)),
            inferInstance⟩ : ProbabilityMeasure (ℝ × ℝ)) = 0 :=
  measureMutualInformation_scalarAWGN_const (Z := id) measurable_id two_pos Measure.map_id 3

/-- The lower second moment of the real Gaussian `N(m, v)` is `m² + v`. -/
theorem lintegral_sq_gaussianReal (m : ℝ) (v : ℝ≥0) :
    ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂(gaussianReal m v) = ENNReal.ofReal (m ^ 2 + v) := by
  have hmem : MemLp id 2 (gaussianReal m v) := memLp_id_gaussianReal' 2 ENNReal.ofNat_ne_top
  have hvar : variance id (gaussianReal m v) = v := variance_id_gaussianReal
  have hmean : (∫ x, x ∂(gaussianReal m v)) = m := integral_id_gaussianReal
  have hdecomp := variance_eq_sub hmem
  rw [hvar] at hdecomp
  simp only [Pi.pow_apply, id_eq] at hdecomp
  rw [hmean] at hdecomp
  have hint : Integrable (fun x : ℝ => x ^ 2) (gaussianReal m v) := hmem.integrable_sq
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x => sq_nonneg x)]
  congr 1
  linarith

/-- A Gaussian input `N(1, 2)` with nonzero mean, independent of noise `N(0, 3)` on the product
space, meets the power bound at `1² + 2 = 3`, and the headline bounds its mutual information by
`log (1 + 3 / 3) / (2 log 2) = 1 / 2` bit. -/
example :
    measureMutualInformation
        (⟨((gaussianReal 1 2).prod (gaussianReal 0 ⟨3, by norm_num⟩)).map
            (fun ω : ℝ × ℝ => (ω.1, ω.1 + ω.2)), inferInstance⟩ :
          ProbabilityMeasure (ℝ × ℝ)) ≤ ENNReal.ofReal (1 / 2) := by
  have hpow : scalarPowerBound
      ((gaussianReal 1 2).prod (gaussianReal 0 ⟨3, by norm_num⟩))
      (fun ω : ℝ × ℝ => ω.1) (1 ^ 2 + 2) := by
    refine ⟨by norm_num, le_of_eq ?_⟩
    have hf : Measurable (fun x : ℝ => ENNReal.ofReal (x ^ 2)) := by fun_prop
    have h := lintegral_map hf (measurable_fst (α := ℝ) (β := ℝ))
      (μ := (gaussianReal 1 2).prod (gaussianReal 0 ⟨3, by norm_num⟩))
    rw [Measure.map_fst_prod, measure_univ, one_smul] at h
    rw [← h, lintegral_sq_gaussianReal]
    norm_num
  have hZlaw : ((gaussianReal 1 2).prod
      (gaussianReal 0 ⟨3, by norm_num⟩)).map (fun ω : ℝ × ℝ => ω.2) =
        gaussianReal 0 ⟨3, by norm_num⟩ := by
    change Measure.map Prod.snd _ = _
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  have h := measureMutualInformation_scalarAWGN_le measurable_fst measurable_snd
    (indepFun_prod (X := id) (Y := id) measurable_id measurable_id) (by norm_num : (0 : ℝ) < 3)
    hZlaw hpow
  have hrhs : Real.log (1 + (1 ^ 2 + 2) / 3) / (2 * Real.log 2) = 1 / 2 := by
    have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
    rw [show (1 : ℝ) + (1 ^ 2 + 2) / 3 = 2 by norm_num, mul_comm 2 (Real.log 2), ← div_div,
      div_self hlog]
  rwa [hrhs] at h

/-- Violated premise: the constant input `2` has variance `0 ≤ 1`, yet the total-moment model
rejects it at budget `1`. -/
example :
    variance (fun _ : ℝ => (2 : ℝ)) (gaussianReal 0 ⟨1, zero_le_one⟩) ≤ 1 ∧
      ¬ scalarPowerBound (gaussianReal 0 ⟨1, zero_le_one⟩) (fun _ => (2 : ℝ)) 1 :=
  not_scalarPowerBound_const_of_lt zero_le_one (by norm_num)

end MathlibExtTest.InformationTheory.AWGNConverse
