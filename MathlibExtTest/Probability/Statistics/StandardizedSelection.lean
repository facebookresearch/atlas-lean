/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.GaussianSelection
public import MathlibExt.Probability.Statistics.StandardizedSelection
import MathlibExt.Probability.Distributions.GaussianCdf

/-! # Standardized selection tests

Direct checks of the generic standardized-selection API: invariance of the upper event under
positive rescaling, reflection under negation, the indicator form of the conditional mean shift
on a point mass, the boundary cases of a null event and of a constant score, and the Gaussian
truncation results for the standard normal law (selected proportion, its value `1/2` at `z = 0`,
standardization, selected mean of the standardized score, and the response of a perfectly
correlated quantity).
-/

@[expose] public section

namespace MathlibExtTest.Probability.Statistics.StandardizedSelection

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.Causality.MissingData (inverseMillsRatio inverseMillsRatio_pos)

/-- Tripling a score does not change its standardized upper event. -/
theorem upperEvent_three_mul {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ)
    (z : ℝ) :
    standardizedUpperEvent μ (fun ω => 3 * f ω) z = standardizedUpperEvent μ f z :=
  standardizedUpperEvent_const_mul f z (by norm_num)

/-- The upper event of a negated score is the reflected lower event of the score. -/
theorem upperEvent_neg {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (z : ℝ) :
    standardizedUpperEvent μ (fun ω => -f ω) z = {ω | f ω ≤ μ[f] - z * populationSD μ f} :=
  standardizedUpperEvent_neg μ f z

/-- On the point mass at `1`, selecting the event `[0, ∞)` (which contains the point) does not
change the mean of the identity: the conditional mean shift is `0`. -/
theorem conditionalMeanShift_dirac_one :
    conditionalMeanShift (Measure.dirac (1 : ℝ)) id (Set.Ici 0) = 0 := by
  rw [conditionalMeanShift_eq_indicator_quotient measurableSet_Ici (by simp)]
  simp [integral_dirac]

/-- A null event: conditioning on the empty set gives the zero measure, so the conditional mean
shift is minus the population mean. -/
theorem conditionalMeanShift_empty {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) :
    conditionalMeanShift μ f ∅ = -μ[f] := by
  simp [conditionalMeanShift]

/-- A constant score has population standard deviation `0`. -/
theorem populationSD_const {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (c : ℝ) :
    populationSD μ (fun _ => c) = 0 := by
  have h : evariance (fun _ : Ω => c) μ = 0 :=
    (evariance_eq_zero_iff aemeasurable_const).mpr (by simp)
  simp [populationSD, variance, h]

/-- Under a probability measure, the standardized upper event of a constant score is the whole
space for every threshold (the zero-variance boundary). -/
theorem upperEvent_const {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (c z : ℝ) :
    standardizedUpperEvent μ (fun _ => c) z = Set.univ := by
  ext ω
  simp [standardizedUpperEvent, populationSD_const]

/-- The Pearson quotient with a constant score is `0` (the zero-variance boundary). -/
theorem pearsonRatio_const_left {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (c : ℝ) (g : Ω → ℝ) :
    pearsonRatio μ (fun _ => c) g = 0 := by
  simp [pearsonRatio, populationSD_const]

/-- The identity has variance `1` under the standard normal law. -/
theorem variance_id_std : Var[id; gaussianReal 0 1] = 1 := by
  rw [variance_id_gaussianReal]
  norm_num

/-- Standardizing the identity under the standard normal law gives the standard normal law. -/
theorem hasLaw_standardizedValue_std :
    HasLaw (standardizedValue (gaussianReal 0 1) id) (gaussianReal 0 1) (gaussianReal 0 1) :=
  hasLaw_standardizedValue IsGaussian.hasGaussianLaw_id (by rw [variance_id_std]; norm_num)

/-- Under the standard normal law, the standardized upper event of the identity at `z` has
probability `Φ(-z)`. -/
theorem measureReal_upperEvent_std (z : ℝ) :
    (gaussianReal 0 1).real (standardizedUpperEvent (gaussianReal 0 1) id z) =
      cdf (gaussianReal 0 1) (-z) :=
  measureReal_standardizedUpperEvent IsGaussian.hasGaussianLaw_id
    (by rw [variance_id_std]; norm_num) z

/-- At the threshold `z = 0` half of a standard normal population is selected. -/
theorem measureReal_upperEvent_std_zero :
    (gaussianReal 0 1).real (standardizedUpperEvent (gaussianReal 0 1) id 0) = 1 / 2 := by
  rw [measureReal_upperEvent_std, neg_zero, cdf_gaussianReal_zero]

/-- The selected proportion at `z = 2` is strictly between `0` and `1`. -/
theorem upperTail_two_mem_Ioo : cdf (gaussianReal 0 1) (-2) ∈ Set.Ioo (0 : ℝ) 1 :=
  gaussianUpperTail_mem_Ioo 2

/-- Under the standard normal law, the selected mean of the standardized identity at threshold
`z` is the inverse Mills ratio at `-z`, which is positive. -/
theorem selectedMean_std (z : ℝ) :
    (∫ x, standardizedValue (gaussianReal 0 1) id x
        ∂(gaussianReal 0 1)[|standardizedUpperEvent (gaussianReal 0 1) id z]) =
      inverseMillsRatio (-z) ∧ 0 < inverseMillsRatio (-z) :=
  ⟨integral_cond_standardizedValue measurable_id IsGaussian.hasGaussianLaw_id
    (by rw [variance_id_std]; norm_num) z, inverseMillsRatio_pos (-z)⟩

/-- At `z = 0` the intensity of selection is `φ(0) / (1/2)`. -/
theorem intensity_zero :
    inverseMillsRatio (-0) = gaussianPDFReal 0 1 0 / (1 / 2) := by
  rw [inverseMillsRatio_neg_eq_pdf_div_upperTail, neg_zero, cdf_gaussianReal_zero]

/-- Under the standard normal law, selecting the standardized upper event of the identity at `z`
shifts the mean of `x ↦ a * x` by `inverseMillsRatio (-z) * a`. -/
theorem response_const_mul (a z : ℝ) :
    conditionalMeanShift (gaussianReal 0 1) (fun x => a * x)
        (standardizedUpperEvent (gaussianReal 0 1) id z) = inverseMillsRatio (-z) * a := by
  have hG : HasGaussianLaw (fun x : ℝ => (a * x, id x)) (gaussianReal 0 1) := by
    have h := (IsGaussian.hasGaussianLaw_id (μ := gaussianReal (0 : ℝ) 1)).map_fun
      ((a • ContinuousLinearMap.id ℝ ℝ).prod (ContinuousLinearMap.id ℝ ℝ))
    simpa using h
  rw [conditionalMeanShift_standardizedUpperEvent_gaussian measurable_id hG
    (by rw [variance_id_std]; norm_num)]
  have hcov : cov[id, fun x : ℝ => a * x; gaussianReal 0 1] = a := by
    rw [show (fun x : ℝ => a * x) = fun x => a * id x from rfl, covariance_const_mul_right,
      covariance_self aemeasurable_id, variance_id_std, mul_one]
  rw [hcov, populationSD, variance_id_std, Real.sqrt_one, div_one]

/-- An uncorrelated quantity does not respond: for `x ↦ 0 * x` the shift is `0`, as
`conditionalMeanShift_eq_zero_of_covariance_eq_zero` also gives. -/
theorem response_zero (z : ℝ) :
    conditionalMeanShift (gaussianReal 0 1) (fun x => 0 * x)
        (standardizedUpperEvent (gaussianReal 0 1) id z) = 0 := by
  rw [response_const_mul, mul_zero]

end MathlibExtTest.Probability.Statistics.StandardizedSelection
