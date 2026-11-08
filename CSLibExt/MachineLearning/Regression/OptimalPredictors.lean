/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Median
public import MathlibExt.Probability.Statistics.EstimationRisk
public import Mathlib.Probability.Decision.BayesEstimator
public import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# Bayes estimators for squared and absolute loss: posterior mean and median

For a real quantity to be predicted, the Bayes estimator under squared loss is the posterior
mean, and under absolute loss a posterior median. The statements use Mathlib's decision-theory
framework (`Mathlib/Probability/Decision/`), with a real parameter, a data kernel
`P : Kernel ℝ 𝓧` and a prior `π`.

* `lintegral_sqLoss_integral_le`: for a probability measure `ν` on `ℝ`, the expected squared loss
  `∫ (θ - y)² dν(θ)` (in `ℝ≥0∞`) is minimized at the mean `y = ∫ θ dν`. The statement covers
  measures without a second moment, for which every prediction has infinite expected loss. The
  decomposition into variance plus squared bias is MathlibExt's
  `EstimationRisk.meanSquaredError_eq_variance_add_sq_expectation_sub`.
* `IsPosteriorMean.isBayesEstimator`: a measurable version of the posterior mean is a Bayes
  estimator for squared loss, and the posterior mean `posteriorMean P π` itself is one
  (`isBayesEstimator_posteriorMean`).
* `lintegral_absLoss_le_of_isMedian`: the expected absolute loss is minimized at every median
  (MathlibExt's `ProbabilityTheory.IsMedian` and `integral_abs_sub_le_of_isMedian`).
* `IsPosteriorMedian.isBayesEstimator`: a measurable choice of posterior medians is a Bayes
  estimator for absolute loss. (The existence of a measurable choice, e.g. via the posterior
  quantile function, is not formalized here.)

Without a prior, the conditional mean `E[Y | X]` is the best square-integrable predictor of `Y`
from `X` (MathlibExt's `MeasureTheory.integral_sq_sub_condExp_comap_le`,
`MathlibExt/MeasureTheory/Function/ConditionalExpectation/BestPredictor.lean`). Classification
with 0-1 loss is `CSLibExt/MachineLearning/Generative/BayesClassifier.lean`. Casella–Berger,
Chapter 7 (`FormalizedTextbooks`) treats Bayes risk through posterior expected loss.
-/

@[expose] public section

namespace Cslib.MachineLearning.OptimalPredictors

open MeasureTheory ProbabilityTheory Set MathlibExt.Probability.Statistics
open scoped ENNReal

/-! ### Posterior means for squared loss -/

section SquaredLoss

/-- The squared loss `(θ - y)²` of predicting `y` when the true value is `θ`. -/
noncomputable def sqLoss (θ y : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((θ - y) ^ 2)

theorem measurable_sqLoss : Measurable (Function.uncurry sqLoss) := by
  unfold sqLoss
  fun_prop

/-- **The mean minimizes the expected squared loss.** When the right side is infinite the
inequality is trivial; otherwise `ν` has a second moment and the variance decomposition applies. -/
theorem lintegral_sqLoss_integral_le (ν : Measure ℝ) [IsProbabilityMeasure ν] (y : ℝ) :
    ∫⁻ θ, sqLoss θ (∫ t, t ∂ν) ∂ν ≤ ∫⁻ θ, sqLoss θ y ∂ν := by
  by_cases htop : ∫⁻ θ, sqLoss θ y ∂ν = ∞
  · rw [htop]
    exact le_top
  have hsq : Integrable (fun θ : ℝ => (θ - y) ^ 2) ν := by
    refine ⟨by fun_prop, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun θ => sq_nonneg _)]
    exact lt_top_iff_ne_top.mpr htop
  have hmem : MemLp (fun θ : ℝ => θ - y) 2 ν :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mpr hsq
  have hν : MemLp id 2 ν := by
    convert hmem.add (memLp_const y) using 1
    funext θ
    simp
  have hsq' : Integrable (fun θ : ℝ => (θ - ∫ t, t ∂ν) ^ 2) ν :=
    (hν.sub (memLp_const _)).integrable_sq
  have hdecomp : ∫ θ, (θ - y) ^ 2 ∂ν =
      ∫ θ, (θ - ∫ t, t ∂ν) ^ 2 ∂ν + ((∫ t, t ∂ν) - y) ^ 2 := by
    have h := EstimationRisk.meanSquaredError_eq_variance_add_sq_expectation_sub (W := id)
      (μ := ⟨ν, inferInstance⟩) (θ := y) hν
    rw [variance_eq_integral measurable_id.aemeasurable] at h
    exact h
  simp only [sqLoss]
  rw [← ofReal_integral_eq_lintegral_ofReal hsq' (ae_of_all _ fun θ => sq_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal hsq (ae_of_all _ fun θ => sq_nonneg _),
    hdecomp]
  exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (sq_nonneg _))

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {P : Kernel ℝ 𝓧} [IsFiniteKernel P] {π : Measure ℝ}
  [IsFiniteMeasure π] {f : 𝓧 → ℝ}

/-- The posterior mean `x ↦ ∫ θ d(P†π x)(θ)`. -/
noncomputable def posteriorMean (P : Kernel ℝ 𝓧) [IsFiniteKernel P] (π : Measure ℝ)
    [IsFiniteMeasure π] (x : 𝓧) : ℝ :=
  ∫ θ, θ ∂(P†π) x

theorem measurable_posteriorMean (P : Kernel ℝ 𝓧) [IsFiniteKernel P] (π : Measure ℝ)
    [IsFiniteMeasure π] : Measurable (posteriorMean P π) :=
  (StronglyMeasurable.integral_kernel_prod_right (f := fun (_ : 𝓧) (θ : ℝ) => θ)
    measurable_snd.stronglyMeasurable).measurable

/-- `f` is a measurable version of the posterior mean. -/
structure IsPosteriorMean (P : Kernel ℝ 𝓧) [IsFiniteKernel P] (π : Measure ℝ) [IsFiniteMeasure π]
    (f : 𝓧 → ℝ) : Prop where
  measurable : Measurable f
  ae_eq : ∀ᵐ x ∂(P ∘ₘ π), f x = posteriorMean P π x

theorem IsPosteriorMean.isArgminEstimator (hf : IsPosteriorMean P π f) :
    IsArgminEstimator sqLoss P π f := by
  refine ⟨hf.measurable, ?_⟩
  filter_upwards [hf.ae_eq] with x hx
  refine le_antisymm (le_iInf fun y => ?_) (iInf_le _ _)
  rw [hx]
  exact lintegral_sqLoss_integral_le _ y

/-- **The posterior mean is the Bayes estimator for squared loss.** -/
theorem IsPosteriorMean.isBayesEstimator (hf : IsPosteriorMean P π f) :
    IsBayesEstimator sqLoss P (Kernel.deterministic f hf.measurable) π :=
  hf.isArgminEstimator.isBayesEstimator measurable_sqLoss

theorem isBayesEstimator_posteriorMean (P : Kernel ℝ 𝓧) [IsFiniteKernel P] (π : Measure ℝ)
    [IsFiniteMeasure π] :
    IsBayesEstimator sqLoss P (Kernel.deterministic _ (measurable_posteriorMean P π)) π :=
  IsPosteriorMean.isBayesEstimator ⟨measurable_posteriorMean P π, ae_of_all _ fun _ => rfl⟩

end SquaredLoss

/-! ### Medians for absolute loss -/

section AbsoluteLoss

/-- The absolute loss `|θ - y|` of predicting `y` when the true value is `θ`. -/
noncomputable def absLoss (θ y : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal |θ - y|

theorem measurable_absLoss : Measurable (Function.uncurry absLoss) := by
  unfold absLoss
  fun_prop

/-- The expected absolute loss is minimized at every median, in `ℝ≥0∞`. -/
theorem lintegral_absLoss_le_of_isMedian (ν : Measure ℝ) [IsProbabilityMeasure ν] {m : ℝ}
    (hm : IsMedian ν m) (y : ℝ) : ∫⁻ θ, absLoss θ m ∂ν ≤ ∫⁻ θ, absLoss θ y ∂ν := by
  by_cases htop : ∫⁻ θ, absLoss θ y ∂ν = ∞
  · rw [htop]
    exact le_top
  have hint : Integrable (fun θ : ℝ => |θ - y|) ν := by
    refine ⟨by fun_prop, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun θ => abs_nonneg _)]
    exact lt_top_iff_ne_top.mpr htop
  have hmint := (integrable_abs_sub_iff ν m).mpr ((integrable_abs_sub_iff ν y).mp hint)
  simp only [absLoss]
  rw [← ofReal_integral_eq_lintegral_ofReal hmint (ae_of_all _ fun θ => abs_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun θ => abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (integral_abs_sub_le_of_isMedian ν hm y)

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {P : Kernel ℝ 𝓧} [IsFiniteKernel P] {π : Measure ℝ}
  [IsFiniteMeasure π] {f : 𝓧 → ℝ}

/-- `f` is a measurable choice of posterior medians: for almost every observation `x`, `f x` is
a median of the posterior `P†π x`. -/
structure IsPosteriorMedian (P : Kernel ℝ 𝓧) [IsFiniteKernel P] (π : Measure ℝ)
    [IsFiniteMeasure π] (f : 𝓧 → ℝ) : Prop where
  measurable : Measurable f
  ae_isMedian : ∀ᵐ x ∂(P ∘ₘ π), IsMedian ((P†π) x) (f x)

theorem IsPosteriorMedian.isArgminEstimator (hf : IsPosteriorMedian P π f) :
    IsArgminEstimator absLoss P π f := by
  refine ⟨hf.measurable, ?_⟩
  filter_upwards [hf.ae_isMedian] with x hx
  exact le_antisymm (le_iInf fun y => lintegral_absLoss_le_of_isMedian _ hx y) (iInf_le _ _)

/-- **A posterior median is a Bayes estimator for absolute loss.** -/
theorem IsPosteriorMedian.isBayesEstimator (hf : IsPosteriorMedian P π f) :
    IsBayesEstimator absLoss P (Kernel.deterministic f hf.measurable) π :=
  hf.isArgminEstimator.isBayesEstimator measurable_absLoss

end AbsoluteLoss

end Cslib.MachineLearning.OptimalPredictors
