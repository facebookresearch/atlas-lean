/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Measurement.ProductMoments
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Kernel.Composition.MeasureComp

import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Probability.ProbabilityMassFunction.Monad

/-! # Item response models with a continuous latent trait -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MathlibExt.Probability.Statistics.Measurement

/-- A real-valued latent ability with probability law `ability`, and a measurable success
curve `curve i` taking values in `[0, 1]` for each item. For a finite set of binary items,
the conditional response law is the locally independent product law. No density for
`ability` is required. See F. M. Lord, *Applications of Item Response Theory to Practical
Testing Problems* (1980), and G. Rasch, *Probabilistic Models for Some Intelligence and
Attainment Tests* (1960). -/
structure ContinuousLatentTrait (ι : Type*) where
  /-- The population law of latent ability on `ℝ`. -/
  ability : ProbabilityMeasure ℝ
  /-- The probability of a positive response to each item, as a function of ability. -/
  curve : ι → ℝ → ℝ
  /-- Each success curve is measurable. -/
  measurable_curve : ∀ i, Measurable (curve i)
  /-- Each success probability is nonnegative. -/
  curve_nonneg : ∀ i θ, 0 ≤ curve i θ
  /-- Each success probability is at most one. -/
  curve_le_one : ∀ i θ, curve i θ ≤ 1

namespace ContinuousLatentTrait

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (M : ContinuousLatentTrait ι)

/-- At a fixed ability `θ`, the binary responses have the product PMF of the item curves. -/
noncomputable def responsePMF (θ : ℝ) : PMF (ι → Bool) :=
  localIndepPMF (fun i => M.curve i θ) (fun i => M.curve_nonneg i θ)
    (fun i => M.curve_le_one i θ)

private theorem measurable_responsePMF_apply (x : ι → Bool) :
    Measurable fun θ => M.responsePMF θ x := by
  simp_rw [responsePMF, localIndepPMF_apply]
  apply Finset.measurable_prod
  intro i _
  have hzero : Measurable (fun θ => (1 : ℝ) - M.curve i θ) :=
    measurable_const.sub (M.measurable_curve i)
  have h₀ : Measurable (fun θ => ENNReal.ofReal (1 - M.curve i θ)) :=
    ENNReal.measurable_ofReal.comp hzero
  have h₁ : Measurable (fun θ => ENNReal.ofReal (M.curve i θ)) :=
    ENNReal.measurable_ofReal.comp (M.measurable_curve i)
  cases h : x i
  · simpa only [h, Bool.false_eq_true, ite_false] using h₀
  · simpa only [h, ite_true] using h₁

/-- The locally independent conditional response laws form a measurable Markov kernel. -/
noncomputable def responseKernel : Kernel ℝ (ι → Bool) where
  toFun θ := (M.responsePMF θ).toMeasure
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp_rw [PMF.toMeasure_apply _ hs, tsum_fintype]
    apply Finset.measurable_sum
    intro x _
    by_cases hx : x ∈ s
    · simpa only [Set.indicator_of_mem hx] using M.measurable_responsePMF_apply x
    · simpa only [Set.indicator_of_notMem hx] using
        (measurable_const : Measurable (fun _ : ℝ => (0 : ℝ≥0∞)))

instance : IsMarkovKernel M.responseKernel :=
  ⟨fun θ => PMF.toMeasure.isProbabilityMeasure (M.responsePMF θ)⟩

/-- The joint probability law of latent ability and the binary response pattern. -/
noncomputable def jointLaw : Measure (ℝ × (ι → Bool)) :=
  (M.ability : Measure ℝ) ⊗ₘ M.responseKernel

instance : IsProbabilityMeasure M.jointLaw := by unfold jointLaw; infer_instance

/-- The observed response law obtained by mixing the conditional response kernel over ability. -/
noncomputable def responseLaw : Measure (ι → Bool) :=
  M.responseKernel ∘ₘ (M.ability : Measure ℝ)

instance : IsProbabilityMeasure M.responseLaw := by unfold responseLaw; infer_instance

/-- The first marginal is the ability law, and the second is the observed response law. -/
theorem jointLaw_marginals : M.jointLaw.fst = (M.ability : Measure ℝ) ∧
    M.jointLaw.snd = M.responseLaw :=
  ⟨Measure.fst_compProd _ _, Measure.snd_compProd _ _⟩

/-- The probability of a response pattern is the ability integral of the product of the
selected item probabilities, `curve i θ` for a positive response and `1 - curve i θ` otherwise. -/
theorem responseLaw_real_singleton (x : ι → Bool) :
    M.responseLaw.real {x} = ∫ θ, ∏ i, (if x i then M.curve i θ else 1 - M.curve i θ)
      ∂(M.ability : Measure ℝ) := by
  let G : Measure ℝ := M.ability
  let w : ℝ → ℝ≥0∞ := fun θ => M.responsePMF θ x
  have hw : Measurable w := M.measurable_responsePMF_apply x
  have hmass (θ : ℝ) : M.responseKernel θ {x} = w θ :=
    PMF.toMeasure_apply_singleton _ x (measurableSet_singleton x)
  have hresponse : M.responseLaw {x} = ∫⁻ θ, w θ ∂G := by
    unfold responseLaw
    rw [Measure.bind_apply (measurableSet_singleton x) M.responseKernel.aemeasurable]
    exact lintegral_congr hmass
  have hprod (θ : ℝ) : (w θ).toReal = ∏ i, (if x i then M.curve i θ else 1 - M.curve i θ) :=
    localIndepPMF_toReal_apply _ _ _ x
  simp_rw [← hprod]
  change (M.responseLaw {x}).toReal = ∫ θ, (w θ).toReal ∂G
  rw [hresponse, integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun θ => ENNReal.toReal_nonneg (a := w θ))
    (ENNReal.measurable_toReal.comp hw).aestronglyMeasurable]
  congr 1
  exact lintegral_congr fun θ => (ENNReal.ofReal_toReal ((M.responsePMF θ).apply_ne_top x)).symm

/-- A finitely supported ability law given as the pushforward of a finite class PMF gives
exactly the finite latent-class mixture of product PMFs. -/
theorem responseLaw_eq_finite_mixture {Z : Type*} [Finite Z] [MeasurableSpace Z]
    [MeasurableSingletonClass Z] (π : PMF Z) (θ : Z → ℝ) (hθ : Measurable θ)
    (hG : (M.ability : Measure ℝ) = π.toMeasure.map θ) :
    M.responseLaw = (π.bind fun z => M.responsePMF (θ z)).toMeasure := by
  let := Fintype.ofFinite Z
  ext s hs
  unfold responseLaw
  rw [Measure.bind_apply hs M.responseKernel.aemeasurable, hG,
    lintegral_map (M.responseKernel.measurable_coe hs) hθ, lintegral_fintype,
    PMF.toMeasure_bind_apply π (fun z => M.responsePMF (θ z)) s hs, tsum_fintype]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [PMF.toMeasure_apply_singleton π z (measurableSet_singleton z), mul_comm]
  rfl

/-- Logistic item curves recover the existing two-parameter logistic conditional law. -/
theorem responsePMF_eq_twoPL (a b : ι → ℝ)
    (hc : ∀ i θ, M.curve i θ = Real.sigmoid (a i * (θ - b i))) (θ : ℝ) :
    M.responsePMF θ = twoPLPMF a b θ := by
  apply PMF.ext
  intro x
  simp only [responsePMF, localIndepPMF_apply, twoPLPMF_apply, hc]

/-- Unit discriminations recover the existing Rasch conditional law. -/
theorem responsePMF_eq_rasch (b : ι → ℝ)
    (hc : ∀ i θ, M.curve i θ = Real.sigmoid (θ - b i)) (θ : ℝ) :
    M.responsePMF θ = raschPMF b θ := by
  rw [raschPMF_eq_twoPLPMF_one]
  exact M.responsePMF_eq_twoPL (fun _ => 1) b (by simpa only [one_mul] using hc) θ

end ContinuousLatentTrait

end MathlibExt.Probability.Statistics.Measurement
