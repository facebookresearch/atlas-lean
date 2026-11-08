/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.PNat.Notation
public import Mathlib.Probability.CDF
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Moments.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Standardized real laws and their i.i.d. normal approximation

The sample law is the actual countable product of a real Borel probability law.
Every positive finite sum uses its initial coordinates. The CDF and all moments
are Mathlib's measure-theoretic constructions. Arbitrary-universe i.i.d. models
are transported to this canonical realization by equality of pushforward laws.

Source: the classical Berry--Esseen setup; catalogue constants/19a.md, revision
2c1968cd520b60f1cf3cf50749f7285e800e4e15. Historical sharper bounds are not asserted here.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace BerryEsseenModel

/-- A genuine standardized real probability law with a finite third absolute moment. -/
structure IsStandardizedLaw (μ : Measure ℝ) : Prop where
  probability : IsProbabilityMeasure μ
  mean_zero : (∫ x, x ∂μ) = 0
  variance_one : variance id μ = 1
  third_moment : MemLp id 3 μ

/-- The actual independent product realization of the entire sequence. -/
noncomputable def iidLaw (μ : Measure ℝ) : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ ↦ μ)

/-- The first n coordinates, divided by the positive normalizing square root. -/
noncomputable def normalizedSum (n : ℕ+) (ω : ℕ → ℝ) : ℝ :=
  (∑ i ∈ Finset.range n.1, ω i) / Real.sqrt (n.1 : ℝ)

/-- The actual pushforward law of the normalized sum. -/
noncomputable def normalizedLaw (μ : Measure ℝ) (n : ℕ+) : Measure ℝ :=
  (iidLaw μ).map (normalizedSum n)

/-- The standard normal right-continuous CDF. -/
noncomputable def normalCDF (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x

/-- The actual third absolute moment, integrable on standardized laws. -/
noncomputable def thirdMoment (μ : Measure ℝ) : ℝ := ∫ x, |x| ^ 3 ∂μ

/-- On real laws, the model moment condition is exactly finiteness of the source integral. -/
theorem memLp_three_iff_integrable_absCube (μ : Measure ℝ) :
    MemLp id 3 μ ↔ Integrable (fun x : ℝ ↦ |x| ^ 3) μ := by
  simpa [Real.norm_eq_abs] using (integrable_norm_rpow_iff
    (μ := μ) (f := (id : ℝ → ℝ)) (p := (3 : ENNReal))
    measurable_id.aestronglyMeasurable (by norm_num) (by simp)).symm

/-- The supremum of the actual all-threshold CDF error. -/
noncomputable def kolmogorovError (μ : Measure ℝ) (n : ℕ+) : ℝ :=
  sSup (Set.range (fun x : ℝ ↦ |cdf (normalizedLaw μ n) x - normalCDF x|))

/-- The canonical product is a probability measure on admissible laws. -/
theorem iidLaw_probability {μ : Measure ℝ} (hμ : IsStandardizedLaw μ) :
    IsProbabilityMeasure (iidLaw μ) := by
  let : IsProbabilityMeasure μ := hμ.probability
  unfold iidLaw
  infer_instance

/-- The sample map is measurable, so its pushforward is not a fallback measure. -/
theorem normalizedSum_measurable (n : ℕ+) : Measurable (normalizedSum n) :=
  (Finset.measurable_sum _ (fun i _ ↦ measurable_pi_apply i)).div_const _

/-- The normalized law is a probability measure. -/
theorem normalizedLaw_probability {μ : Measure ℝ} (hμ : IsStandardizedLaw μ)
    (n : ℕ+) : IsProbabilityMeasure (normalizedLaw μ n) := by
  let : IsProbabilityMeasure (iidLaw μ) := iidLaw_probability hμ
  unfold normalizedLaw
  infer_instance

/-- Canonical coordinates are genuinely independent. -/
theorem iidLaw_independent {μ : Measure ℝ} (hμ : IsStandardizedLaw μ) :
    iIndepFun (fun (i : ℕ) (ω : ℕ → ℝ) ↦ ω i) (iidLaw μ) := by
  let : IsProbabilityMeasure μ := hμ.probability
  exact iIndepFun_infinitePi (fun _ ↦ measurable_id)

/-- Each canonical coordinate has the original law. -/
theorem iidLaw_map_eval {μ : Measure ℝ} (hμ : IsStandardizedLaw μ) (i : ℕ) :
    (iidLaw μ).map (fun ω ↦ ω i) = μ := by
  let : IsProbabilityMeasure μ := hμ.probability
  exact Measure.infinitePi_map_eval _ i

/-- Each coordinate is identically distributed with the identity on its real law. -/
theorem iidLaw_identDistrib {μ : Measure ℝ} (hμ : IsStandardizedLaw μ) (i : ℕ) :
    IdentDistrib (fun ω : ℕ → ℝ ↦ ω i) id (iidLaw μ) μ := by
  refine ⟨(measurable_pi_apply i).aemeasurable, measurable_id.aemeasurable, ?_⟩
  rw [iidLaw_map_eval hμ, Measure.map_id]

/-- The model CDF is exactly the probability of the source's non-strict event. -/
theorem normalized_cdf_eq {μ : Measure ℝ} (hμ : IsStandardizedLaw μ)
    (n : ℕ+) (x : ℝ) :
    cdf (normalizedLaw μ n) x = (iidLaw μ).real {ω | normalizedSum n ω ≤ x} := by
  let : IsProbabilityMeasure (normalizedLaw μ n) := normalizedLaw_probability hμ n
  rw [cdf_eq_real, normalizedLaw,
    map_measureReal_apply (normalizedSum_measurable n) measurableSet_Iic]
  rfl

/-- The third absolute moment is integrable, not a totalized nonintegrable integral. -/
theorem thirdMoment_integrable {μ : Measure ℝ} (hμ : IsStandardizedLaw μ) :
    Integrable (fun x : ℝ ↦ |x| ^ 3) μ := by
  have h := hμ.third_moment.integrable_norm_rpow (by norm_num) (by norm_num)
  simpa using h

/-- Third absolute moments are nonnegative. -/
theorem thirdMoment_nonnegative (μ : Measure ℝ) : 0 ≤ thirdMoment μ :=
  integral_nonneg (fun x ↦ pow_nonneg (abs_nonneg x) 3)

/-- Variance one excludes a zero third absolute moment. -/
theorem thirdMoment_positive {μ : Measure ℝ} (hμ : IsStandardizedLaw μ) :
    0 < thirdMoment μ := by
  have hne : thirdMoment μ ≠ 0 := by
    intro hz
    have hc : (fun x : ℝ ↦ |x| ^ 3) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg
        (fun x ↦ pow_nonneg (abs_nonneg x) 3) (thirdMoment_integrable hμ)).mp hz
    have hid : id =ᵐ[μ] (0 : ℝ → ℝ) := hc.mono (fun x hx ↦ by simpa using hx)
    have hv := variance_congr hid
    rw [hμ.variance_one, variance_zero] at hv
    norm_num at hv
  exact lt_of_le_of_ne (thirdMoment_nonnegative μ) hne.symm

/-- Every CDF error lies between zero and one. -/
theorem pointwise_error_le_one (μ : Measure ℝ) (n : ℕ+) (x : ℝ) :
    |cdf (normalizedLaw μ n) x - normalCDF x| ≤ 1 := by
  have h₁ := cdf_nonneg (normalizedLaw μ n) x
  have h₂ := cdf_le_one (normalizedLaw μ n) x
  have h₃ := cdf_nonneg (gaussianReal 0 1) x
  have h₄ := cdf_le_one (gaussianReal 0 1) x
  unfold normalCDF
  rw [abs_le]
  constructor <;> linarith

/-- The ordinary real supremum is taken over a nonempty bounded range. -/
theorem errorRange_bddAbove (μ : Measure ℝ) (n : ℕ+) :
    BddAbove (Set.range (fun x : ℝ ↦ |cdf (normalizedLaw μ n) x - normalCDF x|)) := by
  refine ⟨1, ?_⟩
  rintro y ⟨x, rfl⟩
  exact pointwise_error_le_one μ n x

/-- Each actual threshold error is below the supremum. -/
theorem pointwise_le_kolmogorovError (μ : Measure ℝ) (n : ℕ+) (x : ℝ) :
    |cdf (normalizedLaw μ n) x - normalCDF x| ≤ kolmogorovError μ n :=
  le_csSup (errorRange_bddAbove μ n) ⟨x, rfl⟩

/-- The error supremum is nonnegative. -/
theorem kolmogorovError_nonnegative (μ : Measure ℝ) (n : ℕ+) :
    0 ≤ kolmogorovError μ n :=
  (abs_nonneg _).trans (pointwise_le_kolmogorovError μ n 0)

/-- The error supremum is at most one. -/
theorem kolmogorovError_le_one (μ : Measure ℝ) (n : ℕ+) :
    kolmogorovError μ n ≤ 1 := by
  apply csSup_le (Set.range_nonempty _)
  rintro y ⟨x, rfl⟩
  exact pointwise_error_le_one μ n x

/-- A uniform all-threshold estimate is equivalent to its supremum estimate. -/
theorem error_le_iff (μ : Measure ℝ) (n : ℕ+) (a : ℝ) :
    kolmogorovError μ n ≤ a ↔ ∀ x : ℝ, |cdf (normalizedLaw μ n) x - normalCDF x| ≤ a := by
  constructor
  · intro h x
    exact (pointwise_le_kolmogorovError μ n x).trans h
  · intro h
    apply csSup_le (Set.range_nonempty _)
    rintro y ⟨x, rfl⟩
    exact h x

/-- A nondegenerate actual Gaussian belongs to the source domain. -/
theorem standardGaussian_isStandardized : IsStandardizedLaw (gaussianReal 0 1) := by
  refine ⟨inferInstance, integral_id_gaussianReal, ?_, ?_⟩
  · simp [variance_id_gaussianReal]
  · exact memLp_id_gaussianReal (μ := 0) (v := 1) (3 : ℝ≥0)

/-- A one-summand normalized law is the original law. -/
theorem normalizedLaw_one {μ : Measure ℝ} (hμ : IsStandardizedLaw μ) :
    normalizedLaw μ ⟨1, by decide⟩ = μ := by
  have hsum : normalizedSum ⟨1, by decide⟩ = (fun ω : ℕ → ℝ ↦ ω 0) := by
    funext ω
    simp [normalizedSum]
  unfold normalizedLaw
  rw [hsum, iidLaw_map_eval hμ]

/-- The actual one-summand standard Gaussian has zero comparison error. -/
theorem standardGaussian_error_one : kolmogorovError (gaussianReal 0 1) ⟨1, by decide⟩ = 0 := by
  unfold kolmogorovError
  rw [normalizedLaw_one standardGaussian_isStandardized]
  simp [normalCDF]

/-- A source-domain i.i.d. model on an arbitrary measurable carrier. -/
structure IsIIDModel {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) : Prop where
  probability : IsProbabilityMeasure P
  measurable : ∀ i, Measurable (X i)
  independent : iIndepFun X P
  identical : ∀ i, IdentDistrib (X i) (X 0) P P
  mean_zero : (∫ ω, X 0 ω ∂P) = 0
  variance_one : variance (X 0) P = 1
  third_moment : MemLp (X 0) 3 P

/-- The law of the first variable on any carrier is standardized. -/
theorem IsIIDModel.standardizedLaw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℕ → Ω → ℝ} (h : IsIIDModel P X) : IsStandardizedLaw (P.map (X 0)) := by
  let : IsProbabilityMeasure P := h.probability
  have hd : IdentDistrib (X 0) id P (P.map (X 0)) :=
    ⟨(h.measurable 0).aemeasurable, measurable_id.aemeasurable, by simp⟩
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · exact hd.integral_eq.symm.trans h.mean_zero
  · exact hd.variance_eq.symm.trans h.variance_one
  · exact hd.memLp_iff.mp h.third_moment

/-- Equality of the complete sequence law, in every carrier universe. -/
theorem IsIIDModel.jointLaw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℕ → Ω → ℝ} (h : IsIIDModel P X) :
    P.map (fun ω i ↦ X i ω) = iidLaw (P.map (X 0)) := by
  calc
    P.map (fun ω i ↦ X i ω) = Measure.infinitePi (fun i ↦ P.map (X i)) :=
      iIndepFun.map_fun_eq_infinitePi_map h.measurable h.independent
    _ = iidLaw (P.map (X 0)) := by
      unfold iidLaw
      congr 1
      funext i
      exact (h.identical i).map_eq

/-- The actual finite normalized sum law is preserved by canonical transport. -/
theorem IsIIDModel.normalizedLaw_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℕ → Ω → ℝ} (h : IsIIDModel P X) (n : ℕ+) :
    P.map (fun ω ↦ (∑ i ∈ Finset.range n.1, X i ω) / Real.sqrt (n.1 : ℝ)) =
      normalizedLaw (P.map (X 0)) n := by
  rw [normalizedLaw, ← h.jointLaw,
    Measure.map_map (normalizedSum_measurable n) (Measurable.of_eval h.measurable)]
  rfl

/-- Canonical transport preserves the actual third absolute moment. -/
theorem IsIIDModel.thirdMoment_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℕ → Ω → ℝ} (h : IsIIDModel P X) :
    thirdMoment (P.map (X 0)) = ∫ ω, |X 0 ω| ^ 3 ∂P := by
  have hd : IdentDistrib (X 0) id P (P.map (X 0)) :=
    ⟨(h.measurable 0).aemeasurable, measurable_id.aemeasurable, by simp⟩
  exact ((hd.comp (continuous_abs.measurable.pow_const 3)).integral_eq).symm

end BerryEsseenModel
