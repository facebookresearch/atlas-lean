/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.HasLaw
public import Mathlib.MeasureTheory.Constructions.Pi
public import MathlibExt.Probability.Statistics.Likelihood
import MathlibExt.Probability.MonteCarloRate

/-!
# The sample law of an i.i.d. tuple

If random variables `X i`, `i : Fin n`, are mutually independent and each has law `ν`, the
tuple `ω ↦ (X i ω)ᵢ` has law `νⁿ = Measure.pi (fun _ => ν)`, and conversely. Consequently the
sampling distribution of a measurable statistic `T` of the sample is `(νⁿ).map T`. The forward
direction is Mathlib's `ProbabilityTheory.iIndepFun.hasLaw_pi`; the tuple-law results here hold
for every `n`, including `n = 0`. The normalized empirical mean additionally requires `0 < n`
(no average is claimed at `n = 0`); it needs only common marginals, not independence.

## Main results

* `iIndepFun_and_hasLaw_of_hasLaw_tuple_pi`: a tuple with law `νⁿ` has independent coordinates,
  each with law `ν`.
* `hasLaw_statistic`: the sampling distribution of a measurable statistic.
* `integral_empiricalMean_of_common_marginals`: the empirical average has expectation
  `∫ g dν` for common marginals, with no independence hypothesis.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MathlibExt.Probability.Statistics

/-- **Converse of `iIndepFun.hasLaw_pi`.** If the tuple has law `νⁿ`, the coordinates are
independent and each has law `ν`. -/
theorem iIndepFun_and_hasLaw_of_hasLaw_tuple_pi {Ω S : Type*} [MeasurableSpace Ω]
    [MeasurableSpace S] {μ : Measure Ω} [IsProbabilityMeasure μ] {ν : Measure S}
    [IsProbabilityMeasure ν] {n : ℕ} {X : Fin n → Ω → S}
    (h : HasLaw (fun ω i => X i ω) (Measure.pi fun _ : Fin n => ν) μ) :
    iIndepFun X μ ∧ ∀ i, HasLaw (X i) ν μ := by
  have hX : ∀ i, HasLaw (X i) ν μ := fun i =>
    (measurePreserving_eval (fun _ : Fin n => ν) i).hasLaw.comp h
  exact ⟨(iIndepFun_iff_hasLaw_pi_pi hX).2 h, hX⟩

/-- **Sampling distribution of a statistic.** For a measurable statistic `T` of an i.i.d.
tuple with marginal law `ν`, `T (X₁, …, Xₙ)` has law `(νⁿ).map T`. -/
theorem hasLaw_statistic {Ω S U : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    [MeasurableSpace U] {μ : Measure Ω} [IsProbabilityMeasure μ] {ν : Measure S}
    [IsProbabilityMeasure ν] {n : ℕ} {X : Fin n → Ω → S} (hlaw : ∀ i, HasLaw (X i) ν μ)
    (hind : iIndepFun X μ) {T : (Fin n → S) → U} (hT : Measurable T) :
    HasLaw (fun ω => T fun i => X i ω) ((Measure.pi fun _ : Fin n => ν).map T) μ := by
  exact (hasLaw_map hT.aemeasurable).comp (hind.hasLaw_pi hlaw)

/-- **Empirical integral under common marginals.** For a `Fin n` family with common marginal
law `ν`, `n > 0`, the expectation of the empirical average of an integrable `g`
is the population integral `∫ g dν`. Independence is unnecessary (linearity of the integral
(`integral_sample_mean`) only). Proved directly; `hasLaw_statistic` is not used. -/
theorem integral_empiricalMean_of_common_marginals
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ν : Measure S} [IsProbabilityMeasure ν]
    {n : ℕ} (hn : 0 < n) {g : S → ℝ} (hg : Integrable g ν)
    {X : Fin n → Ω → S} (hlaw : ∀ i, HasLaw (X i) ν μ) :
    ∫ ω, (∑ i, g (X i ω)) / n ∂μ = ∫ s, g s ∂ν := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hInt : ∀ i : Fin n, Integrable (fun ω => g (X i ω)) μ :=
    fun i => (hlaw i).integrable_comp hg
  have hMean : ∀ i : Fin n, (∫ ω, g (X i ω) ∂μ) = ∫ s, g s ∂ν := fun i => by
    have h := (hlaw i).integral_comp hg.aestronglyMeasurable
    simpa [Function.comp_def] using h
  have h := MathlibExt.Probability.integral_sample_mean (ι := Fin n)
    (X := fun i ω => g (X i ω)) (mu := ∫ s, g s ∂ν) hInt hMean
  rwa [Fintype.card_fin] at h

end MathlibExt.Probability.Statistics

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

private theorem lintegral_const_mul_ae {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (r : ℝ≥0∞) {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    ∫⁻ a, r * f a ∂μ = r * ∫⁻ a, f a ∂μ := by
  have h_eq : f =ᵐ[μ] AEMeasurable.mk f hf := hf.ae_eq_mk
  have h_mul : (fun a => r * f a) =ᵐ[μ] (fun a => r * AEMeasurable.mk f hf a) :=
    Filter.EventuallyEq.mul Filter.EventuallyEq.rfl h_eq
  rw [lintegral_congr_ae h_mul, lintegral_const_mul r hf.measurable_mk,
    lintegral_congr_ae h_eq]

private theorem lintegral_mul_const_ae {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (r : ℝ≥0∞) {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    ∫⁻ a, f a * r ∂μ = (∫⁻ a, f a ∂μ) * r := by
  have h_eq : f =ᵐ[μ] AEMeasurable.mk f hf := hf.ae_eq_mk
  have h_mul : (fun a => f a * r) =ᵐ[μ] (fun a => AEMeasurable.mk f hf a * r) :=
    Filter.EventuallyEq.mul h_eq Filter.EventuallyEq.rfl
  rw [lintegral_congr_ae h_mul, lintegral_mul_const r hf.measurable_mk,
    lintegral_congr_ae h_eq]

private theorem MeasurePreserving_lintegral_comp_ae {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {ν : Measure β} {e : α → β}
    (he : MeasurePreserving e μ ν) {f : β → ℝ≥0∞} (hf : AEMeasurable f ν) :
    ∫⁻ a, f (e a) ∂μ = ∫⁻ b, f b ∂ν := by
  have h_eq : f =ᵐ[ν] AEMeasurable.mk f hf := hf.ae_eq_mk
  have h_comp : (f ∘ e) =ᵐ[μ] (AEMeasurable.mk f hf ∘ e) :=
    he.quasiMeasurePreserving.ae_eq_comp h_eq
  have h1 : (fun a => f (e a)) =ᵐ[μ] (fun a => AEMeasurable.mk f hf (e a)) := h_comp
  rw [lintegral_congr_ae h1, he.lintegral_comp hf.measurable_mk, lintegral_congr_ae h_eq]

private theorem lintegral_pi_fin_prod {n : ℕ} {S : Type*} [MeasurableSpace S]
    (μ : Fin n → Measure S) [∀ i, SigmaFinite (μ i)]
    (f : Fin n → S → ℝ≥0∞) (hf : ∀ i, AEMeasurable (f i) (μ i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ y, f i y ∂(μ i) := by
  induction n with
  | zero =>
    have h_univ : (Set.univ.pi fun _ : Fin 0 => Set.univ (α := S)) = Set.univ := by simp
    rw [show (fun x : Fin 0 → S => ∏ i, f i (x i)) = fun _ => 1 from
      funext fun x => Fin.prod_univ_zero _]
    rw [lintegral_one, ← h_univ, Measure.pi_pi]
    simp
  | succ n ih =>
    let i₀ : Fin (n + 1) := 0
    let μtail : Fin n → Measure S := fun j => μ (i₀.succAbove j)
    let ftail : Fin n → S → ℝ≥0∞ := fun j => f (i₀.succAbove j)
    have : ∀ j, SigmaFinite (μtail j) := fun j => inferInstance
    have hf_tail : ∀ j, AEMeasurable (ftail j) (μtail j) := fun j => hf _
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => S) i₀
    have he_pres : MeasurePreserving (⇑e) (Measure.pi μ)
        ((μ i₀).prod (Measure.pi μtail)) :=
      measurePreserving_piFinSuccAbove μ i₀
    have hProd_tail : AEMeasurable (fun b : Fin n → S => ∏ j, ftail j (b j))
        (Measure.pi μtail) := by
      have := Finset.aemeasurable_fun_prod (M := ℝ≥0∞) (μ := Measure.pi μtail)
        (f := fun j b => ftail j (b j)) Finset.univ (fun j _ =>
        (hf_tail j).comp_quasiMeasurePreserving
          (Measure.quasiMeasurePreserving_eval μtail j))
      simpa using this
    have h1 : AEMeasurable (fun z : S × (Fin n → S) => f i₀ z.1)
        ((μ i₀).prod (Measure.pi μtail)) :=
      (hf i₀).comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
    have h2 : AEMeasurable (fun z : S × (Fin n → S) => ∏ j, ftail j (z.2 j))
        ((μ i₀).prod (Measure.pi μtail)) :=
      hProd_tail.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    let g : S × (Fin n → S) → ℝ≥0∞ := fun z => f i₀ z.1 * ∏ j, ftail j (z.2 j)
    have hg : AEMeasurable g ((μ i₀).prod (Measure.pi μtail)) := h1.mul h2
    have hFG : (fun x : Fin (n + 1) → S => ∏ i, f i (x i)) = (fun x => g (e x)) := by
      funext x
      simp only [g]
      rw [Fin.prod_univ_succAbove (fun i => f i (x i)) i₀]
      have he1 : (e x).1 = x i₀ := by
        simp [e, MeasurableEquiv.piFinSuccAbove_apply]
      have he2 : ∀ j, (e x).2 j = x (i₀.succAbove j) := fun j => by
        simp [e, MeasurableEquiv.piFinSuccAbove_apply, Fin.removeNth_apply]
      simp only [he1, he2, ftail]
    rw [hFG, MeasurePreserving_lintegral_comp_ae he_pres hg, lintegral_prod g hg]
    have hinner : ∀ a : S, (∫⁻ b, g (a, b) ∂(Measure.pi μtail))
        = f i₀ a * ∏ j, ∫⁻ y, ftail j y ∂(μtail j) := by
      intro a
      have h_eq : (fun b : Fin n → S => g (a, b))
          = (fun b => f i₀ a * ∏ j, ftail j (b j)) := rfl
      rw [h_eq, lintegral_const_mul_ae _ hProd_tail, ih μtail ftail hf_tail]
    simp only [hinner]
    rw [lintegral_mul_const_ae _ (hf i₀)]
    exact (Fin.prod_univ_succAbove (fun i => ∫⁻ y, f i y ∂(μ i)) i₀).symm

namespace MathlibExt.Probability.Statistics

/-- **Tuple law as a product density.** The joint law of an i.i.d. sample from a
normalized density family is the product base measure with the `iidLikelihood` product
as density. -/
theorem HasLaw_tuple_of_iidLikelihood
    {Ω S Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {μ₀ : Measure S} [SigmaFinite μ₀]
    {F : NormalizedDensityFamily S Θ μ₀} {θ : Θ} {n : ℕ}
    {X : Fin n → Ω → S}
    (hlaw : ∀ i, HasLaw (X i) (F.law θ) μ) (hind : iIndepFun X μ) :
    HasLaw (fun ω i => X i ω)
      ((Measure.pi fun _ : Fin n => μ₀).withDensity
        fun x : Fin n → S => ∏ i, F.dens θ (x i)) μ := by
  have : IsProbabilityMeasure (F.law θ) := F.isProbabilityMeasure_law θ
  have hPi : HasLaw (fun ω i => X i ω) (Measure.pi fun _ : Fin n => F.law θ) μ :=
    hind.hasLaw_pi hlaw
  have hEq : (Measure.pi fun _ : Fin n => F.law θ)
      = ((Measure.pi fun _ : Fin n => μ₀).withDensity
        fun x : Fin n → S => ∏ i, F.dens θ (x i)) := by
    apply Measure.pi_eq
    intro s hs
    have hbox : MeasurableSet (Set.univ.pi fun i => s i) :=
      MeasurableSet.pi (Set.to_countable _) (fun i _ => hs i)
    rw [withDensity_apply _ hbox]
    have h_restrict : (Measure.pi fun _ : Fin n => μ₀).restrict
        (Set.univ.pi fun i => s i)
        = Measure.pi (fun i => (μ₀).restrict (s i)) :=
      Measure.restrict_pi_pi _ _
    rw [h_restrict]
    rw [lintegral_pi_fin_prod _ _ (fun i => (F.measurable θ).restrict)]
    apply Finset.prod_congr rfl
    intro i _
    rw [NormalizedDensityFamily.law, withDensity_apply _ (hs i)]
  rw [← hEq]
  exact hPi

end MathlibExt.Probability.Statistics
