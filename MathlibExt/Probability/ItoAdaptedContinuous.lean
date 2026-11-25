/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.ItoIntegralContinuous
public import Mathlib.Probability.Process.Indistinguishable
import Mathlib.Topology.DenseEmbedding

/-!
# Adapted continuous versions of the Itô integral

The existing continuous modification of the Itô integral need not be adapted
to an arbitrary filtration. For a complete filtration, fixed-time almost-sure
equality transfers adaptedness. The continuous modification is then a progressive
continuous martingale. Two continuous modifications are indistinguishable;
this last fact needs no filtration or completeness hypothesis.

The complete-filtration convention is explicit in Le Gall, *Brownian Motion,
Martingales, and Stochastic Calculus* (2016), Definition 8.1, and is used in the
classical Lipschitz SDE theorem (Theorem 8.3). The result here supplies the version
needed for that construction; it does not assert that completeness is necessary.
The stochastic integral and its continuous modification are the existing Atlas
constructions, following Karatzas–Shreve, Section 3.2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped NNReal ENNReal

/-- A fixed-time almost-sure modification of an adapted process is adapted if
every sigma algebra of the filtration contains all null sets. -/
theorem MeasureTheory.Adapted.congr_ae_of_complete
    {ι Ω E : Type*} [Preorder ι] {mΩ : MeasurableSpace Ω} [MeasurableSpace E]
    {P : Measure Ω} {F : Filtration ι mΩ} [F.IsComplete P]
    {X Y : ι → Ω → E} (hX : Adapted F X) (he : ∀ t, X t =ᵐ[P] Y t) : Adapted F Y := by
  intro t s hs
  apply Filtration.IsComplete.measurableSet_of_ae_eq (μ := P) (hX t hs)
  filter_upwards [he t] with ω hω
  simp only [mem_preimage, hω]

/-- Fixed-time almost-sure equality of two almost-surely continuous processes
on a separable time space implies indistinguishability. No filtration is needed. -/
theorem ProbabilityTheory.indistinguishable_of_ae_eq_of_continuous
    {ι Ω E : Type*} [TopologicalSpace ι] [SeparableSpace ι]
    [TopologicalSpace E] [T2Space E] [MeasurableSpace Ω] {P : Measure Ω}
    {X Y : ι → Ω → E} (hX : ∀ᵐ ω ∂P, Continuous fun t ↦ X t ω)
    (hY : ∀ᵐ ω ∂P, Continuous fun t ↦ Y t ω) (he : ∀ t, X t =ᵐ[P] Y t) :
    X ≡ᵐ[P] Y := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ι
  have hd : ∀ᵐ ω ∂P, ∀ t ∈ D, X t ω = Y t ω :=
    (ae_ball_iff hDc).2 (fun t _ ↦ he t)
  filter_upwards [hX, hY, hd] with ω hXω hYω hDω
  have hf := hDd.denseRange_val.equalizer hXω hYω
    (funext fun t : D ↦ hDω t t.property)
  exact fun t ↦ congr_fun hf t

/-- For a complete filtration, the Itô integral of a progressive, locally
square-integrable integrand has an adapted continuous martingale version.
The version has continuous paths on every sample and is progressive. -/
theorem ProbabilityTheory.itoIntegral_exists_continuous_martingale
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} [F.IsComplete P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    {H : ℝ≥0 → Ω → ℝ} (hH : IsProgressive F H)
    (hH2 : ∀ t : ℝ≥0, ∫⁻ ω, (∫⁻ u in Ioc (0 : ℝ) t,
      ‖H u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞) :
    ∃ J : ℝ≥0 → Ω → ℝ, Martingale J F P ∧ IsProgressive F J ∧
      (∀ ω, Continuous fun t ↦ J t ω) ∧ ∀ t, J t =ᵐ[P] itoIntegral P F B H t := by
  obtain ⟨J, hc, he⟩ := itoIntegral_continuous_modification hB hBF hInd hH hH2
  have hm := martingale_itoIntegral_of_isProgressive hB.toIsPreBrownianReal hBF hInd hH hH2
  have ha : Adapted F J := hm.stronglyAdapted.adapted.congr_ae_of_complete
    (fun t ↦ (he t).symm)
  exact ⟨J, hm.congr ha.stronglyAdapted (fun t ↦ (he t).symm),
    (ha.stronglyAdapted.isStronglyProgressive_of_continuous hc).isProgressive, hc, he⟩
