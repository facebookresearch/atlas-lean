/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Foundations.AeTailInvariant

open MeasureTheory ProbabilityTheory MeasurableSpace Set
open scoped ENNReal

set_option linter.unusedSectionVars false

namespace StatMech

open ConfigSpace

variable {E : Type*} [Countable E]



theorem ts_trim_restrict_comm {Omega : Type*}
    {m mOmega : MeasurableSpace Omega}
    (mu : @Measure Omega mOmega) (hm : m ≤ mOmega)
    (s : Set Omega) (hs : @MeasurableSet Omega m s) :
    @Measure.trim Omega m mOmega (@Measure.restrict Omega mOmega mu s) hm =
      @Measure.restrict Omega m (@Measure.trim Omega m mOmega mu hm) s := by
  apply @Measure.ext Omega m
  intro t ht
  rw [@trim_measurableSet_eq Omega m mOmega _ t hm ht,
    @Measure.restrict_apply Omega m (@Measure.trim Omega m mOmega mu hm) s t ht,
    @Measure.restrict_apply Omega mOmega mu s t (hm t ht),
    @trim_measurableSet_eq Omega m mOmega mu (t ∩ s) hm (ht.inter hs)]

theorem ts_compProd_restrict_left {alpha beta : Type*}
    {mAlpha : MeasurableSpace alpha} {mBeta : MeasurableSpace beta}
    (mu : @Measure alpha mAlpha) [SFinite mu]
    (K : @Kernel alpha beta mAlpha mBeta) [IsSFiniteKernel K]
    (s : Set alpha) (hs : MeasurableSet s) :
    (mu.restrict s) ⊗ₘ K = (mu ⊗ₘ K).restrict (s ×ˢ Set.univ) := by
  apply Measure.ext
  intro t ht
  rw [Measure.compProd_apply ht, Measure.restrict_apply ht,
    Measure.compProd_apply (ht.inter (hs.prod MeasurableSet.univ)),
    ← lintegral_indicator hs]
  congr 1
  funext a
  by_cases ha : a ∈ s
  · rw [Set.indicator_of_mem ha]
    congr 1
    ext b
    simp [ha]
  · rw [Set.indicator_of_notMem ha]
    have hempty : Prod.mk a ⁻¹' (t ∩ s ×ˢ Set.univ) = ∅ := by
      ext b
      simp [ha]
    rw [hempty, measure_empty]

theorem ts_map_diag_restrict {Omega : Type*}
    {m mOmega : MeasurableSpace Omega}
    (mu : @Measure Omega mOmega) (s : Set Omega)
    (hs : @MeasurableSet Omega m s)
    (hf : @Measurable Omega (Omega × Omega) mOmega (m.prod mOmega)
      (fun omega => (id omega, id omega))) :
    @Measure.restrict (Omega × Omega) (m.prod mOmega)
        (@Measure.map Omega (Omega × Omega) mOmega (m.prod mOmega)
          (fun omega => (id omega, id omega)) mu) (s ×ˢ Set.univ) =
      @Measure.map Omega (Omega × Omega) mOmega (m.prod mOmega)
        (fun omega => (id omega, id omega))
        (@Measure.restrict Omega mOmega mu s) := by
  apply @Measure.ext (Omega × Omega) (m.prod mOmega)
  intro t ht
  rw [@Measure.restrict_apply (Omega × Omega) (m.prod mOmega) _
      (s ×ˢ Set.univ) t ht,
    @Measure.map_apply Omega (Omega × Omega) mOmega (m.prod mOmega) mu _ hf _
      (ht.inter (hs.prod MeasurableSet.univ)),
    @Measure.map_apply Omega (Omega × Omega) mOmega (m.prod mOmega)
      (@Measure.restrict Omega mOmega mu s) _ hf t ht,
    @Measure.restrict_apply Omega mOmega mu s _ (hf ht)]
  congr 1
  ext omega
  simp

theorem ts_trim_smul {Omega : Type*}
    {m mOmega : MeasurableSpace Omega}
    (mu : @Measure Omega mOmega) (hm : m ≤ mOmega) (a : ℝ≥0∞) :
    (a • mu).trim hm = a • (mu.trim hm) :=
  @Measure.ext _ m _ _ (fun s hs => by
    rw [Measure.smul_apply, trim_measurableSet_eq hm hs,
      trim_measurableSet_eq hm hs, Measure.smul_apply])




def IsTailSpecificationState (window : ℕ → Set E)
    (K : ∀ n, @Kernel (ConfigSpace E) (ConfigSpace E)
      (outsideSigma (window n)) inferInstance)
    (mu : Measure (ConfigSpace E)) [IsFiniteMeasure mu] : Prop :=
  ∀ n, (mu.trim (outsideSigma_le (window n))) ⊗ₘ K n =
    @Measure.map (ConfigSpace E) (ConfigSpace E × ConfigSpace E) _
      ((outsideSigma (window n)).prod inferInstance)
      (fun omega => (id omega, id omega)) mu

theorem ts_restrict_state
    {window : ℕ → Set E}
    {K : ∀ n, @Kernel (ConfigSpace E) (ConfigSpace E)
      (outsideSigma (window n)) inferInstance}
    [∀ n, IsSFiniteKernel (K n)]
    (mu : Measure (ConfigSpace E)) [IsFiniteMeasure mu]
    (hmu : IsTailSpecificationState window K mu)
    {s : Set (ConfigSpace E)} (hs : AtiTailEvent window s) (n : ℕ) :
    ((mu.restrict s).trim (outsideSigma_le (window n))) ⊗ₘ K n =
      @Measure.map (ConfigSpace E) (ConfigSpace E × ConfigSpace E) _
        ((outsideSigma (window n)).prod inferInstance)
        (fun omega => (id omega, id omega)) (mu.restrict s) := by
  set hm := outsideSigma_le (window n)
  have hsn : @MeasurableSet _ (outsideSigma (window n)) s := hs n
  have hf : @Measurable (ConfigSpace E) (ConfigSpace E × ConfigSpace E) _
      ((outsideSigma (window n)).prod inferInstance)
      (fun omega => (id omega, id omega)) :=
    (measurable_id'' hm).prodMk measurable_id
  rw [ts_trim_restrict_comm mu hm s hsn,
    ts_compProd_restrict_left _ (K n) s hsn, hmu n]
  exact ts_map_diag_restrict mu s hsn hf

theorem ts_smul_state
    {window : ℕ → Set E}
    {K : ∀ n, @Kernel (ConfigSpace E) (ConfigSpace E)
      (outsideSigma (window n)) inferInstance}
    [∀ n, IsSFiniteKernel (K n)]
    (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (mu : Measure (ConfigSpace E)) [IsFiniteMeasure mu]
    (hmu : IsTailSpecificationState window K mu) :
    haveI : IsFiniteMeasure (c • mu) := mu.smul_finite hc
    IsTailSpecificationState window K (c • mu) := by
  intro n
  have hf : @Measurable (ConfigSpace E) (ConfigSpace E × ConfigSpace E) _
      ((outsideSigma (window n)).prod inferInstance)
      (fun omega => (id omega, id omega)) :=
    (measurable_id'' (outsideSigma_le (window n))).prodMk measurable_id
  rw [ts_trim_smul mu (outsideSigma_le (window n)) c,
    Measure.compProd_smul_left, hmu n, Measure.map_smul]



theorem ts_cond_state
    {window : ℕ → Set E}
    {K : ∀ n, @Kernel (ConfigSpace E) (ConfigSpace E)
      (outsideSigma (window n)) inferInstance}
    [∀ n, IsSFiniteKernel (K n)]
    (mu : Measure (ConfigSpace E)) [IsFiniteMeasure mu]
    (hmu : IsTailSpecificationState window K mu)
    {s : Set (ConfigSpace E)} (hs : AtiTailEvent window s)
    (hs0 : mu s ≠ 0) :
    IsTailSpecificationState window K (mu[|s]) := by
  haveI : IsFiniteMeasure (mu.restrict s) := inferInstance
  have hc : (mu s)⁻¹ ≠ ⊤ := by
    simp only [ne_eq, ENNReal.inv_eq_top]
    exact hs0
  have hrestrict : IsTailSpecificationState window K (mu.restrict s) := by
    intro n
    exact ts_restrict_state mu hmu hs n
  have hscaled := ts_smul_state (mu s)⁻¹ hc (mu.restrict s) hrestrict
  exact hscaled

theorem ts_cond_congr {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) {s t : Set Omega} (h : s =ᵐ[mu] t) :
    (mu[|s]) = (mu[|t]) := by
  rw [ProbabilityTheory.cond, ProbabilityTheory.cond, measure_congr h,
    Measure.restrict_congr_set h]



theorem ts_cond_state_of_ae_tail
    {window : ℕ → Set E}
    {K : ∀ n, @Kernel (ConfigSpace E) (ConfigSpace E)
      (outsideSigma (window n)) inferInstance}
    [∀ n, IsSFiniteKernel (K n)]
    (mu : Measure (ConfigSpace E)) [IsFiniteMeasure mu]
    (hmu : IsTailSpecificationState window K mu)
    {s t : Set (ConfigSpace E)} (ht : AtiTailEvent window t)
    (hae : s =ᵐ[mu] t) (hs0 : mu s ≠ 0) :
    IsTailSpecificationState window K (mu[|s]) := by
  have hmass : mu t = mu s := (measure_congr hae).symm
  have ht0 : mu t ≠ 0 := by
    rw [hmass]
    exact hs0
  have hcond : (mu[|s]) = (mu[|t]) := ts_cond_congr mu hae
  have htail := ts_cond_state mu hmu ht ht0
  simpa only [hcond] using htail

def IsTailSpecificationMeasure (window : ℕ → Set E)
    (K : ∀ n, @Kernel (ConfigSpace E) (ConfigSpace E)
      (outsideSigma (window n)) inferInstance)
    (mu : Measure (ConfigSpace E)) : Prop :=
  ∃ _ : IsFiniteMeasure mu, IsTailSpecificationState window K mu





theorem ts_isErgodic_of_extreme
    {H : Type*} [Group H] [MulAction H E] [DecidableEq E]
    (window : ℕ → Set E) (hwindow : Monotone window)
    (hescape : ∀ (F : Finset E) (k : ℕ), ∃ g : H,
      (↑(F.image (fun e => g⁻¹ • e)) : Set E) ⊆ (window k)ᶜ)
    {K : ∀ n, @Kernel (ConfigSpace E) (ConfigSpace E)
      (outsideSigma (window n)) inferInstance}
    [∀ n, IsSFiniteKernel (K n)]
    {mu : Measure (ConfigSpace E)} [IsProbabilityMeasure mu]
    (hti : IsTranslationInvariant (G := H) mu)
    (hstate : IsTailSpecificationState window K mu)
    (hext : ∀ (nu₁ nu₂ : Measure (ConfigSpace E)) (a b : ℝ≥0∞),
      IsProbabilityMeasure nu₁ → IsProbabilityMeasure nu₂ →
      IsTailSpecificationMeasure window K nu₁ →
      IsTailSpecificationMeasure window K nu₂ →
      0 < a → 0 < b → a + b = 1 → a ≠ ⊤ → b ≠ ⊤ →
      mu = a • nu₁ + b • nu₂ → nu₁ = nu₂) :
    IsErgodic (G := H) mu := by
  refine ⟨hti, ?_⟩
  intro s hs hinv
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hs0, hsfull⟩ := hcon
  rw [measure_univ] at hsfull
  have hab : mu s + mu sᶜ = 1 := by
    calc
      mu s + mu sᶜ = mu Set.univ := measure_add_measure_compl hs
      _ = 1 := measure_univ
  have hsc0 : mu sᶜ ≠ 0 := fun hzero =>
    hsfull (by rw [hzero, add_zero] at hab; exact hab)
  have hinvc : ∀ g : H, shift g ⁻¹' sᶜ = sᶜ := fun g => by
    rw [Set.preimage_compl, hinv g]
  obtain ⟨t, ht, hst⟩ :=
    ati_invariant_aeTail window hwindow hescape hti s hs hinv
  obtain ⟨u, hu, hscu⟩ :=
    ati_invariant_aeTail window hwindow hescape hti sᶜ hs.compl hinvc
  haveI hp₁ : IsProbabilityMeasure (mu[|s]) := cond_isProbabilityMeasure hs0
  haveI hp₂ : IsProbabilityMeasure (mu[|sᶜ]) := cond_isProbabilityMeasure hsc0
  have hstate₁ : IsTailSpecificationState window K (mu[|s]) :=
    ts_cond_state_of_ae_tail mu hstate ht hst hs0
  have hstate₂ : IsTailSpecificationState window K (mu[|sᶜ]) :=
    ts_cond_state_of_ae_tail mu hstate hu hscu hsc0
  have hdecomp : mu = (mu s) • (mu[|s]) + (mu sᶜ) • (mu[|sᶜ]) := by
    have h₁ : (mu s) • (mu[|s]) = mu.restrict s := by
      rw [ProbabilityTheory.cond, smul_smul,
        ENNReal.mul_inv_cancel hs0 (measure_ne_top mu s), one_smul]
    have h₂ : (mu sᶜ) • (mu[|sᶜ]) = mu.restrict sᶜ := by
      rw [ProbabilityTheory.cond, smul_smul,
        ENNReal.mul_inv_cancel hsc0 (measure_ne_top mu sᶜ), one_smul]
    rw [h₁, h₂, Measure.restrict_add_restrict_compl hs]
  have heq : (mu[|s]) = (mu[|sᶜ]) :=
    hext (mu[|s]) (mu[|sᶜ]) (mu s) (mu sᶜ) hp₁ hp₂
      ⟨inferInstance, hstate₁⟩ ⟨inferInstance, hstate₂⟩
      (pos_iff_ne_zero.mpr hs0) (pos_iff_ne_zero.mpr hsc0) hab
      (measure_ne_top mu s) (measure_ne_top mu sᶜ) hdecomp
  have hval₁ : (mu[|s]) s = 1 :=
    cond_apply_self hs0 (measure_ne_top mu s)
  have hval₂ : (mu[|sᶜ]) s = 0 := by
    rw [cond_apply hs.compl, Set.inter_comm, Set.inter_compl_self,
      measure_empty, mul_zero]
  rw [heq, hval₂] at hval₁
  exact one_ne_zero hval₁.symm

end StatMech
