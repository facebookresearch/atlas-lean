/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

























































import Mathlib
import Code.Foundations.Ergodicity
import Code.FK.FKErgodicClose
import Code.FK.CrossBoxGeneralKeystone

open MeasureTheory Measure Set Filter
open scoped ENNReal

set_option linter.unusedSectionVars false

namespace StatMech

namespace ConfigSpace

variable {E : Type*} {G : Type*} [Group G] [MulAction G E]











theorem aeconst_of_ae_invariant
    {μ : Measure (ConfigSpace E)} [IsProbabilityMeasure μ] [Countable G]
    (hμ : IsErgodic (G := G) μ)
    {s : Set (ConfigSpace E)} (hs : MeasurableSet s)
    (hinv : ∀ g : G, (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' s =ᵐ[μ] s) :
    μ s = 0 ∨ μ s = 1 := by
  classical
  
  set u : Set (ConfigSpace E) := ⋂ g : G, (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' s with hu
  have humeas : MeasurableSet u := MeasurableSet.iInter (fun g => (measurable_shift g) hs)
  
  have huinv : ∀ h : G, (shift h : ConfigSpace E → ConfigSpace E) ⁻¹' u = u := by
    intro h
    rw [hu, preimage_iInter]
    have key : ∀ g : G, (shift h) ⁻¹' ((shift g) ⁻¹' s) = (shift (g * h)) ⁻¹' s := by
      intro g; rw [shift_mul]; rfl
    calc ⋂ g, (shift h) ⁻¹' ((shift g) ⁻¹' s)
        = ⋂ g, (shift (g * h)) ⁻¹' s := iInter_congr key
      _ = ⋂ g, (shift g) ⁻¹' s :=
            iInter_congr_of_surjective (f := fun g => (shift (g * h)) ⁻¹' s)
              (g := fun g => (shift g) ⁻¹' s) (· * h) (mul_right_surjective h) (fun g => rfl)
  
  have huae : u =ᵐ[μ] s := by
    have h1 : u =ᵐ[μ] ⋂ g : G, s :=
      Filter.EventuallyEq.countable_iInter (fun g => hinv g)
    refine h1.trans ?_
    rw [iInter_const]
  rcases hμ.2 u humeas huinv with h0 | h1
  · left; rwa [measure_congr huae] at h0
  · right; rw [measure_congr huae, measure_univ] at h1; exact h1








theorem ae_eq_const_of_ae_invariant_function
    {μ : Measure (ConfigSpace E)} [IsProbabilityMeasure μ] [Countable G]
    (hμ : IsErgodic (G := G) μ)
    {φ : ConfigSpace E → ℝ≥0∞} (hφ : Measurable φ)
    (hinv : ∀ g : G, φ ∘ (shift g : ConfigSpace E → ConfigSpace E) =ᵐ[μ] φ) :
    ∃ c : ℝ≥0∞, φ =ᵐ[μ] Function.const _ c := by
  apply Filter.exists_eventuallyEq_const_of_forall_separating (p := MeasurableSet)
  intro U hU
  have hpre : MeasurableSet (φ ⁻¹' U) := hφ hU
  have hinvU : ∀ g : G, (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' (φ ⁻¹' U) =ᵐ[μ] φ ⁻¹' U := by
    intro g
    rw [← Set.preimage_comp]
    exact (hinv g).preimage U
  rcases aeconst_of_ae_invariant hμ hpre hinvU with h0 | h1
  · refine .inr ?_
    rw [ae_iff]; simpa using h0
  · refine .inl ?_
    rw [Filter.eventually_iff, mem_ae_iff]
    have : μ (φ ⁻¹' U)ᶜ = 0 := by
      rw [measure_compl hpre (measure_ne_top _ _), h1, measure_univ, tsub_self]
    simpa using this








theorem eq_smul_of_absolutelyContinuous
    {μ ν : Measure (ConfigSpace E)} [IsProbabilityMeasure μ] [IsFiniteMeasure ν] [Countable G]
    (hμ : IsErgodic (G := G) μ)
    (hν : IsTranslationInvariant (G := G) ν) (hνμ : ν ≪ μ) :
    ∃ c : ℝ≥0∞, ν = c • μ := by
  have hcomp : ∀ g : G,
      ν.rnDeriv μ ∘ (shift g : ConfigSpace E → ConfigSpace E) =ᵐ[μ] ν.rnDeriv μ :=
    fun g => MeasureTheory.MeasurePreserving.rnDeriv_comp_aeEq (hν g) (hμ.1 g)
  obtain ⟨c, hc⟩ := ae_eq_const_of_ae_invariant_function hμ (measurable_rnDeriv ν μ) hcomp
  refine ⟨c, ?_⟩
  ext s hs
  calc
    ν s = ∫⁻ a in s, ν.rnDeriv μ a ∂μ := (setLIntegral_rnDeriv hνμ _).symm
    _ = ∫⁻ _ in s, c ∂μ := lintegral_congr_ae <| hc.filter_mono <| ae_mono restrict_le_self
    _ = (c • μ) s := by simp










theorem eeu_ergodic_summand_eq
    {μ ν₁ ν₂ : Measure (ConfigSpace E)} {a b : ℝ≥0∞}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν₁] [Countable G]
    (hμ : IsErgodic (G := G) μ) (hν₁ : IsTranslationInvariant (G := G) ν₁)
    (hconv : μ = a • ν₁ + b • ν₂) (ha : 0 < a) :
    ν₁ = μ := by
  have hle : a • ν₁ ≤ μ := by rw [hconv]; exact Measure.le_add_right le_rfl
  have hνμ : ν₁ ≪ μ :=
    (Measure.absolutelyContinuous_smul ha.ne').trans (Measure.absolutelyContinuous_of_le hle)
  obtain ⟨c, hc⟩ := eq_smul_of_absolutelyContinuous hμ hν₁ hνμ
  have h1 : ν₁ Set.univ = c • μ Set.univ := by rw [← Measure.smul_apply, ← hc]
  simp only [measure_univ, smul_eq_mul, mul_one] at h1
  rw [hc, ← h1, one_smul]




theorem eeu_ergodic_summands_eq
    {μ ν₁ ν₂ : Measure (ConfigSpace E)} {a b : ℝ≥0∞}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] [Countable G]
    (hμ : IsErgodic (G := G) μ)
    (hν₁ : IsTranslationInvariant (G := G) ν₁) (hν₂ : IsTranslationInvariant (G := G) ν₂)
    (hconv : μ = a • ν₁ + b • ν₂) (ha : 0 < a) (hb : 0 < b) :
    ν₁ = μ ∧ ν₂ = μ := by
  refine ⟨eeu_ergodic_summand_eq hμ hν₁ hconv ha, ?_⟩
  refine eeu_ergodic_summand_eq (a := b) (b := a) (ν₁ := ν₂) (ν₂ := ν₁) hμ hν₂ ?_ hb
  rw [hconv, add_comm]

end ConfigSpace

namespace FK

open ConfigSpace

variable {E : Type*} {G : Type*} [Group G] [MulAction G E]












theorem eeu_isInvariantExtremePoint_of_ergodic [Countable G]
    {μ : Measure (ConfigSpace E)} (hμ : IsErgodic (G := G) μ) [IsProbabilityMeasure μ] :
    IsInvariantExtremePoint (G := G) μ := by
  refine ⟨hμ.1, inferInstance, ?_⟩
  intro ν₁ ν₂ a b hν₁ hν₂ hp1 hp2 ha hb _ hconv
  obtain ⟨e1, e2⟩ := ConfigSpace.eeu_ergodic_summands_eq hμ hν₁ hν₂ hconv ha hb
  rw [e1, e2]
















theorem eeu_wiredIV_isInvariantExtremePoint {d : ℕ} (hd : 1 ≤ d) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    IsInvariantExtremePoint (G := Multiplicative (Lattice.Site d))
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Lattice.Site d)))) :=
  haveI : Countable (Multiplicative (Lattice.Site d)) :=
    inferInstanceAs (Countable (Lattice.Site d))
  eeu_isInvariantExtremePoint_of_ergodic (cbk_wiredIV_isErgodic hd hp hp1)





theorem eeu_wiredIV_extremePoint_clause {d : ℕ} (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ν₁ ν₂ : Measure (ConfigSpace (Sym2 (Lattice.Site d)))) (a b : ℝ≥0∞)
    (h1 : IsTranslationInvariant (G := Multiplicative (Lattice.Site d)) ν₁)
    (h2 : IsTranslationInvariant (G := Multiplicative (Lattice.Site d)) ν₂)
    (hp1' : IsProbabilityMeasure ν₁) (hp2' : IsProbabilityMeasure ν₂)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (hconv : (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Lattice.Site d)))) = a • ν₁ + b • ν₂) :
    ν₁ = ν₂ :=
  (eeu_wiredIV_isInvariantExtremePoint hd hp hp1).2.2 ν₁ ν₂ a b h1 h2 hp1' hp2' ha hb hab hconv

end FK

end StatMech
