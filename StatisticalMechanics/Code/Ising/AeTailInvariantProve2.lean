/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









































import Mathlib
import Code.Ising.AeTailInvariantClose
import Code.Ising.GibbsExtremeClose
import Code.Percolation.BurtonKeane

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology
open scoped BigOperators ENNReal StatMech

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}













theorem atip2_plusState_invariant_zeroOne (β h : ℝ) (hd : 1 ≤ d) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (hti : IsTranslationInvariant (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d))))
    (hdlr : IsDLRState d β h (plusState d β h : Measure (ConfigSpace (Site d))))
    {s : Set (ConfigSpace (Site d))} (hs : MeasurableSet s)
    (hinv : ∀ g : Multiplicative (Site d),
      (shift g : ConfigSpace (Site d) → ConfigSpace (Site d)) ⁻¹' s = s) :
    (plusState d β h : Measure (ConfigSpace (Site d))) s = 0
      ∨ (plusState d β h : Measure (ConfigSpace (Site d))) s = 1 := by
  have herg := aetc_plusState_isErgodic β h hd hβ hh hti hdlr
  rcases herg.2 s hs hinv with hz | hf
  · exact Or.inl hz
  · exact Or.inr (by rwa [measure_univ] at hf)


theorem atip2_minusState_invariant_zeroOne (β h : ℝ) (hd : 1 ≤ d) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (hti : IsTranslationInvariant (G := Multiplicative (Site d))
      (minusState d β h : Measure (ConfigSpace (Site d))))
    (hdlr : IsDLRState d β h (minusState d β h : Measure (ConfigSpace (Site d))))
    {s : Set (ConfigSpace (Site d))} (hs : MeasurableSet s)
    (hinv : ∀ g : Multiplicative (Site d),
      (shift g : ConfigSpace (Site d) → ConfigSpace (Site d)) ⁻¹' s = s) :
    (minusState d β h : Measure (ConfigSpace (Site d))) s = 0
      ∨ (minusState d β h : Measure (ConfigSpace (Site d))) s = 1 := by
  have herg := aetc_minusState_isErgodic β h hd hβ hh hti hdlr
  rcases herg.2 s hs hinv with hz | hf
  · exact Or.inl hz
  · exact Or.inr (by rwa [measure_univ] at hf)












theorem atip2_plusState_ae_const (β h : ℝ) (hd : 1 ≤ d) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (hti : IsTranslationInvariant (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d))))
    (hdlr : IsDLRState d β h (plusState d β h : Measure (ConfigSpace (Site d))))
    {β' : Type*} [Countable β'] [MeasurableSpace β'] [MeasurableSingletonClass β']
    (f : ConfigSpace (Site d) → β') (hf : Measurable f)
    (hinv : ∀ (g : Multiplicative (Site d)) (ω : ConfigSpace (Site d)), f (shift g ω) = f ω) :
    ∃ k : β', (plusState d β h : Measure (ConfigSpace (Site d))) {ω | f ω = k} = 1 :=
  ConfigSpace.ergodic_ae_const_of_shiftInvariant
    (aetc_plusState_isErgodic β h hd hβ hh hti hdlr) f hf hinv



theorem atip2_minusState_ae_const (β h : ℝ) (hd : 1 ≤ d) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (hti : IsTranslationInvariant (G := Multiplicative (Site d))
      (minusState d β h : Measure (ConfigSpace (Site d))))
    (hdlr : IsDLRState d β h (minusState d β h : Measure (ConfigSpace (Site d))))
    {β' : Type*} [Countable β'] [MeasurableSpace β'] [MeasurableSingletonClass β']
    (f : ConfigSpace (Site d) → β') (hf : Measurable f)
    (hinv : ∀ (g : Multiplicative (Site d)) (ω : ConfigSpace (Site d)), f (shift g ω) = f ω) :
    ∃ k : β', (minusState d β h : Measure (ConfigSpace (Site d))) {ω | f ω = k} = 1 :=
  ConfigSpace.ergodic_ae_const_of_shiftInvariant
    (aetc_minusState_isErgodic β h hd hβ hh hti hdlr) f hf hinv













def IsDLRExtremePoint (β h : ℝ) (μ : Measure (ConfigSpace (Site d))) : Prop :=
  ∀ (ν₁ ν₂ : Measure (ConfigSpace (Site d))) [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂],
    IsDLRState d β h ν₁ → IsDLRState d β h ν₂ →
    ∀ (a b : ℝ≥0∞), 0 < a → 0 < b → a + b = 1 → a ≠ ⊤ → b ≠ ⊤ →
      μ = a • ν₁ + b • ν₂ → ν₁ = ν₂



theorem atip2_plusState_isDLRExtremePoint (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) :
    IsDLRExtremePoint β h (plusState d β h : Measure (ConfigSpace (Site d))) := by
  intro ν₁ ν₂ _ _ h₁ h₂ a b ha hb hab hat hbt hconv
  exact gec_plusState_no_proper_split β h hβ hh h₁ h₂ ha hb hab hat hbt hconv



theorem atip2_minusState_isDLRExtremePoint (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) :
    IsDLRExtremePoint β h (minusState d β h : Measure (ConfigSpace (Site d))) := by
  intro ν₁ ν₂ _ _ h₁ h₂ a b ha hb hab hat hbt hconv
  exact gec_minusState_no_proper_split β h hβ hh h₁ h₂ ha hb hab hat hbt hconv















theorem atip2_plusState_isErgodic_extremePoint (β h : ℝ) (hd : 1 ≤ d) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (hti : IsTranslationInvariant (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d))))
    (hdlr : IsDLRState d β h (plusState d β h : Measure (ConfigSpace (Site d)))) :
    IsErgodic (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d)))
      ∧ IsDLRExtremePoint β h (plusState d β h : Measure (ConfigSpace (Site d))) :=
  ⟨aetc_plusState_isErgodic β h hd hβ hh hti hdlr,
   atip2_plusState_isDLRExtremePoint β h hβ hh⟩



theorem atip2_minusState_isErgodic_extremePoint (β h : ℝ) (hd : 1 ≤ d) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (hti : IsTranslationInvariant (G := Multiplicative (Site d))
      (minusState d β h : Measure (ConfigSpace (Site d))))
    (hdlr : IsDLRState d β h (minusState d β h : Measure (ConfigSpace (Site d)))) :
    IsErgodic (G := Multiplicative (Site d)) (minusState d β h : Measure (ConfigSpace (Site d)))
      ∧ IsDLRExtremePoint β h (minusState d β h : Measure (ConfigSpace (Site d))) :=
  ⟨aetc_minusState_isErgodic β h hd hβ hh hti hdlr,
   atip2_minusState_isDLRExtremePoint β h hβ hh⟩













theorem atip2_dirac_const_isErgodic :
    IsErgodic (G := Multiplicative (Site d))
      (Measure.dirac (fun _ => true) : Measure (ConfigSpace (Site d))) := by
  refine ⟨aetc_dirac_const_isTranslationInvariant, ?_⟩
  intro s hs _
  rw [Measure.dirac_apply' _ hs, measure_univ]
  by_cases hmem : (fun _ => true : ConfigSpace (Site d)) ∈ s
  · right; simp [Set.indicator_of_mem hmem]
  · left; simp [Set.indicator_of_notMem hmem]






theorem atip2_ergodic_zeroOne_nonvacuous :
    (Measure.dirac (fun _ => true) : Measure (ConfigSpace (Site 1)))
        {ω : ConfigSpace (Site 1) | ∀ e, ω e = true} = 1 := by
  
  have herg := atip2_dirac_const_isErgodic (d := 1)
  have hmeas : MeasurableSet {ω : ConfigSpace (Site 1) | ∀ e, ω e = true} := by
    have hrw : {ω : ConfigSpace (Site 1) | ∀ e, ω e = true} = ⋂ e, {ω | ω e = true} := by
      ext ω; simp [Set.mem_iInter]
    rw [hrw]
    exact MeasurableSet.iInter fun e =>
      (ConfigSpace.measurable_eval e) (measurableSet_singleton true)
  have hinv : ∀ g : Multiplicative (Site 1),
      (shift g : ConfigSpace (Site 1) → ConfigSpace (Site 1)) ⁻¹'
        {ω | ∀ e, ω e = true} = {ω | ∀ e, ω e = true} := by
    intro g
    ext ω
    simp only [Set.mem_preimage, Set.mem_setOf_eq, shift]
    exact ⟨fun hf e => by simpa using hf (g • e), fun hf e => hf _⟩
  rcases herg.2 _ hmeas hinv with hz | hf
  · 
    exfalso
    rw [Measure.dirac_apply' _ hmeas, Set.indicator_of_mem (by intro e; rfl)] at hz
    exact one_ne_zero hz
  · rwa [measure_univ] at hf

end Ising

end StatMech
