/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











































































import Mathlib
import Code.FK.Ergodicity
import Code.FK.DlrSandwich
import Code.FK.IvProperties
import Code.FK.Uniqueness

open MeasureTheory Set
open scoped ENNReal

set_option linter.unusedSectionVars false

namespace StatMech

namespace FK

open ConfigSpace

variable {E : Type*} {G : Type*} [Group G] [MulAction G E]










theorem ergodic_invariant_event_zero_or_one {μ : Measure (ConfigSpace E)}
    [IsProbabilityMeasure μ] (hμ : IsErgodic (G := G) μ)
    {s : Set (ConfigSpace E)} (hs : MeasurableSet s)
    (hinv : ∀ g : G, (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' s = s) :
    μ s = 0 ∨ μ s = 1 := by
  have := hμ.2 s hs hinv
  rwa [measure_univ] at this



theorem ergodic_invariant_event_eq_one_of_pos {μ : Measure (ConfigSpace E)}
    [IsProbabilityMeasure μ] (hμ : IsErgodic (G := G) μ)
    {s : Set (ConfigSpace E)} (hs : MeasurableSet s)
    (hinv : ∀ g : G, (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' s = s)
    (hpos : 0 < μ s) : μ s = 1 :=
  (ergodic_invariant_event_zero_or_one hμ hs hinv).resolve_left hpos.ne'








theorem le_self_of_convexCombo {μ ν₁ ν₂ : Measure (ConfigSpace E)} {a b : ℝ≥0∞}
    (hconv : μ = a • ν₁ + b • ν₂) (s : Set (ConfigSpace E)) :
    a * ν₁ s ≤ μ s ∧ b * ν₂ s ≤ μ s := by
  constructor
  · rw [hconv]; simp [Measure.add_apply, Measure.smul_apply]
  · rw [hconv]; simp [Measure.add_apply, Measure.smul_apply]














theorem convexSummand_eq_on_invariants {μ ν₁ ν₂ : Measure (ConfigSpace E)} {a b : ℝ≥0∞}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν₁]
    (hμ : IsErgodic (G := G) μ) (hconv : μ = a • ν₁ + b • ν₂) (ha : 0 < a)
    {s : Set (ConfigSpace E)} (hs : MeasurableSet s)
    (hinv : ∀ g : G, (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' s = s) :
    ν₁ s = μ s := by
  rcases ergodic_invariant_event_zero_or_one hμ hs hinv with h0 | h1
  · 
    have hle := (le_self_of_convexCombo hconv s).1
    rw [h0] at hle ⊢
    have : a * ν₁ s = 0 := le_antisymm hle (by positivity)
    exact (mul_eq_zero.mp this).resolve_left ha.ne'
  · 
    have hinvc : ∀ g : G, (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' sᶜ = sᶜ := fun g => by
      rw [Set.preimage_compl, hinv g]
    have hmsc : μ sᶜ = 0 := by
      rw [measure_compl hs (measure_ne_top μ s), h1, measure_univ]; simp
    have hlec := (le_self_of_convexCombo hconv sᶜ).1
    rw [hmsc] at hlec
    have h0c : a * ν₁ sᶜ = 0 := le_antisymm hlec (by positivity)
    have hν1sc : ν₁ sᶜ = 0 := (mul_eq_zero.mp h0c).resolve_left ha.ne'
    have : ν₁ s = 1 := by
      rw [← measure_univ (μ := ν₁), ← Set.union_compl_self s,
        measure_union disjoint_compl_right hs.compl, hν1sc, add_zero]
    rw [this, h1]











theorem ergodic_eq_on_invariants_of_convexCombo {μ ν₁ ν₂ : Measure (ConfigSpace E)} {a b : ℝ≥0∞}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (hμ : IsErgodic (G := G) μ) (hconv : μ = a • ν₁ + b • ν₂) (ha : 0 < a) (hb : 0 < b)
    {s : Set (ConfigSpace E)} (hs : MeasurableSet s)
    (hinv : ∀ g : G, (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' s = s) :
    ν₁ s = μ s ∧ ν₂ s = μ s := by
  refine ⟨convexSummand_eq_on_invariants hμ hconv ha hs hinv, ?_⟩
  
  refine convexSummand_eq_on_invariants hμ (a := b) (b := a) (ν₁ := ν₂) (ν₂ := ν₁) ?_ hb hs hinv
  rw [hconv, add_comm]









theorem ergodic_summands_eq_on_invariants {μ ν₁ ν₂ : Measure (ConfigSpace E)} {a b : ℝ≥0∞}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (hμ : IsErgodic (G := G) μ) (hconv : μ = a • ν₁ + b • ν₂) (ha : 0 < a) (hb : 0 < b)
    {s : Set (ConfigSpace E)} (hs : MeasurableSet s)
    (hinv : ∀ g : G, (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' s = s) :
    ν₁ s = ν₂ s := by
  obtain ⟨h1, h2⟩ := ergodic_eq_on_invariants_of_convexCombo hμ hconv ha hb hs hinv
  rw [h1, h2]








theorem ergodic_invariant_event_zero_or_one_pair {μ ν : Measure (ConfigSpace E)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsErgodic (G := G) μ) (hν : IsErgodic (G := G) ν)
    {s : Set (ConfigSpace E)} (hs : MeasurableSet s)
    (hinv : ∀ g : G, (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' s = s) :
    (μ s = 0 ∨ μ s = 1) ∧ (ν s = 0 ∨ ν s = 1) :=
  ⟨ergodic_invariant_event_zero_or_one hμ hs hinv,
   ergodic_invariant_event_zero_or_one hν hs hinv⟩















theorem ergodic_off_countable {φ : ℝ → Measure (ConfigSpace E)} {S : Set ℝ} (hS : S.Countable)
    (herg : ∀ p ∉ S, IsErgodic (G := G) (φ p)) :
    {p : ℝ | ¬ IsErgodic (G := G) (φ p)}.Countable := by
  refine hS.mono ?_
  intro p hp
  by_contra hpS
  exact hp (herg p hpS)








theorem extreme_on_invariants_off_countable {φ : ℝ → Measure (ConfigSpace E)} {S : Set ℝ}
    (hpm : ∀ p, IsProbabilityMeasure (φ p))
    (herg : ∀ p ∉ S, IsErgodic (G := G) (φ p)) :
    ∀ p ∉ S, ∀ (ν₁ ν₂ : Measure (ConfigSpace E)) (a b : ℝ≥0∞),
      IsProbabilityMeasure ν₁ → IsProbabilityMeasure ν₂ →
        φ p = a • ν₁ + b • ν₂ → 0 < a → 0 < b →
          ∀ {s : Set (ConfigSpace E)}, MeasurableSet s →
            (∀ g : G, (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' s = s) →
              ν₁ s = ν₂ s := by
  intro p hp ν₁ ν₂ a b h1 h2 hconv ha hb s hs hinv
  haveI := hpm p
  exact ergodic_summands_eq_on_invariants (herg p hp) hconv ha hb hs hinv

end FK

end StatMech
