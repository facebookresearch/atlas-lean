/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import PhyslibExt.StatisticalMechanics.RandomCluster.Ergodicity
public import PhyslibExt.StatisticalMechanics.RandomCluster.DlrSandwich
public import PhyslibExt.StatisticalMechanics.RandomCluster.IvProperties
public import PhyslibExt.StatisticalMechanics.RandomCluster.Uniqueness

/-!
# Ergodic measures and their convex summands

Abstract facts about measures on a configuration space that are ergodic under a group action: they
are trivial on invariant events, and any two summands of a convex decomposition agree on invariant
events.

## i. Overview

Translation-invariant random-cluster measures are studied through their ergodic components. If an
ergodic probability measure `μ` is written as `a • ν₁ + b • ν₂` with `a, b > 0`, the 0–1 law for
invariant events forces `ν₁` and `ν₂` to agree with `μ` on every invariant event. This file proves
that statement and a parametrized version for a family `p ↦ φ p` of measures that are ergodic
outside a countable set of parameters. `ergodic_summands_eq_on_invariants` is proved
unconditionally: its ergodicity hypothesis is the subject of the statement.
`extreme_on_invariants_off_countable` is conditional on the input `herg` (ergodicity of `φ p` for
every `p` outside the countable set `S`), which callers must supply.

## ii. Key results

- `ergodic_invariant_event_zero_or_one` : an ergodic measure gives invariant events mass `0` or `1`.
- `ergodic_summands_eq_on_invariants` : convex summands of an ergodic measure agree on invariant
  events.
- `extreme_on_invariants_off_countable` : the same for a family ergodic off a countable set.

## iii. Table of contents

- A. The 0–1 law for invariant events
- B. Convex decompositions of ergodic measures
- C. Families of measures ergodic off a countable set

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Chapter 4.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

set_option linter.unusedSectionVars false

namespace StatMech

namespace FK

open ConfigSpace

variable {E : Type*} {G : Type*} [Group G] [MulAction G E]

/-! ## A. The 0–1 law for invariant events -/

/-- An ergodic probability measure gives every invariant measurable event mass `0` or `1`. -/
lemma ergodic_invariant_event_zero_or_one {μ : Measure (ConfigSpace E)}
    [IsProbabilityMeasure μ] (hμ : IsErgodic (G := G) μ)
    {s : Set (ConfigSpace E)} (hs : MeasurableSet s)
    (hinv : ∀ g : G, (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' s = s) :
    μ s = 0 ∨ μ s = 1 := by
  have := hμ.2 s hs hinv
  rwa [measure_univ] at this

lemma ergodic_invariant_event_eq_one_of_pos {μ : Measure (ConfigSpace E)}
    [IsProbabilityMeasure μ] (hμ : IsErgodic (G := G) μ)
    {s : Set (ConfigSpace E)} (hs : MeasurableSet s)
    (hinv : ∀ g : G, (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' s = s)
    (hpos : 0 < μ s) : μ s = 1 :=
  (ergodic_invariant_event_zero_or_one hμ hs hinv).resolve_left hpos.ne'

/-! ## B. Convex decompositions of ergodic measures -/

lemma le_self_of_convexCombo {μ ν₁ ν₂ : Measure (ConfigSpace E)} {a b : ℝ≥0∞}
    (hconv : μ = a • ν₁ + b • ν₂) (s : Set (ConfigSpace E)) :
    a * ν₁ s ≤ μ s ∧ b * ν₂ s ≤ μ s := by
  constructor
  · rw [hconv]; simp [Measure.add_apply, Measure.smul_apply]
  · rw [hconv]; simp [Measure.add_apply, Measure.smul_apply]

lemma convexSummand_eq_on_invariants {μ ν₁ ν₂ : Measure (ConfigSpace E)} {a b : ℝ≥0∞}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν₁]
    (hμ : IsErgodic (G := G) μ) (hconv : μ = a • ν₁ + b • ν₂) (ha : 0 < a)
    {s : Set (ConfigSpace E)} (hs : MeasurableSet s)
    (hinv : ∀ g : G, (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' s = s) :
    ν₁ s = μ s := by
  rcases ergodic_invariant_event_zero_or_one hμ hs hinv with h0 | h1
  · have hle := (le_self_of_convexCombo hconv s).1
    rw [h0] at hle ⊢
    have : a * ν₁ s = 0 := le_antisymm hle (by positivity)
    exact (mul_eq_zero.mp this).resolve_left ha.ne'
  · have hinvc : ∀ g : G, (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' sᶜ = sᶜ := fun g => by
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

lemma ergodic_eq_on_invariants_of_convexCombo {μ ν₁ ν₂ : Measure (ConfigSpace E)}
    {a b : ℝ≥0∞}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (hμ : IsErgodic (G := G) μ) (hconv : μ = a • ν₁ + b • ν₂) (ha : 0 < a) (hb : 0 < b)
    {s : Set (ConfigSpace E)} (hs : MeasurableSet s)
    (hinv : ∀ g : G, (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' s = s) :
    ν₁ s = μ s ∧ ν₂ s = μ s := by
  refine ⟨convexSummand_eq_on_invariants hμ hconv ha hs hinv, ?_⟩
  refine convexSummand_eq_on_invariants hμ (a := b) (b := a) (ν₁ := ν₂) (ν₂ := ν₁) ?_ hb hs hinv
  rw [hconv, add_comm]

/-- If an ergodic probability measure is a convex combination `a • ν₁ + b • ν₂` with
`a, b > 0` of probability measures, then `ν₁` and `ν₂` agree on every invariant event. -/
theorem ergodic_summands_eq_on_invariants {μ ν₁ ν₂ : Measure (ConfigSpace E)} {a b : ℝ≥0∞}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (hμ : IsErgodic (G := G) μ) (hconv : μ = a • ν₁ + b • ν₂) (ha : 0 < a) (hb : 0 < b)
    {s : Set (ConfigSpace E)} (hs : MeasurableSet s)
    (hinv : ∀ g : G, (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' s = s) :
    ν₁ s = ν₂ s := by
  obtain ⟨h1, h2⟩ := ergodic_eq_on_invariants_of_convexCombo hμ hconv ha hb hs hinv
  rw [h1, h2]

lemma ergodic_invariant_event_zero_or_one_pair {μ ν : Measure (ConfigSpace E)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsErgodic (G := G) μ) (hν : IsErgodic (G := G) ν)
    {s : Set (ConfigSpace E)} (hs : MeasurableSet s)
    (hinv : ∀ g : G, (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' s = s) :
    (μ s = 0 ∨ μ s = 1) ∧ (ν s = 0 ∨ ν s = 1) :=
  ⟨ergodic_invariant_event_zero_or_one hμ hs hinv,
   ergodic_invariant_event_zero_or_one hν hs hinv⟩

/-! ## C. Families of measures ergodic off a countable set -/

lemma ergodic_off_countable {φ : ℝ → Measure (ConfigSpace E)} {S : Set ℝ} (hS : S.Countable)
    (herg : ∀ p ∉ S, IsErgodic (G := G) (φ p)) :
    {p : ℝ | ¬ IsErgodic (G := G) (φ p)}.Countable := by
  refine hS.mono ?_
  intro p hp
  by_contra hpS
  exact hp (herg p hpS)

/-- For a family `φ` of probability measures ergodic outside a set `S`, at every `p ∉ S`
the two summands of any strictly positive convex decomposition of `φ p` agree on invariant
events. -/
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
  have := hpm p
  exact ergodic_summands_eq_on_invariants (herg p hp) hconv ha hb hs hinv

end FK

end StatMech
