/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.DecoupledForestCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorCoverRouting
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BernoulliErgodicFiniteEnergy
public import MathlibExt.Probability.Percolation.BurtonKeane.FiniteModification

/-!
# Burton–Keane uniqueness from encounter points

Encounter points have probability zero for every translation-invariant measure in `d ≥ 1`; with the
encounter-point step, ergodicity and finite energy for merges give uniqueness of the infinite
cluster.

## i. Overview

Every translation-invariant probability measure in `d ≥ 1` gives probability zero to an encounter
point at the origin (`measure_encounter_eq_zero`). With the encounter-point step
`0 < μ(N = ⊤) → 0 < μ(encounter point at 0)`, `N ≠ ⊤` almost surely, and the merge argument gives
the Burton–Keane conclusion (`cbk_canonical_uniqueness`).

**Fidelity.** `cbk_canonical_uniqueness` is conditional on the encounter-point step `htrif`; the
probability-zero step is proved with no further hypothesis.

## ii. Key results

- `cbk_canonical_uniqueness` : uniqueness from the encounter-point step.

## iii. Table of contents

- A. Uniqueness

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
- G. Grimmett, *Percolation*, 2nd ed., Springer (1999), Section 8.2.
-/

@[expose] public section

namespace StatMech.Percolation

open StatMech StatMech.ConfigSpace MeasureTheory SimpleGraph Finset Filter Topology
open StatMech.Lattice
open scoped ENNReal
open MathlibExt.Probability.Percolation.BurtonKeaneWanted
  (IsEncounterPoint measure_encounter_eq_zero exists_mergeWitness_pos)

variable {d : ℕ}

/-! ## A. Uniqueness -/

lemma cbk_numInfiniteClusters_ne_top (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] (hd : 1 ≤ d)
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (htrif : 0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      0 < μ {ω | IsEncounterPoint d ω 0}) :
    ∃ k : ℕ∞, k ≠ ⊤ ∧ μ {ω | numInfiniteClusters d ω = k} = 1 := by
  have htri0 : μ {ω | IsEncounterPoint d ω 0} = 0 :=
    measure_encounter_eq_zero μ hd herg.isTranslationInvariant
  have htop0 : μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
    by_contra h
    have hpos : 0 < μ {ω | numInfiniteClusters d ω = ⊤} := pos_iff_ne_zero.mpr h
    have := htrif hpos
    rw [htri0] at this
    exact (lt_irrefl 0) this
  obtain ⟨k, hk⟩ := numInfiniteClusters_ae_const μ herg
  refine ⟨k, ?_, hk⟩
  intro hktop
  rw [hktop] at hk
  rw [hk] at htop0
  exact one_ne_zero htop0

/-- **Burton–Keane uniqueness via encounter points.** For an ergodic measure with finite energy for
merges in `d ≥ 1`, if infinitely many infinite clusters with positive probability give an encounter
point at the origin with positive probability, then a.s. `N ∈ {0, 1}`. Burton and Keane, *Density
and uniqueness in percolation* (1989). -/
lemma cbk_canonical_uniqueness (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] (hd : 1 ≤ d)
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (htrif : 0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      0 < μ {ω | IsEncounterPoint d ω 0}) :
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ μ (atLeastTwoInfinite d) = 0
      ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
  have hkne_top : ∀ k : ℕ∞, μ {ω | numInfiniteClusters d ω = k} = 1 → k ≠ ⊤ := by
    intro k hk
    obtain ⟨k', hk'top, hk'⟩ := cbk_numInfiniteClusters_ne_top μ hd herg htrif
    intro hktop
    have hsub : {ω | numInfiniteClusters d ω = k} ⊆ {ω | numInfiniteClusters d ω = k'}ᶜ := by
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, hω]
      intro h; exact hk'top (by rw [← h, hktop])
    have hmk' : MeasurableSet
        {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω = k'} := by
      have heq : {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω = k'}
          = numInfiniteClusters d ⁻¹' {k'} := by ext ω; simp [Set.mem_preimage]
      rw [heq]; exact measurable_numInfiniteClusters (MeasurableSet.of_discrete)
    have hfull : μ {ω | numInfiniteClusters d ω = k'}ᶜ = 1 :=
      le_antisymm prob_le_one (hk ▸ measure_mono hsub)
    have hnull : μ {ω | numInfiniteClusters d ω = k'} = 0 :=
      (prob_compl_eq_one_iff hmk').mp hfull
    rw [hk'] at hnull
    exact one_ne_zero hnull
  have hmerge : μ (atLeastTwoInfinite d) = 0 :=
    merge_event_null μ herg hfe hkne_top
      (fun k hk2 _ hk => exists_mergeWitness_pos μ k hk2 hk)
  refine ⟨numInfiniteClusters_zero_or_one μ herg hmerge, hmerge,
    infiniteCluster_unique_ae μ herg hmerge⟩

end StatMech.Percolation
