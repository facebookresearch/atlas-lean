/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Order.Filter.AtTopBot.Defs
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.DistinctCutClusters
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.DisjointCutNoCrossing
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CutLeavesInfinite
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CanonicalTrifCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorCoverRouting

/-!
# Canonical trifurcations by rewiring at the origin

Three open neighbours of the origin in distinct infinite clusters without it make a canonical
trifurcation; origin rewiring in every box gives corridor covers, the route and the Burton–Keane
conclusion.

## i. Overview

Three distinct open neighbours of the origin with infinite, pairwise distinct clusters in
`removeSite 0 ω` form a canonical trifurcation at the origin. `bc8_OriginRewiring d n` asks that
every configuration of `threeMeetBox d n` become such a configuration after forcing a finite set of
edges avoiding the origin. It gives corridor covers of `threeMeetBox`, the route for measures with
finite energy, and the Burton–Keane conclusion. Three non-crossing arms give a canonical
trifurcation.

**Fidelity.** `bc8_burtonKeane_uniqueness_of_originRewiring` also assumes the counting hypotheses of
`burton_keane_uniqueness_full`, which are unsatisfiable for `d ≥ 1` (`tfc_not_hbound_hdens`), so it
has content only for `d = 0`.

## ii. Key results

- `bc8_isCanonicalTrifurcation_of_threeArms` : a canonical trifurcation from three arms.
- `bc8_hroute_of_originRewiring` : the route from origin rewiring.

## iii. Table of contents

- A. Canonical trifurcations at the origin
- B. Origin rewiring

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
-/

@[expose] public section

open Set SimpleGraph
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths
open MeasureTheory

namespace StatMech

namespace Walls

variable {d : ℕ}

/-! ## A. Canonical trifurcations at the origin -/

lemma bc8_isCanonicalTrifurcation_of_arms (ω : ConfigSpace (Sym2 (Site d)))
    {a₁ a₂ a₃ : Site d}
    (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (hadj : (openSubgraph d ω).Adj 0 a₁ ∧ (openSubgraph d ω).Adj 0 a₂ ∧
      (openSubgraph d ω).Adj 0 a₃)
    (hinf : (cluster d (removeSite 0 ω) a₁).Infinite ∧
      (cluster d (removeSite 0 ω) a₂).Infinite ∧ (cluster d (removeSite 0 ω) a₃).Infinite)
    (hcd12 : cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₂)
    (hcd13 : cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₃)
    (hcd23 : cluster d (removeSite 0 ω) a₂ ≠ cluster d (removeSite 0 ω) a₃) :
    IsCanonicalTrifurcation d ω 0 := by
  refine ⟨a₁, a₂, a₃, hne, hadj, hinf, ?_, ?_, ?_⟩
  · exact bc8_cut_ne_iff_disconnected.mp hcd12
  · exact bc8_cut_ne_iff_disconnected.mp hcd13
  · exact bc8_cut_ne_iff_disconnected.mp hcd23

lemma bc8_arm_ne_of_cut_ne {ω : ConfigSpace (Sym2 (Site d))} {a b : Site d}
    (h : cluster d (removeSite 0 ω) a ≠ cluster d (removeSite 0 ω) b) : a ≠ b := by
  rintro rfl; exact h rfl

lemma bc8_isCanonicalTrifurcation_of_threeArms (ω : ConfigSpace (Sym2 (Site d)))
    {a₁ a₂ a₃ : Site d}
    (hadj1 : (openSubgraph d ω).Adj 0 a₁) (hadj2 : (openSubgraph d ω).Adj 0 a₂)
    (hadj3 : (openSubgraph d ω).Adj 0 a₃)
    (hi1 : (cluster d (removeSite 0 ω) a₁).Infinite)
    (hi2 : (cluster d (removeSite 0 ω) a₂).Infinite)
    (hi3 : (cluster d (removeSite 0 ω) a₃).Infinite)
    (hcd12 : cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₂)
    (hcd13 : cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₃)
    (hcd23 : cluster d (removeSite 0 ω) a₂ ≠ cluster d (removeSite 0 ω) a₃) :
    IsCanonicalTrifurcation d ω 0 :=
  bc8_isCanonicalTrifurcation_of_arms ω
    ⟨bc8_arm_ne_of_cut_ne hcd12, bc8_arm_ne_of_cut_ne hcd13, bc8_arm_ne_of_cut_ne hcd23⟩
    ⟨hadj1, hadj2, hadj3⟩ ⟨hi1, hi2, hi3⟩ hcd12 hcd13 hcd23

lemma bc8_isCanonicalTrifurcation_of_originSplits (ω : ConfigSpace (Sym2 (Site d)))
    (h : ∃ a₁ a₂ a₃ : Site d,
      (openSubgraph d ω).Adj 0 a₁ ∧ (openSubgraph d ω).Adj 0 a₂ ∧ (openSubgraph d ω).Adj 0 a₃ ∧
      (cluster d (removeSite 0 ω) a₁).Infinite ∧ (cluster d (removeSite 0 ω) a₂).Infinite ∧
      (cluster d (removeSite 0 ω) a₃).Infinite ∧
      cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₂ ∧
      cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₃ ∧
      cluster d (removeSite 0 ω) a₂ ≠ cluster d (removeSite 0 ω) a₃) :
    IsCanonicalTrifurcation d ω 0 := by
  obtain ⟨a₁, a₂, a₃, hadj1, hadj2, hadj3, hi1, hi2, hi3, hcd12, hcd13, hcd23⟩ := h
  exact bc8_isCanonicalTrifurcation_of_threeArms ω hadj1 hadj2 hadj3 hi1 hi2 hi3 hcd12 hcd13 hcd23

/-! ## B. Origin rewiring -/

/-- Origin rewiring for the box of radius `n`: every configuration of `threeMeetBox d n` gets three
open
neighbours of the origin in distinct infinite clusters without the origin after forcing a finite set
of edges avoiding the origin. -/
def bc8_OriginRewiring (d n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n, ∃ W : Finset (Sym2 (Site d)),
    (∀ e ∈ W, (0 : Site d) ∉ e) ∧
    ∃ a₁ a₂ a₃ : Site d,
      (openSubgraph d (forceOpenFinset W ω)).Adj 0 a₁ ∧
      (openSubgraph d (forceOpenFinset W ω)).Adj 0 a₂ ∧
      (openSubgraph d (forceOpenFinset W ω)).Adj 0 a₃ ∧
      (cluster d (removeSite 0 (forceOpenFinset W ω)) a₁).Infinite ∧
      (cluster d (removeSite 0 (forceOpenFinset W ω)) a₂).Infinite ∧
      (cluster d (removeSite 0 (forceOpenFinset W ω)) a₃).Infinite ∧
      cluster d (removeSite 0 (forceOpenFinset W ω)) a₁ ≠
        cluster d (removeSite 0 (forceOpenFinset W ω)) a₂ ∧
      cluster d (removeSite 0 (forceOpenFinset W ω)) a₁ ≠
        cluster d (removeSite 0 (forceOpenFinset W ω)) a₃ ∧
      cluster d (removeSite 0 (forceOpenFinset W ω)) a₂ ≠
        cluster d (removeSite 0 (forceOpenFinset W ω)) a₃

lemma bc8_canonicalTrif_of_originRewiring (n : ℕ) (hrw : bc8_OriginRewiring d n)
    (ω : ConfigSpace (Sym2 (Site d))) (hω : ω ∈ threeMeetBox d n) :
    ∃ W : Finset (Sym2 (Site d)), (∀ e ∈ W, (0 : Site d) ∉ e) ∧
      IsCanonicalTrifurcation d (forceOpenFinset W ω) 0 := by
  obtain ⟨W, hW0, a₁, a₂, a₃, hadj1, hadj2, hadj3, hi1, hi2, hi3, hcd12, hcd13, hcd23⟩ := hrw ω hω
  exact ⟨W, hW0, bc8_isCanonicalTrifurcation_of_threeArms (forceOpenFinset W ω)
    hadj1 hadj2 hadj3 hi1 hi2 hi3 hcd12 hcd13 hcd23⟩

lemma bc8_corridorWorks_of_rewiringData (ω : ConfigSpace (Sym2 (Site d)))
    {W : Finset (Sym2 (Site d))} {a₁ a₂ a₃ : Site d}
    (hadj1 : (openSubgraph d (forceOpenFinset W ω)).Adj 0 a₁)
    (hadj2 : (openSubgraph d (forceOpenFinset W ω)).Adj 0 a₂)
    (hadj3 : (openSubgraph d (forceOpenFinset W ω)).Adj 0 a₃)
    (hi1 : (cluster d (removeSite 0 (forceOpenFinset W ω)) a₁).Infinite)
    (hi2 : (cluster d (removeSite 0 (forceOpenFinset W ω)) a₂).Infinite)
    (hi3 : (cluster d (removeSite 0 (forceOpenFinset W ω)) a₃).Infinite)
    (hcd12 : cluster d (removeSite 0 (forceOpenFinset W ω)) a₁ ≠
      cluster d (removeSite 0 (forceOpenFinset W ω)) a₂)
    (hcd13 : cluster d (removeSite 0 (forceOpenFinset W ω)) a₁ ≠
      cluster d (removeSite 0 (forceOpenFinset W ω)) a₃)
    (hcd23 : cluster d (removeSite 0 (forceOpenFinset W ω)) a₂ ≠
      cluster d (removeSite 0 (forceOpenFinset W ω)) a₃) :
    ω ∈ CorridorWorks a₁ a₂ a₃ W :=
  ⟨⟨bc8_arm_ne_of_cut_ne hcd12, bc8_arm_ne_of_cut_ne hcd13, bc8_arm_ne_of_cut_ne hcd23⟩,
   ⟨openSubgraph_le (forceOpenFinset W ω) hadj1, openSubgraph_le (forceOpenFinset W ω) hadj2,
     openSubgraph_le (forceOpenFinset W ω) hadj3⟩,
   ⟨hi1, hi2, hi3⟩, hcd12, hcd13, hcd23⟩

lemma bc8_threeMeetBox_subset_corridorCover (n : ℕ) (hrw : bc8_OriginRewiring d n) :
    threeMeetBox d n ⊆
      ⋃ (a₁ : Site d) (a₂ : Site d) (a₃ : Site d) (G : Finset (Sym2 (Site d))),
        CorridorWorks a₁ a₂ a₃ G := by
  intro ω hω
  obtain ⟨W, _hW0, a₁, a₂, a₃, hadj1, hadj2, hadj3, hi1, hi2, hi3, hcd12, hcd13, hcd23⟩ := hrw ω hω
  refine Set.mem_iUnion.mpr ⟨a₁, Set.mem_iUnion.mpr ⟨a₂, Set.mem_iUnion.mpr ⟨a₃,
    Set.mem_iUnion.mpr ⟨W, ?_⟩⟩⟩⟩
  exact bc8_corridorWorks_of_rewiringData ω hadj1 hadj2 hadj3 hi1 hi2 hi3 hcd12 hcd13 hcd23

lemma bc8_hroute_of_originRewiring
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ)
    (hrw : ∀ n : ℕ, bc8_OriginRewiring d n) :
    ∀ n : ℕ, 0 < μ (threeMeetBox d n) →
      ∃ a₁ a₂ a₃ : Site d, 0 < μ (NeighborTrifPrecursor d a₁ a₂ a₃) :=
  hroute_of_corridorCover μ hfe (fun n => bc8_threeMeetBox_subset_corridorCover n (hrw n))

/-- Burton–Keane conclusion from origin rewiring in every box and the counting hypotheses of
`burton_keane_uniqueness_full`. Those hypotheses are unsatisfiable for `d ≥ 1`
(`tfc_not_hbound_hdens`), so the statement has content only for `d = 0`. -/
lemma bc8_burtonKeane_uniqueness_of_originRewiring
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (bdry : ℕ → ℕ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Filter.Tendsto
      (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ))
      Filter.atTop (nhds 0))
    (hrw : ∀ n : ℕ, bc8_OriginRewiring d n) :
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ μ (atLeastTwoInfinite d) = 0
      ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  burton_keane_uniqueness_trif_route μ herg hfe bdry hbound hvol hdens
    (bc8_hroute_of_originRewiring μ hfe hrw)

lemma bc8_threeArmsNoCrossing_isCanonical (n : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    (hω : ω ∈ threeMeetBox d n) :
    ∃ a₁ a₂ a₃ : Site d,
      (cluster d (removeSite 0 ω) a₁).Infinite ∧
      (cluster d (removeSite 0 ω) a₂).Infinite ∧
      (cluster d (removeSite 0 ω) a₃).Infinite ∧
      cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₂ ∧
      cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₃ ∧
      cluster d (removeSite 0 ω) a₂ ≠ cluster d (removeSite 0 ω) a₃ ∧
      bc8_NoCrossing ω a₁ a₂ ∧ bc8_NoCrossing ω a₁ a₃ ∧ bc8_NoCrossing ω a₂ a₃ := by
  obtain ⟨a₁, a₂, a₃, hi1, hi2, hi3, hcd12, hcd13, hcd23⟩ :=
    bc8_threeArmClusters_distinct n ω hω
  exact ⟨a₁, a₂, a₃, hi1, hi2, hi3, hcd12, hcd13, hcd23,
    bc8_noCrossing ω a₁ a₂, bc8_noCrossing ω a₁ a₃, bc8_noCrossing ω a₂ a₃⟩

end Walls

end StatMech
