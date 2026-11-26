/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Order.Filter.Defs
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseForestFiniteEnergy
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClassicalPrecursorFiniteEnergy
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClassicalVertexForest
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalCutSeparation

/-!
# Uniqueness from the route via fine trifurcations

Classical trifurcations are fine, and fine trifurcations are coarse at scale zero, so the route
hypothesis gives the scale-zero coarse step and Burton–Keane uniqueness for Bernoulli percolation.

## i. Overview

Deleting the origin from the open subgraph is below removing it, so a classical trifurcation at the
origin is fine, and the event of a coarse trifurcation at scale `0` is the event of a fine
trifurcation. With finite energy, the route hypothesis (or disjoint routing) gives the scale-zero
coarse step, and the scale-zero count gives uniqueness (`bfx_bk_of_route`).

**Fidelity.** `bfx_bk_of_route` is conditional on the route hypothesis `hroute`. With the nine-shell
route package of `SquareLatticeUniqueness` it becomes the unconditional `bins_bk_unconditional` on
`ℤ²`.

## ii. Key results

- `bfx_trifExistence_of_route` : the scale-zero coarse step from the route.
- `bfx_bk_of_route` : uniqueness from the route hypothesis.

## iii. Table of contents

- A. Fine and classical trifurcations
- B. Uniqueness

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
- G. Grimmett, *Percolation*, 2nd ed., Springer (1999), Section 8.2.
-/

@[expose] public section

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}

/-! ## A. Fine and classical trifurcations -/

lemma bfx_deleteVertex_le (ω : ConfigSpace (Sym2 (Site d))) :
    bkg_deleteVertex (openSubgraph d ω) 0 ≤ openSubgraph d (removeSite 0 ω) := by
  intro a b hab
  obtain ⟨hadj, ha, hb⟩ := hab
  rw [openSubgraph_adj] at hadj ⊢
  obtain ⟨hlatt, hopen⟩ := hadj
  refine ⟨hlatt, ?_⟩
  have h0 : (0 : Site d) ∉ s(a, b) := by
    simp only [Sym2.mem_iff, not_or]
    exact ⟨fun h => ha h.symm, fun h => hb h.symm⟩
  rw [removeSite_apply_of_notMem h0]
  exact hopen

lemma bfx_fineTrif_of_classical (ω : ConfigSpace (Sym2 (Site d)))
    (h : bc47_IsClassicalTrifurcation ω 0) : bft_FineTrif ω 0 := by
  obtain ⟨a₁, a₂, a₃, hne, ⟨he1, he2, he3⟩, ⟨hi1, hi2, hi3⟩, ⟨hs12, hs13, hs23⟩⟩ := h
  rw [bft_fineTrif_iff]
  refine ⟨a₁, a₂, a₃, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · exact he1
  · exact he2
  · exact he3
  · rw [daep_removeSites_singleton]; exact hi1
  · rw [daep_removeSites_singleton]; exact hi2
  · rw [daep_removeSites_singleton]; exact hi3
  · exact fun hr => hs12 (hr.mono (bfx_deleteVertex_le ω))
  · exact fun hr => hs13 (hr.mono (bfx_deleteVertex_le ω))
  · exact fun hr => hs23 (hr.mono (bfx_deleteVertex_le ω))

lemma bfx_coarseSet_eq_fineSet :
    {ω : ConfigSpace (Sym2 (Site d)) | bc61_IsCoarseTrifurcation ω 0 0}
      = {ω | bft_FineTrif ω 0} := by
  ext ω
  simp only [Set.mem_ofPred_eq]
  rw [bc67_coarseTrif_is_G_n_trifurcation ω 0 0]
  exact (bfl_fineTrif_iff_bc67_zero ω 0).symm

/-! ## B. Uniqueness -/

lemma bfx_trifExistence_of_route (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hroute : ∀ n : ℕ,
      0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (threeMeetBox d n) →
        ∃ a₁ a₂ a₃ : Site d,
          0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
            (NeighborTrifPrecursor d a₁ a₂ a₃)) :
    bc61_CoarseTrifExistence (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1) 0 := by
  intro htop
  set μ := bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 with hμ
  have hfe : HasFiniteEnergyMerge μ := bkc_bernoulli_hasFiniteEnergyMerge p hp1 hp0
  have hcl : 0 < μ {ω | bc47_IsClassicalTrifurcation ω 0} :=
    bc49_classical_htrif_of_route μ hfe hroute htop
  have hsub : {ω : ConfigSpace (Sym2 (Site d)) | bc47_IsClassicalTrifurcation ω 0}
      ⊆ {ω | bft_FineTrif ω 0} := fun ω hω => bfx_fineTrif_of_classical ω hω
  have hbft : 0 < μ {ω | bft_FineTrif ω 0} := lt_of_lt_of_le hcl (measure_mono hsub)
  rw [bfx_coarseSet_eq_fineSet]
  exact hbft

lemma bfx_trifExistence_of_routingCover (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hrt : ∀ n : ℕ, hrHD_DisjointRouting d n) :
    bc61_CoarseTrifExistence (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1) 0 :=
  bfx_trifExistence_of_route p hp1 hp0
    (hrHD_route_of_routing (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1)
      (bkc_bernoulli_hasFiniteEnergyMerge p hp1 hp0) hrt)

/-- **Burton–Keane uniqueness from the route.** For Bernoulli bond percolation in `d ≥ 1` with
`p > 0`,
if every box with three distinct infinite clusters meeting it with positive probability has a
neighbour trifurcation precursor of positive probability, then a.s. `N ∈ {0, 1}`. Burton and Keane,
*Density and uniqueness in percolation* (1989). Same statement as `bc54_burton_keane_bernoulli`;
kept because PrecursorRouting, ShellInsertionTolerance use it. -/
lemma bfx_bk_of_route (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hroute : ∀ n : ℕ,
      0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (threeMeetBox d n) →
        ∃ a₁ a₂ a₃ : Site d,
          0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
            (NeighborTrifPrecursor d a₁ a₂ a₃)) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  bfe_bk hd p hp1 hp0 (bfx_trifExistence_of_route p hp1 hp0 hroute)

lemma bfx_bk_atLeastTwo_of_route (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hroute : ∀ n : ℕ,
      0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (threeMeetBox d n) →
        ∃ a₁ a₂ a₃ : Site d,
          0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
            (NeighborTrifPrecursor d a₁ a₂ a₃)) :
    bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 :=
  (bfx_bk_of_route hd p hp1 hp0 hroute).2.1

end StatMech.Walls
