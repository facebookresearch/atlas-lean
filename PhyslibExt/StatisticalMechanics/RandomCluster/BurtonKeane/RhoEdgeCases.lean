/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.HighDimRouting
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorSidesFromClusters

/-!
# Open edges after opening three axis corridors

After opening three axis corridors and removing the origin, every open edge is a lattice edge away
from the origin that was open in `ω` or belongs to a corridor.

## i. Overview

The corridor configuration opens the edges of three axis segments and then closes every edge at the
origin. An open edge of the result is a lattice edge not containing the origin, and it is either
open in `ω` or one of the corridor edges. These case splits feed the arguments about corridor
clusters.

## ii. Key results

- `bc3_rho_omegaOpen_or_forced` : open edges are open in `ω` or forced
- `bc3_isOpenEdge_rhoCorridor_cases` : the case split for the three-corridor configuration

## iii. Table of contents

- A. Results

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
- G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §8.2.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation

namespace StatMech

namespace Walls

variable {d : ℕ}

/-! ## A. Results -/

lemma bc3_rhoEdge_cases (ω : ConfigSpace (Sym2 (Site d))) (G : Finset (Sym2 (Site d)))
    {e : Sym2 (Site d)} (h : removeSite 0 (forceOpenFinset G ω) e = true) :
    (0 : Site d) ∉ e ∧ (ω e = true ∨ e ∈ G) := by
  have hno0 : (0 : Site d) ∉ e := by
    intro hmem
    rw [removeSite_apply_of_mem hmem] at h
    exact Bool.false_ne_true h
  refine ⟨hno0, ?_⟩
  rw [removeSite_apply_of_notMem hno0] at h
  by_cases hG : e ∈ G
  · exact Or.inr hG
  · rw [forceOpenFinset_of_notMem hG] at h
    exact Or.inl h

lemma bc3_rho_origin_notMem (ω : ConfigSpace (Sym2 (Site d))) (G : Finset (Sym2 (Site d)))
    {e : Sym2 (Site d)} (h : removeSite 0 (forceOpenFinset G ω) e = true) :
    (0 : Site d) ∉ e :=
  (bc3_rhoEdge_cases ω G h).1

lemma bc3_rho_endpoints_ne_zero (ω : ConfigSpace (Sym2 (Site d))) (G : Finset (Sym2 (Site d)))
    {x y : Site d} (h : removeSite 0 (forceOpenFinset G ω) s(x, y) = true) :
    x ≠ (0 : Site d) ∧ y ≠ (0 : Site d) := by
  have hno0 : (0 : Site d) ∉ s(x, y) := bc3_rho_origin_notMem ω G h
  rw [Sym2.mem_iff] at hno0
  push Not at hno0
  exact ⟨fun hx => hno0.1 hx.symm, fun hy => hno0.2 hy.symm⟩

lemma bc3_rho_omegaOpen_or_forced (ω : ConfigSpace (Sym2 (Site d)))
    (G : Finset (Sym2 (Site d))) {e : Sym2 (Site d)}
    (h : removeSite 0 (forceOpenFinset G ω) e = true) :
    ω e = true ∨ e ∈ G :=
  (bc3_rhoEdge_cases ω G h).2

lemma bc3_isOpenEdge_rho_cases (ω : ConfigSpace (Sym2 (Site d))) (G : Finset (Sym2 (Site d)))
    {x y : Site d} (h : IsOpenEdge d (removeSite 0 (forceOpenFinset G ω)) x y) :
    (hypercubicLattice d).Adj x y ∧ (0 : Site d) ∉ s(x, y) ∧
      (ω s(x, y) = true ∨ s(x, y) ∈ G) := by
  obtain ⟨hadj, hopen⟩ := h
  obtain ⟨hno0, hcase⟩ := bc3_rhoEdge_cases ω G hopen
  exact ⟨hadj, hno0, hcase⟩

lemma bc3_rho_openSubgraph_le_lattice (ω : ConfigSpace (Sym2 (Site d)))
    (G : Finset (Sym2 (Site d))) :
    openSubgraph d (removeSite 0 (forceOpenFinset G ω)) ≤ hypercubicLattice d :=
  openSubgraph_le _

lemma bc3_rho_edgeSet_subset_lattice (ω : ConfigSpace (Sym2 (Site d)))
    (G : Finset (Sym2 (Site d))) :
    (openSubgraph d (removeSite 0 (forceOpenFinset G ω))).edgeSet ⊆
      (hypercubicLattice d).edgeSet :=
  fun _ h => SimpleGraph.edgeSet_subset_edgeSet.mpr (openSubgraph_le _) h

lemma bc3_rho_edgeSet_cases (ω : ConfigSpace (Sym2 (Site d))) (G : Finset (Sym2 (Site d)))
    {e : Sym2 (Site d)}
    (h : e ∈ (openSubgraph d (removeSite 0 (forceOpenFinset G ω))).edgeSet) :
    e ∈ (hypercubicLattice d).edgeSet ∧ (0 : Site d) ∉ e ∧ (ω e = true ∨ e ∈ G) := by
  refine ⟨bc3_rho_edgeSet_subset_lattice ω G h, ?_⟩
  induction e with
  | h x y =>
    rw [SimpleGraph.mem_edgeSet, openSubgraph_adj] at h
    exact bc3_rhoEdge_cases ω G h.2

lemma bc3_isOpenEdge_rhoCorridor_cases (ω : ConfigSpace (Sym2 (Site d)))
    (j₁ j₂ j₃ : Fin d) (L₁ L₂ L₃ : ℕ) {x y : Site d}
    (h : IsOpenEdge d (removeSite 0 (forceOpenFinset
          (hrHD_corridorEdges j₁ (L₁ + 1) ∪ hrHD_corridorEdges j₂ (L₂ + 1) ∪
            hrHD_corridorEdges j₃ (L₃ + 1)) ω)) x y) :
    (hypercubicLattice d).Adj x y ∧ (0 : Site d) ∉ s(x, y) ∧
      (ω s(x, y) = true ∨
        s(x, y) ∈ hrHD_corridorEdges j₁ (L₁ + 1) ∪ hrHD_corridorEdges j₂ (L₂ + 1) ∪
          hrHD_corridorEdges j₃ (L₃ + 1)) :=
  bc3_isOpenEdge_rho_cases ω
    (hrHD_corridorEdges j₁ (L₁ + 1) ∪ hrHD_corridorEdges j₂ (L₂ + 1) ∪
      hrHD_corridorEdges j₃ (L₃ + 1)) h

end Walls

end StatMech
