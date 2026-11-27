/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.BoxSurfaceVolume
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.Clusters
public import MathlibExt.Probability.Percolation.InfiniteClusterCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeaneUniqueness
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifurcationCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalCutSeparation
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SingleCutSeparation
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmReachComponent
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForestPeel
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.PrivateFarForest
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmForestRooting
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmCutAcyclic
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmCutSpanning
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmCutFunnel
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmRootSide

/-!
# Root-ward avoiding walks

A walk from a trifurcation's arm that avoids the trifurcation is the same as a connection after
removing it; a chain example shows the all-parents rank condition is contradictory with a far
parent.

## i. Overview

Removing a site only deletes edges, so connections after removing `x` are exactly walks avoiding
`x`. If the root-ward avoiding walk condition is asked for all parents and ranks, a far parent makes
it false. The labelling `bc42_chainFarLab` on a three-vertex chain shows that the single-parent
version is consistent.

## ii. Key results

- `bc42_avoidingWalk_iff_connected_removeSite` : avoiding walks are connections after removal
- `bc42_rootWardAvoidingWalk_allParRank_false_of_farParent` : the all-parents version fails with a
  far parent
- `bc42_chainFar_consistent` : the chain labelling is consistent

## iii. Table of contents

- A. Results

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
- G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §8.2.
-/

@[expose] public section

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}

/-! ## A. Results -/

lemma bc42_removeSite_openSubgraph_le (y : Site d) (ω : ConfigSpace (Sym2 (Site d))) :
    openSubgraph d (removeSite y ω) ≤ openSubgraph d ω := by
  intro x z h
  obtain ⟨hadj, hval⟩ := h
  refine ⟨hadj, ?_⟩
  by_cases hy : y ∈ s(x, z)
  · rw [removeSite_apply_of_mem hy] at hval; exact absurd hval (by simp)
  · rwa [removeSite_apply_of_notMem hy] at hval

lemma bc42_avoidingWalk_of_connected_removeSite (ω : ConfigSpace (Sym2 (Site d))) {x y z : Site d}
    (hxy : x ≠ y) (h : Connected d (removeSite y ω) x z) :
    ∃ p : (openSubgraph d ω).Walk x z, ∀ v ∈ p.support, v ≠ y := by
  obtain ⟨w⟩ := h
  refine ⟨w.mapLe (bc42_removeSite_openSubgraph_le y ω), ?_⟩
  intro v hv
  rw [SimpleGraph.Walk.support_mapLe_eq_support] at hv
  exact fun hvy => (arc_walk_avoids_x hxy w) (hvy ▸ hv)

lemma bc42_avoidingWalk_iff_connected_removeSite (ω : ConfigSpace (Sym2 (Site d)))
    {x y z : Site d} (hxy : x ≠ y) :
    (∃ p : (openSubgraph d ω).Walk x z, ∀ v ∈ p.support, v ≠ y) ↔
      Connected d (removeSite y ω) x z := by
  constructor
  · rintro ⟨p, hp⟩
    have : Connected d (removeSites {y} ω) x z := by
      apply bc39_connected_removeSites_of_walk_avoids {y} ω p
      intro v hv; rw [Finset.mem_singleton]; exact hp v hv
    rwa [daep_removeSites_singleton] at this
  · exact bc42_avoidingWalk_of_connected_removeSite ω hxy

lemma bc42_rootWardAvoidingWalk_allParRank_false_of_farParent
    (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ z₀ : Site d} (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (hy0box : y₀ ∈ box d n) (htriy0 : IsTrifurcation d ω y₀)
    (hne : x₀ ≠ y₀) (hconn : Connected d ω x₀ y₀)
    (hadj : bc37_ArmAdjacent ω n y₀ z₀) (hx0z0 : x₀ ≠ z₀)
    (hfar : ¬ Connected d (removeSite y₀ ω) x₀ z₀) :
    ¬ ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d),
        bc41_RootWardAvoidingWalk ω n rank par := by
  intro hwalk
  set rank : Site d → ℕ ×ₗ ℕ := fun w => toLex (if w = y₀ then 1 else 0, 0) with hrank
  set par : Site d → Site d := fun _ => z₀ with hpar
  have hlt : rank x₀ < rank y₀ := by
    simp only [hrank, ite_eq_right hne, ite_eq_left]
    exact stt_lex_lt_fst (by norm_num)
  obtain ⟨p, hp⟩ :=
    hwalk rank par x₀ hx0box htri0 y₀ hy0box htriy0 hne hconn hlt (by simpa [hpar] using hx0z0)
      (by simpa [hpar] using hadj)
  have hconn_cut : Connected d (removeSite y₀ ω) x₀ (par y₀) :=
    (bc42_avoidingWalk_iff_connected_removeSite ω hne).mp ⟨p, hp⟩
  simp only [hpar] at hconn_cut
  exact hfar hconn_cut

/-- Labels of the three chain vertices seen from centre `c`, used to define sameness of arms. -/
def bc42_chainFarLab (c v : Fin 3) : ℕ :=
  if c = 1 then
    (if v = 1 then 101 else if v = 0 then 0 else 2)
  else
    (if v = 0 then 100 else 1)

lemma bc42_chainFar_consistent :
    ∃ (x₀ y₀ z₀ : Fin 3) (R : Fin 3 → Fin 3 → Fin 3 → Prop),
      (∀ c u v, R c u v ↔ bc42_chainFarLab c u = bc42_chainFarLab c v) ∧
      x₀ ≠ y₀ ∧ x₀ ≠ z₀ ∧ y₀ ≠ z₀ ∧
      R 0 y₀ z₀ ∧
      ¬ R 1 x₀ z₀ := by
  refine ⟨0, 1, 2, (fun c u v => bc42_chainFarLab c u = bc42_chainFarLab c v),
    fun _ _ _ => Iff.rfl, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide
  · decide

end StatMech.Walls
