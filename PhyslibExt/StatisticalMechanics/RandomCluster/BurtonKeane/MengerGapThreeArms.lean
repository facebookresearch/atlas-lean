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
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifSuperVertex
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseStarForestEmbedding
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.NeighbourBoxConnect

/-!
# Three incident arms of a coarse trifurcation

A coarse trifurcation has three incident arms separated in the contracted lattice, each reaching the
boundary, so a coarse boundary injection bounds the coarse count.

## i. Overview

Every coarse trifurcation of the `L`-box around `y` has three arms incident to the box
(`bc67_GnIncident`) that are pairwise unreachable in the contracted lattice; infinite arms reach the
boundary of `B_R`. A boundary injection (`bc64_CoarseBoundaryInjection`) then bounds
`bc61_coarseTcount` by `|∂B_R|`. In `bc60_upperLines` the origin is a coarse trifurcation while the
neighbour-reach condition `bc56_BoxClusterReachesNbr 2 3` fails.

The trifurcation notion here is the coarse one on `L`-boxes (`bc61_IsCoarseTrifurcation`,
`bc67_IsGnTrifurcation`), whose arms are infinite after the whole `L`-box is removed. Results that
assume a certificate for every configuration are conditional: no such certificate is constructed for
all configurations.

## ii. Key results

- `bc101_gnTrif_three_incident_arms` : three separated incident arms
- `StatMech.Walls.bc64_coarseTcount_le_boundary_of_boundaryInjection` (in
  `CoarseStarForestEmbedding`) : a boundary injection bounds the coarse count
- `bc101_status` : the statements together

## iii. Table of contents

- A. Results
- B. Summary

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
- G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §8.2.
-/

@[expose] public section

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}

/-! ## A. Results -/

lemma bc101_gnTrif_three_incident_arms (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d)
    (h : bc61_IsCoarseTrifurcation ω L y) :
    ∃ a₁ a₂ a₃ : Site d,
      (bc67_GnIncident ω L y a₁ ∧ bc67_GnIncident ω L y a₂ ∧ bc67_GnIncident ω L y a₃) ∧
      ((cluster d (removeSites (bc61_boxAround d L y) ω) a₁).Infinite ∧
       (cluster d (removeSites (bc61_boxAround d L y) ω) a₂).Infinite ∧
       (cluster d (removeSites (bc61_boxAround d L y) ω) a₃).Infinite) ∧
      (¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂ ∧
       ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃ ∧
       ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃) := by
  obtain ⟨a₁, a₂, a₃, hincs, hinf, hcuts⟩ := bc67_gnTrif_of_coarseTrif ω L y h
  exact ⟨a₁, a₂, a₃, hincs, hinf, hcuts⟩

lemma bc101_residue_is_boundary_injection (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d R) (hz₁ : z₁ ∈ vertexBoundary d R)
    (hzne : z₀ ≠ z₁) (hinj : bc64_CoarseBoundaryInjection ω L R) :
    bc61_CoarseForestLeafCount ω L R :=
  (bc63_coarseArmEmbedding_iff_forestLeafCount ω L R).mp
    (bc64_coarseArmEmbedding_of_boundaryInjection ω L R hz₀ hz₁ hzne hinj)

lemma bc101_three_arms_upperLines {L : ℕ} (hL : 3 ≤ L) :
    ∃ a₁ a₂ a₃ : Site 2,
      (bc67_GnIncident bc60_upperLines L 0 a₁ ∧ bc67_GnIncident bc60_upperLines L 0 a₂ ∧
        bc67_GnIncident bc60_upperLines L 0 a₃) ∧
      (¬ (bc67_contractedLattice bc60_upperLines L 0).Reachable a₁ a₂ ∧
       ¬ (bc67_contractedLattice bc60_upperLines L 0).Reachable a₁ a₃ ∧
       ¬ (bc67_contractedLattice bc60_upperLines L 0).Reachable a₂ a₃) :=
  bc81_singleBox_no_gap bc60_upperLines L 0 (bc61_wholeBox_severs_upperLines hL)

/-! ## B. Summary -/

lemma bc101_status :
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d),
      bc61_IsCoarseTrifurcation ω L y →
      ∃ a₁ a₂ a₃ : Site d,
        (bc67_GnIncident ω L y a₁ ∧ bc67_GnIncident ω L y a₂ ∧ bc67_GnIncident ω L y a₃) ∧
        (¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂ ∧
         ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃ ∧
         ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃)) ∧
    (∀ {L : ℕ}, 3 ≤ L →
      bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2) ∧
        ¬ bc56_BoxClusterReachesNbr 2 3) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (z₀ z₁ : Site d),
      z₀ ∈ vertexBoundary d R → z₁ ∈ vertexBoundary d R → z₀ ≠ z₁ →
      bc64_CoarseBoundaryInjection ω L R →
      bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ω L y h; exact bc81_singleBox_no_gap ω L y h
  · intro L hL; exact bc99_notFree_of_coarseTrif hL
  · intro ω L R z₀ z₁ hz₀ hz₁ hzne hinj
    exact bc64_coarseTcount_le_boundary_of_boundaryInjection ω L R hz₀ hz₁ hzne hinj

end StatMech.Walls
