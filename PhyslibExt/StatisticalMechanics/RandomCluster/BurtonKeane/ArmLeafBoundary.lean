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
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalForestLeafCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseForestConnected
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GnBranchLeafCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.MengerGapThreeArms

/-!
# Leaf counts for coarse forests

The global forest gives the coarse count, shared leaves are absorbed by the leaf count, and the
connected-forest reduction holds when the box has no coarse trifurcation.

## i. Overview

From the global forest `bc69_Gn_globalForest` the coarse count is at most the boundary size. In a
forest of minimum degree one, branch vertices are at most the leaves, so leaves shared between arms
do not affect the bound. Spanning forests of fibre quotients satisfy the same inequality. In the
upper-lines configuration two disjoint boxes are connected, and the disjoint star has the expected
degrees.

## ii. Key results

- `StatMech.Walls.bc80_branch_le_leaf` (in `GnBranchLeafCount`) : branch vertices are at most leaves
  in fibre spanning forests.

## iii. Table of contents

- A. Leaf counts
- B. Examples

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
-/

@[expose] public section

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}

/-! ## A. Leaf counts -/

/-! ## B. Examples -/

lemma bc102_bc64_disjointStar_degrees :
    bc64_starG.degree 0 = 3 ∧ (∀ i : Fin 4, i ≠ 0 → bc64_starG.degree i = 1) :=
  ⟨bc64_starG_centre_deg, bc64_starG_leaf_deg⟩

lemma bc102_BK_count_reduces_to_connectedForest (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) :
    (bc69_Gn_globalForest ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) ∧
    (∀ {z₀ z₁ : Site d}, z₀ ∈ vertexBoundary d R → z₁ ∈ vertexBoundary d R → z₀ ≠ z₁ →
      bc64_CoarseBoundaryInjection ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) :=
  ⟨bc69_coarseTcount_le_boundary ω L R,
   fun hz₀ hz₁ hzne hinj => StatMech.Walls.bc64_coarseTcount_le_boundary_of_boundaryInjection ω L R
       hz₀ hz₁ hzne hinj⟩

lemma bc102_status :
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      bc69_Gn_globalForest ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) ∧
    (∀ {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V) [_inst : DecidableRel G.Adj],
      G.IsAcyclic → (∀ v, 1 ≤ G.degree v) →
      (univ.filter (fun v => 3 ≤ G.degree v)).card
        ≤ (univ.filter (fun v => G.degree v = 1)).card) ∧
    (bc64_starG.degree 0 = 3 ∧ (∀ i : Fin 4, i ≠ 0 → bc64_starG.degree i = 1)) ∧
    (∀ (L : ℕ),
      Disjoint (bc61_boxAround 2 L (0 : Site 2))
          (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧
        Connected 2 bc60_upperLines
          (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1)) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (z₀ z₁ : Site d),
      z₀ ∈ vertexBoundary d R → z₁ ∈ vertexBoundary d R → z₀ ≠ z₁ →
      bc64_CoarseBoundaryInjection ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ω L R h; exact bc69_coarseTcount_le_boundary ω L R h
  · intro V _ _ G _ hacyc hmin; exact Percolation.flc2_forest_internal_le_leaves G hacyc hmin
  · exact bc102_bc64_disjointStar_degrees
  · intro L; exact StatMech.Walls.bc64_arms_can_share_boundary L
  · intro ω L R z₀ z₁ hz₀ hz₁ hzne hinj; exact
      StatMech.Walls.bc64_coarseTcount_le_boundary_of_boundaryInjection ω L R hz₀ hz₁ hzne hinj

end StatMech.Walls
