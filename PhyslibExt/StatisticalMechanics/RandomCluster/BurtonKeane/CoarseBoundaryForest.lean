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
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseForestConnected
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CanonForestCount

/-!
# Coarse boundary forests

Leaves of a forest mapped injectively to the boundary bound its branch vertices; forest data give a
connected forest and `μ(N = ⊤) = 0`, and coarse arms always reach the boundary.

## i. Overview

In a finite forest whose leaves map injectively into the boundary, branch vertices are at most the
boundary size. Forest data give a connected coarse forest. In the upper-lines configuration two
disjoint boxes share a boundary connection. With the connected forest for every configuration and
the coarse step, `μ(N = ⊤) = 0`. Coarse arms reach the boundary unconditionally.

## ii. Key results

- `StatMech.Percolation.flc2_leaf_card_le_boundary` (in `SpanningTreeLeafCount`) : branch vertices
  from boundary leaves.
- `StatMech.Walls.bc65_infiniteClusters_top_null_of_connectedForest_route` (in
  `CoarseForestConnected`) : `μ(N = ⊤) = 0` from the connected forest.

## iii. Table of contents

- A. Leaf injections and connected forests

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

/-! ## A. Leaf injections and connected forests -/

set_option linter.unusedDecidableInType false in
/-- Same statement as `bc65_connectedForest_of_forestData`; kept because TrifSuperVertex uses it. -/
lemma bc66_connectedForest_of_forestData (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (W : Type) [Fintype W] [Nonempty W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (ιT : Site d → W) (lamL : W → Site d)
    (hacyc : G.IsAcyclic) (hmin : ∀ v, 1 ≤ G.degree v)
    (hdeg3 : ∀ y, y ∈ box d R → bc61_IsCoarseTrifurcation ω L y → 3 ≤ G.degree (ιT y))
    (hιinj : ∀ y, y ∈ box d R → bc61_IsCoarseTrifurcation ω L y → ∀ z, z ∈ box d R →
      bc61_IsCoarseTrifurcation ω L z → ιT y = ιT z → y = z)
    (hlammap : ∀ v, G.degree v = 1 → lamL v ∈ vertexBoundary d R)
    (hlaminj : Set.InjOn lamL (univ.filter (fun v => G.degree v = 1))) :
    bc65_ConnectedCoarseForest ω L R :=
  bc65_connectedForest_of_forestData ω L R W G ιT lamL hacyc hmin hdeg3 hιinj hlammap hlaminj

/-- Same statement as `bc63_coarseArm_reaches_boundary`; kept because TrifSuperVertex uses it. -/
lemma bc66_coarse_armReaching_unconditional (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (hR : 1 ≤ R) (y a : Site d) (habox : a ∈ box d R)
    (hinf : (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite) :
    ∃ z ∈ vertexBoundary d R, Connected d (removeSites (bc61_boxAround d L y) ω) a z :=
  StatMech.Walls.bc63_coarseArm_reaches_boundary ω L R hR y a habox hinf

lemma bc66_status :
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), 1 ≤ R → ∀ (y a : Site d), a ∈ box d R →
      (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite →
      ∃ z ∈ vertexBoundary d R, Connected d (removeSites (bc61_boxAround d L y) ω) a z) ∧
    (∀ {L : ℕ}, 3 ≤ L → bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2)) ∧
    (∀ {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V) [_inst : DecidableRel G.Adj],
      G.IsAcyclic → (∀ v, 1 ≤ G.degree v) →
      (univ.filter (fun v => 3 ≤ G.degree v)).card
        ≤ (univ.filter (fun v => G.degree v = 1)).card) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (z₀ z₁ : Site d),
      z₀ ∈ vertexBoundary d R → z₁ ∈ vertexBoundary d R → z₀ ≠ z₁ →
      bc64_CoarseBoundaryInjection ω L R → bc65_ConnectedCoarseForest ω L R) ∧
    (∀ (L : ℕ),
      Disjoint (bc61_boxAround 2 L (0 : Site 2))
          (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧
        Connected 2 bc60_upperLines
          (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ω L R hR y a habox hinf
    exact bc66_coarse_armReaching_unconditional ω L R hR y a habox hinf
  · intro L hL
    exact StatMech.Walls.bc61_wholeBox_severs_upperLines hL
  · intro V _ _ G _ hacyc hmin
    exact Percolation.flc2_forest_internal_le_leaves G hacyc hmin
  · intro ω L R z₀ z₁ hz₀ hz₁ hzne hinj
    exact StatMech.Walls.bc65_connectedForest_of_boundaryInjection ω L R hz₀ hz₁ hzne hinj
  · intro L
    exact bc64_arms_can_share_boundary L

end StatMech.Walls
