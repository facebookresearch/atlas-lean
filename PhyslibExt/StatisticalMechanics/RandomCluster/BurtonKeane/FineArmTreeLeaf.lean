/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.LocallyFinite
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.FineTrif
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.RaysInTree
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.AcyclicArmSubforest

/-!
# Fine arms in a spanning tree

Arms and rays of a locally finite open tree reach the box boundary, and arm unions in a tree are
acyclic; an arbitrary spanning tree need not have its leaves on the boundary.

## i. Overview

A subgraph of the open subgraph is a subgraph of the lattice. In a locally finite open tree, a fine
arm and an injective ray from inside the box reach its vertex boundary. Unions of subgraphs of a
tree are acyclic, and ray graphs are subgraphs of the tree. Fine trifurcations are coarse
trifurcations at scale `0`, and the arm subforest datum at scale `0` gives the fine count. On
`Fin 4` a spanning tree with a leaf off the boundary shows the leaf clause cannot be dropped.

## ii. Key results

- `bfl_fineArm_reaches_boundary` : fine arms reach the boundary.
- `StatMech.Walls.bof2_interiorLeaf_obstruction` (in `HandshakeLeafCount`) : an arbitrary spanning
  tree can have a leaf off the boundary.

## iii. Table of contents

- A. Arms and rays in a tree
- B. Fine trifurcations

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

/-! ## A. Arms and rays in a tree -/

lemma bfl_tree_le_lattice {ω : ConfigSpace (Sym2 (Site d))} {T : SimpleGraph (Site d)}
    (hT : T ≤ openSubgraph d ω) : T ≤ hypercubicLattice d :=
  le_trans hT (openSubgraph_le ω)

lemma bfl_fineArm_reaches_boundary {ω : ConfigSpace (Sym2 (Site d))} (T : SimpleGraph (Site d))
    [LocallyFinite T] (hT : T ≤ openSubgraph d ω) {w x : Site d} {R : ℕ} (hR : 1 ≤ R) (hwx : w ≠ x)
    (hw : w ∈ box d R) (hinf : (ray34_AvoidCluster T {x} w).Infinite) :
    ∃ r : ℕ → Site d, r 0 = w ∧ Function.Injective r ∧
      (∀ k, T.Adj (r k) (r (k + 1))) ∧ (∀ k, r k ≠ x) ∧ (∃ k, r k ∈ vertexBoundary d R) :=
  bri_branchRay_reaches_boundary T (bfl_tree_le_lattice hT) hR hwx hw hinf

lemma bfl_treeRay_reaches_boundary {ω : ConfigSpace (Sym2 (Site d))} (T : SimpleGraph (Site d))
    [LocallyFinite T] (hT : T ≤ openSubgraph d ω) {w : Site d} {R : ℕ} (hR : 1 ≤ R)
    (hw : w ∈ box d R) (hinf : (ray34_AvoidCluster T ∅ w).Infinite) :
    ∃ r : ℕ → Site d, r 0 = w ∧ Function.Injective r ∧
      (∀ k, T.Adj (r k) (r (k + 1))) ∧ (∃ k, r k ∈ vertexBoundary d R) :=
  bri_treeRay_reaches_boundary T (bfl_tree_le_lattice hT) hR hw hinf

/-! ## B. Fine trifurcations -/

lemma bfl_fineTrif_iff_bc67_zero (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) :
    bft_FineTrif ω x ↔ bc67_IsGnTrifurcation ω 0 x := Iff.rfl

lemma bfl_fineCount_of_armSubforest (ω : ConfigSpace (Sym2 (Site 2))) (R : ℕ)
    (h : bau_ArmSubforestData ω 0 R) :
    bc61_coarseTcount ω 0 R ≤ boxSV_boundaryCard 2 R :=
  bca_datum_implies_count ω 0 R h

lemma bfl_status :
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) {T : SimpleGraph (Site 2)},
      T ≤ openSubgraph 2 ω → T ≤ hypercubicLattice 2) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (T : SimpleGraph (Site 2)) [LocallyFinite T],
      T ≤ openSubgraph 2 ω → ∀ {w x : Site 2} {R : ℕ}, 1 ≤ R → w ≠ x → w ∈ box 2 R →
      (ray34_AvoidCluster T {x} w).Infinite →
      ∃ r : ℕ → Site 2, r 0 = w ∧ Function.Injective r ∧
        (∀ k, T.Adj (r k) (r (k + 1))) ∧ (∀ k, r k ≠ x) ∧ (∃ k, r k ∈ vertexBoundary 2 R)) ∧
    (∀ {V : Type} {T : SimpleGraph V}, T.IsTree → ∀ {ι : Type} (Gs : ι → SimpleGraph V),
      (∀ i, Gs i ≤ T) → (⨆ i, Gs i).IsAcyclic) ∧
    (∃ (G T : SimpleGraph (Fin 4)) (_ : DecidableRel G.Adj) (_ : DecidableRel T.Adj)
      (B : Finset (Fin 4)),
      T ≤ G ∧ T.IsTree ∧ (∃ v, G.degree v = 2 ∧ T.degree v = 1 ∧ v ∉ B) ∧
      ¬ (∀ v, T.degree v = 1 → v ∈ B)) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (R : ℕ),
      bau_ArmSubforestData ω 0 R → bc61_coarseTcount ω 0 R ≤ boxSV_boundaryCard 2 R) ∧
    (∀ (p : ℝ≥0) (hp1 : p ≤ 1), 0 < p →
      (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bau_ArmSubforestData ω L R) →
      bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ω T hT; exact bfl_tree_le_lattice hT
  · intro ω T _ hT w x R hR hwx hw hinf; exact bfl_fineArm_reaches_boundary T hT hR hwx hw hinf
  · intro V T hT ι Gs hle; exact bri_union_le_acyclic hT Gs hle
  · exact bof2_interiorLeaf_obstruction
  · intro ω R h; exact bfl_fineCount_of_armSubforest ω R h
  · intro p hp1 hp0 hdata; exact StatMech.Walls.bau_bk_of_subforestData p hp1 hp0 hdata

end StatMech.Walls
