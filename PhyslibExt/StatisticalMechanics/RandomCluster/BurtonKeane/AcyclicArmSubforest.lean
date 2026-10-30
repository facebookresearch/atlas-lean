/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.InteriorArmBoundaryLeaf

/-!
# Arm subforests of a spanning tree

A subgraph of a tree or of an acyclic graph is acyclic; the arm subforest datum built from a
spanning tree gives the planar coarse forest and the Burton–Keane count.

## i. Overview

Every connected graph has a spanning tree, and every subgraph of a tree is acyclic. The datum
`bau_ArmSubforestData ω L R` asks for a finite vertex set carrying a connected graph `H`, a spanning
tree `T ≤ H` and an arm union `G ≤ T` with the leaf and degree properties used by the coarse count.
It gives the acyclic arm union `blf_AcyclicArmUnion`, the global forest `bc69_Gn_globalForest` and,
for every configuration, Burton–Keane uniqueness on `ℤ²`. A star on four vertices and a subgraph of
it check the definitions.

## ii. Key results

- `bau_armUnion_acyclic_of_spanningTree` : an arm union inside a spanning tree is acyclic.
- `bau_bc69_of_subforestData` : the global forest from the arm subforest datum.
- `bau_bk_of_subforestData` : uniqueness on `ℤ²` from the datum for every configuration.

## iii. Table of contents

- A. Subgraphs of trees
- B. The arm subforest datum
- C. A star example

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

/-! ## A. Subgraphs of trees -/

lemma bau_isAcyclic_of_le_tree {V : Type*} {T G : SimpleGraph V}
    (hT : T.IsTree) (hle : G ≤ T) : G.IsAcyclic :=
  hT.isAcyclic.anti hle

lemma bau_isAcyclic_of_le_acyclic {V : Type*} {T G : SimpleGraph V}
    (hT : T.IsAcyclic) (hle : G ≤ T) : G.IsAcyclic :=
  hT.anti hle

lemma bau_armUnion_acyclic_of_spanningTree {V : Type*} {H G : SimpleGraph V} (_hH : H.Connected)
    (T : SimpleGraph V) (_hTH : T ≤ H) (hT : T.IsTree) (hle : G ≤ T) : G.IsAcyclic :=
  bau_isAcyclic_of_le_tree hT hle

/-! ## B. The arm subforest datum -/

/-- Arm subforest datum for the planar box of radius `R` at scale `L`: a finite vertex set with a
connected graph `H`, a spanning tree `T ≤ H` and an arm union `G ≤ T`, whose leaves lie on the
boundary and whose coarse trifurcations have degree at least three. -/
def bau_ArmSubforestData (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ) : Prop :=
  ∃ (S : Set (Site 2)) (_ : Fintype (↑S : Type)) (_ : Nonempty (↑S : Type))
    (H T G : SimpleGraph (↑S : Type)) (_ : DecidableRel G.Adj) (ιU : Site 2 → (↑S : Type)),
    H.Connected ∧ T ≤ H ∧ T.IsTree ∧ G ≤ T ∧
    (∀ v, 1 ≤ G.degree v) ∧
    (∀ y, y ∈ box 2 R → bc67_IsGnTrifurcation ω L y → 3 ≤ G.degree (ιU y)) ∧
    (∀ y, y ∈ box 2 R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box 2 R →
      bc67_IsGnTrifurcation ω L z → ιU y = ιU z → y = z) ∧
    (∀ v : (↑S : Type), ((v : Site 2) ∉ vertexBoundary 2 R) → 2 ≤ G.degree v)

lemma bau_blf_of_subforestData (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ)
    (h : bau_ArmSubforestData ω L R) : blf_AcyclicArmUnion ω L R := by
  obtain ⟨S, hSfin, hSne, H, T, G, hGdec, ιU, hHconn, hTH, hT, hle, hmin, hdeg3, hinj, hint⟩ := h
  exact ⟨S, hSfin, hSne, G, hGdec, ιU, bau_isAcyclic_of_le_tree hT hle, hmin, hdeg3, hinj, hint⟩

lemma bau_bc69_of_subforestData (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ)
    (h : bau_ArmSubforestData ω L R) : bc69_Gn_globalForest ω L R :=
  blf_bc69_of_acyclicArmUnion ω L R (bau_blf_of_subforestData ω L R h)

lemma bau_bk_of_subforestData (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bau_ArmSubforestData ω L R) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 := by
  apply blf_bk_of_acyclicArmUnion p hp1 hp0
  intro ω L R
  exact bau_blf_of_subforestData ω L R (hdata ω L R)

/-! ## C. A star example -/

/-- The star on `Fin 4` with centre `0`. -/
def bau_star : SimpleGraph (Fin 4) := SimpleGraph.fromEdgeSet {s(0,1), s(0,2), s(0,3)}

/-- Adjacency in `bau_star` is decidable. -/
instance : DecidableRel bau_star.Adj := by unfold bau_star; infer_instance

lemma bau_star_witness :
    bau_star.IsTree ∧ bau_star.IsAcyclic ∧
    bau_star.degree 0 = 3 ∧ bau_star.degree 1 = 1 ∧ bau_star.degree 2 = 1 ∧ bau_star.degree 3 =
        1 := by
  have htree : bau_star.IsTree := by
    rw [isTree_iff_connected_and_card]
    refine ⟨by decide, ?_⟩
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
    decide
  refine ⟨htree, bau_isAcyclic_of_le_tree htree le_rfl, by decide, by decide, by decide, by decide⟩

/-- The subgraph of `bau_star` keeping the edges to `1` and `2`. -/
def bau_sub : SimpleGraph (Fin 4) := SimpleGraph.fromEdgeSet {s(0,1), s(0,2)}

/-- Adjacency in `bau_sub` is decidable. -/
instance : DecidableRel bau_sub.Adj := by unfold bau_sub; infer_instance

lemma bau_sub_witness :
    bau_sub ≤ bau_star ∧ bau_sub ≠ bau_star ∧ bau_sub.IsAcyclic := by
  have hle : bau_sub ≤ bau_star := by
    change ∀ a b, bau_sub.Adj a b → bau_star.Adj a b; decide
  refine ⟨hle, ?_, ?_⟩
  · intro h
    have : bau_star.Adj 0 3 := by decide
    rw [← h] at this
    exact absurd this (by decide)
  · exact bau_isAcyclic_of_le_tree bau_star_witness.1 hle

lemma bau_status :
    (∀ {V : Type} {T G : SimpleGraph V}, T.IsTree → G ≤ T → G.IsAcyclic) ∧
    (∀ {V : Type} {H : SimpleGraph V}, H.Connected → ∃ T : SimpleGraph V, T ≤ H ∧ T.IsTree) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ),
      bau_ArmSubforestData ω L R → blf_AcyclicArmUnion ω L R) ∧
    (∀ (p : ℝ≥0) (hp1 : p ≤ 1), 0 < p →
      (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bau_ArmSubforestData ω L R) →
      bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0) ∧
    (bau_star.IsTree ∧ bau_star.IsAcyclic ∧ bau_star.degree 0 = 3) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro V T G hT hle; exact bau_isAcyclic_of_le_tree hT hle
  · intro V H hH; exact SimpleGraph.Connected.exists_isTree_le hH
  · intro ω L R h; exact bau_blf_of_subforestData ω L R h
  · intro p hp1 hp0 hdata; exact bau_bk_of_subforestData p hp1 hp0 hdata
  · exact ⟨bau_star_witness.1, bau_star_witness.2.1, bau_star_witness.2.2.1⟩

end StatMech.Walls
