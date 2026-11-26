/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Order.Filter.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TreeCutVertex

/-!
# The handshake bound for trees and its limits

In a finite tree, branch vertices are at most leaves; injectively placed cut vertices with three
separated neighbours are therefore at most the leaves, and small examples show what can fail.

## i. Overview

The handshake lemma gives `#{deg ≥ 3} ≤ #{deg = 1}` in a finite tree. If a spanning tree of `H`
contains injectively placed vertices each separating three neighbours in `H`, they are at most the
number of leaves, hence at most any set containing the leaves. The four-vertex examples `bof2_advG`
and `bof2_advT` show that a leaf of the tree can be an interior vertex of the ambient graph, so
leaves need not lie on the boundary.

## ii. Key results

- `bof2_forest_handshake` : branch vertices are at most leaves in a finite tree
- `bof2_trifCount_le_boundary` : separating vertices in a spanning tree are at most the leaves
- `bof2_interiorLeaf_obstruction` : a tree leaf can be an interior vertex
- `bof2_status` : the statements together

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
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

/-! ## A. Results -/

lemma bof2_forest_handshake {V : Type*} [Fintype V] [DecidableEq V] {T : SimpleGraph V}
    [DecidableRel T.Adj] (hT : T.IsTree) :
    (Finset.univ.filter (fun v => 3 ≤ T.degree v)).card ≤
      (Finset.univ.filter (fun v => T.degree v = 1)).card := by
  classical
  set A : ℤ := ((Finset.univ.filter (fun v => T.degree v = 0)).card : ℤ) with hA
  set B : ℤ := ((Finset.univ.filter (fun v => T.degree v = 1)).card : ℤ) with hB
  set D : ℤ := ((Finset.univ.filter (fun v => 3 ≤ T.degree v)).card : ℤ) with hD
  have hedge : T.edgeFinset.card + 1 = Fintype.card V := hT.card_edgeFinset
  have hsumdeg : (∑ v, (T.degree v : ℤ)) = 2 * (Fintype.card V : ℤ) - 2 := by
    have h1 : (∑ v, T.degree v) = 2 * T.edgeFinset.card :=
      T.sum_degrees_eq_twice_card_edges
    have h2 : (∑ v, (T.degree v : ℤ)) = 2 * (T.edgeFinset.card : ℤ) := by
      have := congrArg (Nat.cast : ℕ → ℤ) h1
      push_cast at this ⊢
      linarith [this]
    have h3 : (T.edgeFinset.card : ℤ) + 1 = (Fintype.card V : ℤ) := by exact_mod_cast hedge
    rw [h2]; linarith
  have hpt : ∀ v : V, (2 : ℤ) - (T.degree v : ℤ) ≤
      2 * (if T.degree v = 0 then (1 : ℤ) else 0)
        + (if T.degree v = 1 then (1 : ℤ) else 0)
        - (if 3 ≤ T.degree v then (1 : ℤ) else 0) := by
    intro v
    rcases Nat.lt_or_ge (T.degree v) 3 with h | h
    · rw [ite_eq_right (show ¬ 3 ≤ T.degree v by omega)]
      rcases Nat.eq_zero_or_pos (T.degree v) with h0 | h0
      · rw [ite_eq_left h0, ite_eq_right (show ¬ T.degree v = 1 by omega), h0]; norm_num
      · rcases Nat.lt_or_ge (T.degree v) 2 with h1 | h1
        · have he : T.degree v = 1 := by omega
          rw [ite_eq_right (show ¬ T.degree v = 0 by omega), ite_eq_left he, he]; norm_num
        · have he : T.degree v = 2 := by omega
          rw [ite_eq_right (show ¬ T.degree v = 0 by omega),
              ite_eq_right (show ¬ T.degree v = 1 by omega), he]; norm_num
    · rw [ite_eq_left h, ite_eq_right (show ¬ T.degree v = 0 by omega),
          ite_eq_right (show ¬ T.degree v = 1 by omega)]
      have : (3 : ℤ) ≤ (T.degree v : ℤ) := by exact_mod_cast h
      linarith
  have hsum := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset V)) => hpt v)
  have hLHS : (∑ v, ((2 : ℤ) - (T.degree v : ℤ))) = 2 := by
    rw [Finset.sum_sub_distrib, hsumdeg]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  have hRHS : (∑ v, (2 * (if T.degree v = 0 then (1 : ℤ) else 0)
        + (if T.degree v = 1 then (1 : ℤ) else 0)
        - (if 3 ≤ T.degree v then (1 : ℤ) else 0))) = 2 * A + B - D := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [Finset.sum_boole, Finset.sum_boole, Finset.sum_boole]
  rw [hLHS, hRHS] at hsum
  rcases Nat.lt_or_ge (Fintype.card V) 2 with hcard | hcard
  · have hDeg0 : ∀ v : V, T.degree v < 3 := by
      intro v
      have : T.degree v ≤ Fintype.card V - 1 := by
        have := T.degree_lt_card_verts v
        omega
      omega
    have : (Finset.univ.filter (fun v => 3 ≤ T.degree v)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro v _; exact Nat.not_le.mpr (hDeg0 v)
    rw [this]; simp
  · have hA0 : A = 0 := by
      rw [hA]
      have : (Finset.univ.filter (fun v => T.degree v = 0)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro v _
        obtain ⟨w, hw⟩ : ∃ w, w ≠ v := by
          by_contra hcon
          push Not at hcon
          have : Fintype.card V ≤ 1 := Fintype.card_le_one_iff.mpr (fun a b => (hcon a).trans (hcon b).symm)
          omega
        obtain ⟨p⟩ := hT.connected.preconnected v w
        have hpos : 0 < T.degree v := by
          rcases p with _ | @⟨_, b, _, hvb, q⟩
          · exact absurd rfl (Ne.symm hw)
          · exact hvb.degree_pos_left
        omega
      rw [this]; simp
    have hDle : D ≤ B := by rw [hA0] at hsum; linarith
    rw [hD, hB] at hDle
    exact_mod_cast hDle

lemma bof2_trifCount_le_boundary {V : Type*} [Fintype V] [DecidableEq V]
    {H T : SimpleGraph V} [DecidableRel T.Adj]
    (hTH : T ≤ H) (hT : T.IsTree)
    {ι : Type*} [Fintype ι] (f : ι → V) (hf : Function.Injective f)
    (hcut : ∀ i, ∃ a₁ a₂ a₃ : V, a₁ ≠ f i ∧ a₂ ≠ f i ∧ a₃ ≠ f i ∧
        ¬ (bkg_deleteVertex H (f i)).Reachable a₁ a₂ ∧
        ¬ (bkg_deleteVertex H (f i)).Reachable a₁ a₃ ∧
        ¬ (bkg_deleteVertex H (f i)).Reachable a₂ a₃)
    (B : Finset V) (hleaf : ∀ v, T.degree v = 1 → v ∈ B) :
    Fintype.card ι ≤ B.card := by
  classical
  have hbranch : Finset.univ.image f ⊆ Finset.univ.filter (fun v => 3 ≤ T.degree v) := by
    intro v hv
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hv
    obtain ⟨i, rfl⟩ := hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    obtain ⟨a₁, a₂, a₃, h1, h2, h3, s12, s13, s23⟩ := hcut i
    exact bcv_trif_degree_ge_three hTH hT.connected h1 h2 h3 s12 s13 s23
  calc Fintype.card ι = (Finset.univ.image f).card := by
          rw [Finset.card_image_of_injective _ hf, Finset.card_univ]
    _ ≤ (Finset.univ.filter (fun v => 3 ≤ T.degree v)).card := Finset.card_le_card hbranch
    _ ≤ (Finset.univ.filter (fun v => T.degree v = 1)).card := bof2_forest_handshake hT
    _ ≤ B.card := by
          apply Finset.card_le_card
          intro v hv
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
          exact hleaf v hv

lemma bof2_bgnW_handshake_witness :
    (Finset.univ.filter (fun v => 3 ≤ bcv_T0.degree v)).card = 2 ∧
    (Finset.univ.filter (fun v => bcv_T0.degree v = 1)).card = 6 ∧
    (Finset.univ.filter (fun v => 3 ≤ bcv_T0.degree v)).card ≤
      (Finset.univ.filter (fun v => bcv_T0.degree v = 1)).card :=
  ⟨by decide, by decide, by decide⟩

lemma bof2_bgnW_handshake_applies :
    (Finset.univ.filter (fun v => 3 ≤ bcv_T0.degree v)).card ≤
      (Finset.univ.filter (fun v => bcv_T0.degree v = 1)).card := by
  have hconn : bcv_T0.Connected := by decide
  have htree : bcv_T0.IsTree := by
    rw [isTree_iff_connected_and_card]
    refine ⟨hconn, ?_⟩
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
        ← SimpleGraph.edgeFinset_card]
    decide
  exact bof2_forest_handshake htree

/-- A four-vertex graph: a triangle `1 2 3` with a pendant vertex `0`. -/
def bof2_advG : SimpleGraph (Fin 4) :=
  SimpleGraph.fromEdgeSet {s(0,1), s(1,2), s(2,3), s(3,1)}

/-- Adjacency in the four-vertex example graph is decidable. -/
instance : DecidableRel bof2_advG.Adj := by unfold bof2_advG; infer_instance

/-- A spanning tree of `bof2_advG`: the star at `1`. -/
def bof2_advT : SimpleGraph (Fin 4) :=
  SimpleGraph.fromEdgeSet {s(0,1), s(1,2), s(3,1)}

/-- Adjacency in the example spanning tree is decidable. -/
instance : DecidableRel bof2_advT.Adj := by unfold bof2_advT; infer_instance

lemma bof2_interiorLeaf_witness :
    bof2_advT ≤ bof2_advG ∧
    bof2_advG.degree 2 = 2 ∧
    bof2_advT.degree 2 = 1 ∧
    (2 : Fin 4) ∉ ({0} : Finset (Fin 4)) := by
  refine ⟨?_, by decide, by decide, by decide⟩
  change ∀ a b, bof2_advT.Adj a b → bof2_advG.Adj a b; decide

lemma bof2_interiorLeaf_obstruction :
    ∃ (G T : SimpleGraph (Fin 4)) (_ : DecidableRel G.Adj) (_ : DecidableRel T.Adj)
      (B : Finset (Fin 4)),
      T ≤ G ∧ T.IsTree ∧
      (∃ v, G.degree v = 2 ∧ T.degree v = 1 ∧ v ∉ B) ∧
      ¬ (∀ v, T.degree v = 1 → v ∈ B) := by
  refine ⟨bof2_advG, bof2_advT, inferInstance, inferInstance, {0}, ?_, ?_,
    ⟨2, by decide, by decide, by decide⟩, ?_⟩
  · change ∀ a b, bof2_advT.Adj a b → bof2_advG.Adj a b; decide
  · rw [isTree_iff_connected_and_card]
    refine ⟨by decide, ?_⟩
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
    decide
  · intro hall
    have := hall 2 (by decide)
    revert this; decide

/-! ## B. Summary -/

lemma bof2_status :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {T : SimpleGraph V} [_i : DecidableRel T.Adj],
      T.IsTree →
      (Finset.univ.filter (fun v => 3 ≤ T.degree v)).card ≤
        (Finset.univ.filter (fun v => T.degree v = 1)).card) ∧
    (∀ {V : Type} [Fintype V] [DecidableEq V] {H T : SimpleGraph V} [_i : DecidableRel T.Adj],
      T ≤ H → T.IsTree → ∀ {ι : Type} [Fintype ι] (f : ι → V), Function.Injective f →
      (∀ i, ∃ a₁ a₂ a₃ : V, a₁ ≠ f i ∧ a₂ ≠ f i ∧ a₃ ≠ f i ∧
        ¬ (bkg_deleteVertex H (f i)).Reachable a₁ a₂ ∧
        ¬ (bkg_deleteVertex H (f i)).Reachable a₁ a₃ ∧
        ¬ (bkg_deleteVertex H (f i)).Reachable a₂ a₃) →
      ∀ (B : Finset V), (∀ v, T.degree v = 1 → v ∈ B) → Fintype.card ι ≤ B.card) ∧
    (∃ (G T : SimpleGraph (Fin 4)) (_ : DecidableRel G.Adj) (_ : DecidableRel T.Adj)
      (B : Finset (Fin 4)),
      T ≤ G ∧ T.IsTree ∧ (∃ v, G.degree v = 2 ∧ T.degree v = 1 ∧ v ∉ B) ∧
      ¬ (∀ v, T.degree v = 1 → v ∈ B)) ∧
    (∀ (p : ℝ≥0) (hp1 : p ≤ 1), 0 < p →
      (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bcv_ClusterTreeData ω L R) →
      bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro V _ _ T _ hT; exact bof2_forest_handshake hT
  · intro V _ _ H T _ hTH hT ι _ f hf hcut B hleaf
    exact bof2_trifCount_le_boundary hTH hT f hf hcut B hleaf
  · exact bof2_interiorLeaf_obstruction
  · intro p hp1 hp0 hdata; exact bcv_bk_of_treeData p hp1 hp0 hdata

end StatMech.Walls
