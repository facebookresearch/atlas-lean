/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


























































import Mathlib
import Code.Walls.bcaconcreteclose
import Code.Walls.bararmray

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

variable {d : ℕ}













theorem bri_treeRay_of_infiniteComponent {V : Type*} [DecidableEq V] (T : SimpleGraph V)
    [LocallyFinite T] {w : V} (hinf : (ray34_AvoidCluster T ∅ w).Infinite) :
    ∃ r : ℕ → V, r 0 = w ∧ Function.Injective r ∧ (∀ k, T.Adj (r k) (r (k + 1))) := by
  obtain ⟨r, hr0, hinj, hadj, -⟩ := ray34_konig T (Set.notMem_empty w) hinf
  exact ⟨r, hr0, hinj, hadj⟩






theorem bri_branchRay_avoiding_vertex {V : Type*} [DecidableEq V] (T : SimpleGraph V)
    [LocallyFinite T] {w x : V} (hwx : w ≠ x)
    (hinf : (ray34_AvoidCluster T {x} w).Infinite) :
    ∃ r : ℕ → V, r 0 = w ∧ Function.Injective r ∧
      (∀ k, T.Adj (r k) (r (k + 1))) ∧ (∀ k, r k ≠ x) := by
  have hw : w ∉ ({x} : Set V) := by simpa using hwx
  obtain ⟨r, hr0, hinj, hadj, havoid⟩ := ray34_konig T hw hinf
  exact ⟨r, hr0, hinj, hadj, fun k => by have := havoid k; simpa using this⟩








theorem bri_treeRay_reaches_boundary (T : SimpleGraph (Site d)) [LocallyFinite T]
    (hle : T ≤ hypercubicLattice d) {w : Site d} {R : ℕ} (hR : 1 ≤ R) (hw : w ∈ box d R)
    (hinf : (ray34_AvoidCluster T ∅ w).Infinite) :
    ∃ r : ℕ → Site d, r 0 = w ∧ Function.Injective r ∧
      (∀ k, T.Adj (r k) (r (k + 1))) ∧ (∃ k, r k ∈ vertexBoundary d R) := by
  obtain ⟨r, hr0, hinj, hadj⟩ := bri_treeRay_of_infiniteComponent T hinf
  have hlat : ∀ k, (hypercubicLattice d).Adj (r k) (r (k + 1)) := fun k => hle (hadj k)
  have h0box : r 0 ∈ box d R := by rw [hr0]; exact hw
  obtain ⟨k, hk⟩ := bar_ray_crosses_boundary r hinj hlat R hR h0box
  exact ⟨r, hr0, hinj, hadj, ⟨k, hk⟩⟩





theorem bri_branchRay_reaches_boundary (T : SimpleGraph (Site d)) [LocallyFinite T]
    (hle : T ≤ hypercubicLattice d) {w x : Site d} {R : ℕ} (hR : 1 ≤ R) (hwx : w ≠ x)
    (hw : w ∈ box d R) (hinf : (ray34_AvoidCluster T {x} w).Infinite) :
    ∃ r : ℕ → Site d, r 0 = w ∧ Function.Injective r ∧
      (∀ k, T.Adj (r k) (r (k + 1))) ∧ (∀ k, r k ≠ x) ∧ (∃ k, r k ∈ vertexBoundary d R) := by
  obtain ⟨r, hr0, hinj, hadj, havoid⟩ := bri_branchRay_avoiding_vertex T hwx hinf
  have hlat : ∀ k, (hypercubicLattice d).Adj (r k) (r (k + 1)) := fun k => hle (hadj k)
  have h0box : r 0 ∈ box d R := by rw [hr0]; exact hw
  obtain ⟨k, hk⟩ := bar_ray_crosses_boundary r hinj hlat R hR h0box
  exact ⟨r, hr0, hinj, hadj, havoid, ⟨k, hk⟩⟩

#check @bri_treeRay_reaches_boundary
#check @bri_branchRay_reaches_boundary








def bri_rayEdges {V : Type*} (r : ℕ → V) (N : ℕ) : Set (Sym2 V) :=
  {e | ∃ k < N, e = s(r k, r (k + 1))}


def bri_rayGraph {V : Type*} (r : ℕ → V) (N : ℕ) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (bri_rayEdges r N)




theorem bri_rayGraph_le {V : Type*} (T : SimpleGraph V) (r : ℕ → V) (N : ℕ)
    (hadj : ∀ k, T.Adj (r k) (r (k + 1))) : bri_rayGraph r N ≤ T := by
  intro a b hab
  rw [bri_rayGraph, SimpleGraph.fromEdgeSet_adj] at hab
  obtain ⟨⟨k, hk, hek⟩, hne⟩ := hab
  rw [Sym2.eq_iff] at hek
  rcases hek with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hadj k
  · exact (hadj k).symm



theorem bri_rayGraph_acyclic {V : Type*} {T : SimpleGraph V} (hT : T.IsTree) (r : ℕ → V) (N : ℕ)
    (hadj : ∀ k, T.Adj (r k) (r (k + 1))) : (bri_rayGraph r N).IsAcyclic :=
  bau_isAcyclic_of_le_tree hT (bri_rayGraph_le T r N hadj)





theorem bri_union_le_acyclic {V : Type*} {T : SimpleGraph V} (hT : T.IsTree)
    {ι : Type*} (Gs : ι → SimpleGraph V) (hGs : ∀ i, Gs i ≤ T) :
    (⨆ i, Gs i).IsAcyclic :=
  bau_isAcyclic_of_le_tree hT (iSup_le hGs)



theorem bri_two_rays_acyclic {V : Type*} {T : SimpleGraph V} (hT : T.IsTree) (r s : ℕ → V) (N M : ℕ)
    (hr : ∀ k, T.Adj (r k) (r (k + 1))) (hs : ∀ k, T.Adj (s k) (s (k + 1))) :
    (bri_rayGraph r N ⊔ bri_rayGraph s M).IsAcyclic :=
  bau_isAcyclic_of_le_tree hT (sup_le (bri_rayGraph_le T r N hr) (bri_rayGraph_le T s M hs))














def bri_twoHub : SimpleGraph (Fin 7) :=
  SimpleGraph.fromEdgeSet {s(0,2), s(0,3), s(0,4), s(1,5), s(1,6), s(1,4)}

instance : DecidableRel bri_twoHub.Adj := by unfold bri_twoHub; infer_instance







theorem bri_twoHub_witness :
    bri_twoHub.IsTree ∧ bri_twoHub.IsAcyclic ∧
    bri_twoHub.degree 0 = 3 ∧ bri_twoHub.degree 1 = 3 ∧ bri_twoHub.degree 4 = 2 ∧
    bri_twoHub.degree 2 = 1 ∧ bri_twoHub.degree 3 = 1 ∧
    bri_twoHub.degree 5 = 1 ∧ bri_twoHub.degree 6 = 1 ∧
    (∀ v : Fin 7, v ∉ ({2, 3, 5, 6} : Finset (Fin 7)) → 2 ≤ bri_twoHub.degree v) := by
  have htree : bri_twoHub.IsTree := by
    rw [isTree_iff_connected_and_card]
    refine ⟨by decide, ?_⟩
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
    decide
  refine ⟨htree, bau_isAcyclic_of_le_tree htree le_rfl, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, ?_⟩
  intro v hv; fin_cases v <;> first | (exfalso; exact hv (by decide)) | decide





theorem bri_twoHub_count :
    ({0, 1} : Finset (Fin 7)).card ≤ ({2, 3, 5, 6} : Finset (Fin 7)).card := by decide

#check @bri_rayGraph_le
#check @bri_union_le_acyclic
#check bri_twoHub_witness










theorem bri_bk_of_subforestData (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bau_ArmSubforestData ω L R) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 :=
  bau_bk_of_subforestData p hp1 hp0 hdata




theorem bri_datum_implies_count (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ)
    (h : bau_ArmSubforestData ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R :=
  bca_datum_implies_count ω L R h













































theorem bri_status :
    
    (∀ (T : SimpleGraph (Site 2)) [LocallyFinite T], T ≤ hypercubicLattice 2 →
      ∀ {w x : Site 2} {R : ℕ}, 1 ≤ R → w ≠ x → w ∈ box 2 R →
        (ray34_AvoidCluster T {x} w).Infinite →
        ∃ r : ℕ → Site 2, r 0 = w ∧ Function.Injective r ∧
          (∀ k, T.Adj (r k) (r (k + 1))) ∧ (∀ k, r k ≠ x) ∧
          (∃ k, r k ∈ vertexBoundary 2 R)) ∧
    
    (∀ {V : Type} {T : SimpleGraph V}, T.IsTree → ∀ {ι : Type} (Gs : ι → SimpleGraph V),
      (∀ i, Gs i ≤ T) → (⨆ i, Gs i).IsAcyclic) ∧
    
    (bri_twoHub.IsTree ∧ bri_twoHub.degree 0 = 3 ∧ bri_twoHub.degree 1 = 3 ∧
      bri_twoHub.degree 4 = 2 ∧
      (∀ v : Fin 7, v ∉ ({2, 3, 5, 6} : Finset (Fin 7)) → 2 ≤ bri_twoHub.degree v)) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ),
      bau_ArmSubforestData ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R) ∧
    
    (∀ (p : ℝ≥0) (hp1 : p ≤ 1), 0 < p →
      (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bau_ArmSubforestData ω L R) →
      bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro T _ hle w x R hR hwx hw hinf
    exact bri_branchRay_reaches_boundary T hle hR hwx hw hinf
  · intro V T hT ι Gs hGs; exact bri_union_le_acyclic hT Gs hGs
  · exact ⟨bri_twoHub_witness.1, bri_twoHub_witness.2.2.1, bri_twoHub_witness.2.2.2.1,
      bri_twoHub_witness.2.2.2.2.1, bri_twoHub_witness.2.2.2.2.2.2.2.2.2⟩
  · intro ω L R h; exact bri_datum_implies_count ω L R h
  · intro p hp1 hp0 hdata; exact bri_bk_of_subforestData p hp1 hp0 hdata

end StatMech.Walls
