/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















































import Mathlib
import Code.Walls.briraysintree
import Code.Walls.bcvcutvertex
import Code.Walls.bauacyclicarm

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







private theorem bsg_ediv_succ_bounds (q m : ℤ) (hq : 0 < q) :
    m / q ≤ (m + 1) / q ∧ (m + 1) / q ≤ m / q + 1 := by
  refine ⟨Int.ediv_le_ediv hq (by omega), ?_⟩
  have hstep : (m + 1) / q ≤ (m + 1 * q) / q :=
    Int.ediv_le_ediv hq (by nlinarith)
  rwa [Int.add_mul_ediv_right _ _ (by omega : q ≠ 0)] at hstep


private theorem bsg_idxCoord_shift_le (L : ℕ) (c s : ℤ) (hs : s = 1 ∨ s = -1) :
    ((c + L) / (2 * (L : ℤ) + 1) - (c + s + L) / (2 * (L : ℤ) + 1)).natAbs ≤ 1 := by
  have hq : (0 : ℤ) < 2 * (L : ℤ) + 1 := by positivity
  rcases hs with rfl | rfl
  · 
    have h := bsg_ediv_succ_bounds (2 * (L : ℤ) + 1) (c + L) hq
    have e1 : c + 1 + (L : ℤ) = (c + L) + 1 := by ring
    rw [e1]
    omega
  · 
    have h := bsg_ediv_succ_bounds (2 * (L : ℤ) + 1) (c + (-1) + L) hq
    have e1 : (c + (-1) + L) + 1 = c + (L : ℤ) := by ring
    rw [e1] at h
    omega







theorem bsg_Gn_le_lattice (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) :
    bgn_Gn ω L ≤ hypercubicLattice d := by
  intro j k hjk
  obtain ⟨hne, a, b, ha, hb, hab⟩ := hjk
  
  have hnn : NearestNeighbour d a b := (openSubgraph_adj ω a b).mp hab |>.1
  rw [nearestNeighbour_iff_shift] at hnn
  obtain ⟨t, s, hs, hbshift⟩ := hnn
  
  have hcoord : ∀ i, (j i - k i).natAbs ≤ (if i = t then 1 else 0) := by
    intro i
    by_cases hit : i = t
    · rw [if_pos hit]
      have hbi : b i = a i + s := by
        rw [hbshift, hit, Lattice.shift, Function.update_self]
      have hji : j i = (a i + L) / (2 * (L : ℤ) + 1) := by rw [← ha]; rfl
      have hki : k i = (a i + s + L) / (2 * (L : ℤ) + 1) := by
        rw [← hb]; show (b i + L) / (2 * (L : ℤ) + 1) = _; rw [hbi]
      rw [hji, hki]
      exact bsg_idxCoord_shift_le L (a i) s hs
    · rw [if_neg hit]
      have hbi : b i = a i := by rw [hbshift, Lattice.shift, Function.update_of_ne hit]
      have hji : j i = (a i + L) / (2 * (L : ℤ) + 1) := by rw [← ha]; rfl
      have hki : k i = (a i + L) / (2 * (L : ℤ) + 1) := by
        rw [← hb]; show (b i + L) / (2 * (L : ℤ) + 1) = _; rw [hbi]
      rw [hji, hki]; simp
  
  rw [hypercubicLattice_adj]
  set S := (∑ i, (j i - k i).natAbs) with hS
  have hsum_le : S ≤ 1 := by
    rw [hS]
    calc (∑ i, (j i - k i).natAbs) ≤ ∑ i, (if i = t then 1 else 0) :=
          Finset.sum_le_sum (fun i _ => hcoord i)
      _ = 1 := by simp
  have hsum_pos : 1 ≤ S := by
    rcases Nat.eq_zero_or_pos S with h0 | hpos
    · exfalso
      apply hne
      funext i
      have hle : (j i - k i).natAbs ≤ S :=
        Finset.single_le_sum (f := fun i => (j i - k i).natAbs)
          (fun i _ => Nat.zero_le _) (Finset.mem_univ i)
      have : (j i - k i).natAbs = 0 := by omega
      omega
    · exact hpos
  omega

#check @bsg_Gn_le_lattice













theorem bsg_GnTreeRay_reaches_boundary (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ)
    (T : SimpleGraph (Site d)) [LocallyFinite T] (hT : T ≤ bgn_Gn ω L)
    {w : Site d} {R : ℕ} (hR : 1 ≤ R) (hw : w ∈ box d R)
    (hinf : (ray34_AvoidCluster T ∅ w).Infinite) :
    ∃ r : ℕ → Site d, r 0 = w ∧ Function.Injective r ∧
      (∀ k, T.Adj (r k) (r (k + 1))) ∧ (∃ k, r k ∈ vertexBoundary d R) :=
  bri_treeRay_reaches_boundary T (le_trans hT (bsg_Gn_le_lattice ω L)) hR hw hinf





theorem bsg_GnBranchRay_reaches_boundary (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ)
    (T : SimpleGraph (Site d)) [LocallyFinite T] (hT : T ≤ bgn_Gn ω L)
    {w x : Site d} {R : ℕ} (hR : 1 ≤ R) (hwx : w ≠ x) (hw : w ∈ box d R)
    (hinf : (ray34_AvoidCluster T {x} w).Infinite) :
    ∃ r : ℕ → Site d, r 0 = w ∧ Function.Injective r ∧
      (∀ k, T.Adj (r k) (r (k + 1))) ∧ (∀ k, r k ≠ x) ∧ (∃ k, r k ∈ vertexBoundary d R) :=
  bri_branchRay_reaches_boundary T (le_trans hT (bsg_Gn_le_lattice ω L)) hR hwx hw hinf














theorem bsg_hub_degree_ge_three {V : Type*} [Fintype V] {H T : SimpleGraph V} [DecidableRel T.Adj]
    (hTH : T ≤ H) (hTconn : T.Connected) {x a₁ a₂ a₃ : V}
    (hne₁ : a₁ ≠ x) (hne₂ : a₂ ≠ x) (hne₃ : a₃ ≠ x)
    (hsep₁₂ : ¬ (bkg_deleteVertex H x).Reachable a₁ a₂)
    (hsep₁₃ : ¬ (bkg_deleteVertex H x).Reachable a₁ a₃)
    (hsep₂₃ : ¬ (bkg_deleteVertex H x).Reachable a₂ a₃) :
    3 ≤ T.degree x :=
  bcv_trif_degree_ge_three hTH hTconn hne₁ hne₂ hne₃ hsep₁₂ hsep₁₃ hsep₂₃






theorem bsg_bgnW_hubs_deg3 {T : SimpleGraph (Fin 8)} [DecidableRel T.Adj]
    (hTH : T ≤ bgn_W) (hTconn : T.Connected) :
    3 ≤ T.degree 0 ∧ 3 ≤ T.degree 1 :=
  bcv_bgnW_test hTH hTconn




theorem bsg_bgnW_spanningTree_exists :
    ∃ T : SimpleGraph (Fin 8), T ≤ bgn_W ∧ T.IsTree ∧
      (∀ (_ : DecidableRel T.Adj), 3 ≤ T.degree 0 ∧ 3 ≤ T.degree 1) :=
  bcv_bgnW_spanningTree_deg3










theorem bsg_rayUnion_acyclic {V : Type*} {T : SimpleGraph V} (hT : T.IsTree)
    {ι : Type*} (Gs : ι → SimpleGraph V) (hGs : ∀ i, Gs i ≤ T) :
    (⨆ i, Gs i).IsAcyclic :=
  bri_union_le_acyclic hT Gs hGs





theorem bsg_bk_of_treeData (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bcv_ClusterTreeData ω L R) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 :=
  bcv_bk_of_treeData p hp1 hp0 hdata



theorem bsg_bk_of_subforestData (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bau_ArmSubforestData ω L R) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 :=
  bau_bk_of_subforestData p hp1 hp0 hdata












theorem bsg_datum_implies_count (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ)
    (h : bau_ArmSubforestData ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R :=
  bca_datum_implies_count ω L R h













theorem bsg_twoHub_witness :
    bri_twoHub.IsTree ∧ bri_twoHub.degree 0 = 3 ∧ bri_twoHub.degree 1 = 3 ∧
      bri_twoHub.degree 4 = 2 ∧
      (∀ v : Fin 7, v ∉ ({2, 3, 5, 6} : Finset (Fin 7)) → 2 ≤ bri_twoHub.degree v) :=
  ⟨bri_twoHub_witness.1, bri_twoHub_witness.2.2.1, bri_twoHub_witness.2.2.2.1,
    bri_twoHub_witness.2.2.2.2.1, bri_twoHub_witness.2.2.2.2.2.2.2.2.2⟩









































theorem bsg_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ), bgn_Gn ω L ≤ hypercubicLattice 2) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (T : SimpleGraph (Site 2)) [LocallyFinite T],
      T ≤ bgn_Gn ω L → ∀ {w : Site 2} {R : ℕ}, 1 ≤ R → w ∈ box 2 R →
        (ray34_AvoidCluster T ∅ w).Infinite →
        ∃ r : ℕ → Site 2, r 0 = w ∧ Function.Injective r ∧
          (∀ k, T.Adj (r k) (r (k + 1))) ∧ (∃ k, r k ∈ vertexBoundary 2 R)) ∧
    
    (∀ {T : SimpleGraph (Fin 8)} [_i : DecidableRel T.Adj], T ≤ bgn_W → T.Connected →
      3 ≤ T.degree 0 ∧ 3 ≤ T.degree 1) ∧
    
    (∀ {V : Type} {T : SimpleGraph V}, T.IsTree → ∀ {ι : Type} (Gs : ι → SimpleGraph V),
      (∀ i, Gs i ≤ T) → (⨆ i, Gs i).IsAcyclic) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ),
      bau_ArmSubforestData ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R) ∧
    
    (∀ (p : ℝ≥0) (hp1 : p ≤ 1), 0 < p →
      (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bau_ArmSubforestData ω L R) →
      bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ω L; exact bsg_Gn_le_lattice ω L
  · intro ω L T _ hT w R hR hw hinf; exact bsg_GnTreeRay_reaches_boundary ω L T hT hR hw hinf
  · intro T _ hTH hTconn; exact bsg_bgnW_hubs_deg3 hTH hTconn
  · intro V T hT ι Gs hGs; exact bsg_rayUnion_acyclic hT Gs hGs
  · intro ω L R h; exact bsg_datum_implies_count ω L R h
  · intro p hp1 hp0 hdata; exact bsg_bk_of_subforestData p hp1 hp0 hdata

end StatMech.Walls


#print axioms StatMech.Walls.bsg_Gn_le_lattice
#print axioms StatMech.Walls.bsg_GnTreeRay_reaches_boundary
#print axioms StatMech.Walls.bsg_bk_of_subforestData
#print axioms StatMech.Walls.bsg_status
