/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






























































import Mathlib
import Code.Walls.bc71spanningtree
import Code.Walls.bgnglobalcontract

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








theorem bcv_neighbor_of_walk {V : Type*} {K : SimpleGraph V} {x : V} :
    ∀ {a : V}, K.Walk a x → a ≠ x →
      ∃ w, K.Adj w x ∧ (bkg_deleteVertex K x).Reachable a w
  | _, SimpleGraph.Walk.nil, hax => absurd rfl hax
  | a, SimpleGraph.Walk.cons (v := b) h q, hax => by
      by_cases hbx : b = x
      · subst hbx
        exact ⟨a, h, SimpleGraph.Reachable.refl a⟩
      · obtain ⟨w, hwadj, hwreach⟩ := bcv_neighbor_of_walk q hbx
        have hstep : (bkg_deleteVertex K x).Adj a b := ⟨h, hax, hbx⟩
        exact ⟨w, hwadj, hstep.reachable.trans hwreach⟩



theorem bcv_deleteVertex_mono {V : Type*} {T H : SimpleGraph V} (hTH : T ≤ H) (x : V) :
    bkg_deleteVertex T x ≤ bkg_deleteVertex H x := by
  intro a b hab
  exact ⟨hTH hab.1, hab.2.1, hab.2.2⟩

















theorem bcv_degree_ge_components {V : Type*} [Fintype V] {H T : SimpleGraph V} [DecidableRel T.Adj]
    (hTH : T ≤ H) (hTconn : T.Connected) (x : V) {k : ℕ} (a : Fin k → V)
    (hne : ∀ i, a i ≠ x)
    (hsep : ∀ i j, i ≠ j → ¬ (bkg_deleteVertex H x).Reachable (a i) (a j)) :
    k ≤ T.degree x := by
  classical
  
  have harm : ∀ i, ∃ w, T.Adj w x ∧ (bkg_deleteVertex T x).Reachable (a i) w := by
    intro i
    obtain ⟨p⟩ := hTconn.preconnected (a i) x
    exact bcv_neighbor_of_walk p (hne i)
  choose w hwadj hwreach using harm
  
  have hmem : ∀ i, w i ∈ T.neighborFinset x := by
    intro i; rw [SimpleGraph.mem_neighborFinset]; exact (hwadj i).symm
  
  have hinj : Function.Injective w := by
    intro i j hij
    by_contra hne'
    
    have hreach_T : (bkg_deleteVertex T x).Reachable (a i) (a j) :=
      (hwreach i).trans (hij ▸ (hwreach j).symm)
    
    have hreach_H : (bkg_deleteVertex H x).Reachable (a i) (a j) :=
      hreach_T.mono (bcv_deleteVertex_mono hTH x)
    exact hsep i j hne' hreach_H
  
  calc k = (Finset.univ : Finset (Fin k)).card := by rw [Finset.card_univ, Fintype.card_fin]
    _ ≤ (T.neighborFinset x).card :=
        Finset.card_le_card_of_injOn w (fun i _ => hmem i) (fun i _ j _ h => hinj h)
    _ = T.degree x := SimpleGraph.card_neighborFinset_eq_degree T x





theorem bcv_spanningTree_degree_ge {V : Type*} [Fintype V] {H : SimpleGraph V}
    (hH : H.Connected) (x : V) {k : ℕ} (a : Fin k → V)
    (hne : ∀ i, a i ≠ x)
    (hsep : ∀ i j, i ≠ j → ¬ (bkg_deleteVertex H x).Reachable (a i) (a j)) :
    ∃ T : SimpleGraph V, T ≤ H ∧ T.IsTree ∧ (∀ (_ : DecidableRel T.Adj), k ≤ T.degree x) := by
  classical
  obtain ⟨T, hTH, hT⟩ := hH.exists_isTree_le
  refine ⟨T, hTH, hT, fun _ => ?_⟩
  exact bcv_degree_ge_components hTH hT.connected x a hne hsep


theorem bcv_sep3 {V : Type*} {K : SimpleGraph V} {b : Fin 3 → V}
    (h01 : ¬ K.Reachable (b 0) (b 1)) (h02 : ¬ K.Reachable (b 0) (b 2))
    (h12 : ¬ K.Reachable (b 1) (b 2)) :
    ∀ i j, i ≠ j → ¬ K.Reachable (b i) (b j) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first
      | exact absurd rfl hij
      | exact h01 | exact h02 | exact h12
      | exact fun h => h01 h.symm | exact fun h => h02 h.symm | exact fun h => h12 h.symm











theorem bcv_trif_degree_ge_three {V : Type*} [Fintype V] {H T : SimpleGraph V} [DecidableRel T.Adj]
    (hTH : T ≤ H) (hTconn : T.Connected) {x a₁ a₂ a₃ : V}
    (hne₁ : a₁ ≠ x) (hne₂ : a₂ ≠ x) (hne₃ : a₃ ≠ x)
    (hsep₁₂ : ¬ (bkg_deleteVertex H x).Reachable a₁ a₂)
    (hsep₁₃ : ¬ (bkg_deleteVertex H x).Reachable a₁ a₃)
    (hsep₂₃ : ¬ (bkg_deleteVertex H x).Reachable a₂ a₃) :
    3 ≤ T.degree x := by
  have h := bcv_degree_ge_components hTH hTconn x (![a₁, a₂, a₃] : Fin 3 → V)
    (by intro i; fin_cases i <;> assumption)
    (bcv_sep3 (b := ![a₁, a₂, a₃]) hsep₁₂ hsep₁₃ hsep₂₃)
  simpa using h

















theorem bcv_bgnW_test {T : SimpleGraph (Fin 8)} [DecidableRel T.Adj]
    (hTH : T ≤ bgn_W) (hTconn : T.Connected) :
    3 ≤ T.degree 0 ∧ 3 ≤ T.degree 1 := by
  obtain ⟨⟨_, _, _, h23, h26, h36⟩, ⟨_, _, _, h45, h46, h56⟩, _, _, _⟩ := bgn_crossing_witness
  refine ⟨?_, ?_⟩
  · exact bcv_trif_degree_ge_three hTH hTconn
      (by decide) (by decide) (by decide) h23 h26 h36
  · exact bcv_trif_degree_ge_three hTH hTconn
      (by decide) (by decide) (by decide) h45 h46 h56


theorem bcv_bgnW_connected : bgn_W.Connected := by decide






theorem bcv_bgnW_spanningTree_deg3 :
    ∃ T : SimpleGraph (Fin 8), T ≤ bgn_W ∧ T.IsTree ∧
      (∀ (_ : DecidableRel T.Adj), 3 ≤ T.degree 0 ∧ 3 ≤ T.degree 1) := by
  classical
  obtain ⟨T, hTH, hT⟩ := bcv_bgnW_connected.exists_isTree_le
  exact ⟨T, hTH, hT, fun _ => bcv_bgnW_test hTH hT.connected⟩




def bcv_T0 : SimpleGraph (Fin 8) :=
  SimpleGraph.fromEdgeSet {s(0,1), s(0,2), s(0,3), s(0,6), s(0,7), s(1,4), s(1,5)}

instance : DecidableRel bcv_T0.Adj := by unfold bcv_T0; infer_instance







theorem bcv_T0_witness :
    bcv_T0 ≤ bgn_W ∧ bcv_T0.Connected ∧ bcv_T0.degree 0 = 5 ∧ bcv_T0.degree 1 = 3 ∧
      3 ≤ bcv_T0.degree 0 ∧ 3 ≤ bcv_T0.degree 1 := by
  have hle : bcv_T0 ≤ bgn_W := by change ∀ a b, bcv_T0.Adj a b → bgn_W.Adj a b; decide
  have hconn : bcv_T0.Connected := by decide
  exact ⟨hle, hconn, by decide, by decide, (bcv_bgnW_test hle hconn).1, (bcv_bgnW_test hle hconn).2⟩
























def bcv_ClusterTreeData (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ) : Prop :=
  ∃ (S : Set (Site 2)) (_ : Fintype (↑S : Type)) (_ : Nonempty (↑S : Type))
    (H T : SimpleGraph (↑S : Type)) (_ : DecidableRel T.Adj) (ιU : Site 2 → (↑S : Type)),
    T ≤ H ∧ T.IsTree ∧ (∀ v, 1 ≤ T.degree v) ∧
    (∀ y, y ∈ box 2 R → bc67_IsGnTrifurcation ω L y →
      ∃ v₁ v₂ v₃ : (↑S : Type),
        v₁ ≠ ιU y ∧ v₂ ≠ ιU y ∧ v₃ ≠ ιU y ∧
        ¬ (bkg_deleteVertex H (ιU y)).Reachable v₁ v₂ ∧
        ¬ (bkg_deleteVertex H (ιU y)).Reachable v₁ v₃ ∧
        ¬ (bkg_deleteVertex H (ιU y)).Reachable v₂ v₃) ∧
    (∀ y, y ∈ box 2 R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box 2 R →
      bc67_IsGnTrifurcation ω L z → ιU y = ιU z → y = z) ∧
    (∀ v : (↑S : Type), T.degree v = 1 → (v : Site 2) ∈ vertexBoundary 2 R)






theorem bcv_globalForest_of_treeData (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ)
    (h : bcv_ClusterTreeData ω L R) : bc69_Gn_globalForest ω L R := by
  obtain ⟨S, hSfin, hSne, H, T, hTdec, ιU, hTH, hT, hmin, hsep, hιinj, hleaf⟩ := h
  refine ⟨S, hSfin, hSne, T, hTdec, ιU, hT.isAcyclic, hmin, ?_, hιinj, hleaf⟩
  
  intro y hybox htri
  obtain ⟨v₁, v₂, v₃, hn₁, hn₂, hn₃, hs₁₂, hs₁₃, hs₂₃⟩ := hsep y hybox htri
  exact bcv_trif_degree_ge_three hTH hT.connected hn₁ hn₂ hn₃ hs₁₂ hs₁₃ hs₂₃



theorem bcv_count_of_treeData (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ)
    (h : bcv_ClusterTreeData ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R :=
  bc69_count_via_leafBound ω L R (bcv_globalForest_of_treeData ω L R h)






theorem bcv_bk_of_treeData (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bcv_ClusterTreeData ω L R) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 := by
  apply bgn_bk_of_forest p hp1 hp0
  intro ω L R
  rw [bgn_forest_iff_bc69]
  exact bcv_globalForest_of_treeData ω L R (hdata ω L R)









































theorem bcv_status :
    
    (∀ {V : Type} [Fintype V] {H T : SimpleGraph V} [_i : DecidableRel T.Adj],
      T ≤ H → T.Connected → ∀ (x : V) {k : ℕ} (a : Fin k → V), (∀ i, a i ≠ x) →
      (∀ i j, i ≠ j → ¬ (bkg_deleteVertex H x).Reachable (a i) (a j)) → k ≤ T.degree x) ∧
    
    (∀ {V : Type} [Fintype V] {H T : SimpleGraph V} [_i : DecidableRel T.Adj],
      T ≤ H → T.Connected → ∀ {x a₁ a₂ a₃ : V}, a₁ ≠ x → a₂ ≠ x → a₃ ≠ x →
      ¬ (bkg_deleteVertex H x).Reachable a₁ a₂ → ¬ (bkg_deleteVertex H x).Reachable a₁ a₃ →
      ¬ (bkg_deleteVertex H x).Reachable a₂ a₃ → 3 ≤ T.degree x) ∧
    
    (∀ {T : SimpleGraph (Fin 8)} [_i : DecidableRel T.Adj], T ≤ bgn_W → T.Connected →
      3 ≤ T.degree 0 ∧ 3 ≤ T.degree 1) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ),
      bcv_ClusterTreeData ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro V _ H T _ hTH hTconn x k a hne hsep
    exact bcv_degree_ge_components hTH hTconn x a hne hsep
  · intro V _ H T _ hTH hTconn x a₁ a₂ a₃ h₁ h₂ h₃ hs₁₂ hs₁₃ hs₂₃
    exact bcv_trif_degree_ge_three hTH hTconn h₁ h₂ h₃ hs₁₂ hs₁₃ hs₂₃
  · intro T _ hTH hTconn
    exact bcv_bgnW_test hTH hTconn
  · intro ω L R h
    exact bcv_count_of_treeData ω L R h

end StatMech.Walls
