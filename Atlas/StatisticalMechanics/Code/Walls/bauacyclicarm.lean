/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

























































import Mathlib
import Code.Walls.blfboundaryleaf

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







theorem bau_isAcyclic_of_le_tree {V : Type*} {T G : SimpleGraph V}
    (hT : T.IsTree) (hle : G ≤ T) : G.IsAcyclic :=
  hT.isAcyclic.anti hle


theorem bau_isAcyclic_of_le_acyclic {V : Type*} {T G : SimpleGraph V}
    (hT : T.IsAcyclic) (hle : G ≤ T) : G.IsAcyclic :=
  hT.anti hle










theorem bau_exists_spanningTree_infinite {V : Type*} {H : SimpleGraph V} (hH : H.Connected) :
    ∃ T : SimpleGraph V, T ≤ H ∧ T.IsTree := by
  obtain ⟨T, hle, hT⟩ := hH.exists_isTree_le
  exact ⟨T, hle, hT⟩



theorem bau_armUnion_acyclic_of_spanningTree {V : Type*} {H G : SimpleGraph V} (hH : H.Connected)
    (T : SimpleGraph V) (hTH : T ≤ H) (hT : T.IsTree) (hle : G ≤ T) : G.IsAcyclic :=
  bau_isAcyclic_of_le_tree hT hle













def bau_ArmSubforestData (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ) : Prop :=
  ∃ (S : Set (Site 2)) (_ : Fintype (↑S : Type)) (_ : Nonempty (↑S : Type))
    (H T G : SimpleGraph (↑S : Type)) (_ : DecidableRel G.Adj) (ιU : Site 2 → (↑S : Type)),
    H.Connected ∧ T ≤ H ∧ T.IsTree ∧ G ≤ T ∧
    (∀ v, 1 ≤ G.degree v) ∧
    (∀ y, y ∈ box 2 R → bc67_IsGnTrifurcation ω L y → 3 ≤ G.degree (ιU y)) ∧
    (∀ y, y ∈ box 2 R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box 2 R →
      bc67_IsGnTrifurcation ω L z → ιU y = ιU z → y = z) ∧
    (∀ v : (↑S : Type), ((v : Site 2) ∉ vertexBoundary 2 R) → 2 ≤ G.degree v)





theorem bau_blf_of_subforestData (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ)
    (h : bau_ArmSubforestData ω L R) : blf_AcyclicArmUnion ω L R := by
  obtain ⟨S, hSfin, hSne, H, T, G, hGdec, ιU, hHconn, hTH, hT, hle, hmin, hdeg3, hinj, hint⟩ := h
  exact ⟨S, hSfin, hSne, G, hGdec, ιU, bau_isAcyclic_of_le_tree hT hle, hmin, hdeg3, hinj, hint⟩



theorem bau_bc69_of_subforestData (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ)
    (h : bau_ArmSubforestData ω L R) : bc69_Gn_globalForest ω L R :=
  blf_bc69_of_acyclicArmUnion ω L R (bau_blf_of_subforestData ω L R h)





theorem bau_bk_of_subforestData (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bau_ArmSubforestData ω L R) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 := by
  apply blf_bk_of_acyclicArmUnion p hp1 hp0
  intro ω L R
  exact bau_blf_of_subforestData ω L R (hdata ω L R)










def bau_star : SimpleGraph (Fin 4) := SimpleGraph.fromEdgeSet {s(0,1), s(0,2), s(0,3)}

instance : DecidableRel bau_star.Adj := by unfold bau_star; infer_instance






theorem bau_star_witness :
    bau_star.IsTree ∧ bau_star.IsAcyclic ∧
    bau_star.degree 0 = 3 ∧ bau_star.degree 1 = 1 ∧ bau_star.degree 2 = 1 ∧ bau_star.degree 3 = 1 := by
  have htree : bau_star.IsTree := by
    rw [isTree_iff_connected_and_card]
    refine ⟨by decide, ?_⟩
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
    decide
  refine ⟨htree, bau_isAcyclic_of_le_tree htree le_rfl, by decide, by decide, by decide, by decide⟩




def bau_sub : SimpleGraph (Fin 4) := SimpleGraph.fromEdgeSet {s(0,1), s(0,2)}

instance : DecidableRel bau_sub.Adj := by unfold bau_sub; infer_instance

theorem bau_sub_witness :
    bau_sub ≤ bau_star ∧ bau_sub ≠ bau_star ∧ bau_sub.IsAcyclic := by
  have hle : bau_sub ≤ bau_star := by
    change ∀ a b, bau_sub.Adj a b → bau_star.Adj a b; decide
  refine ⟨hle, ?_, ?_⟩
  · intro h
    have : bau_star.Adj 0 3 := by decide
    rw [← h] at this
    exact absurd this (by decide)
  · exact bau_isAcyclic_of_le_tree bau_star_witness.1 hle















































theorem bau_status :
    
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
  · intro V H hH; exact bau_exists_spanningTree_infinite hH
  · intro ω L R h; exact bau_blf_of_subforestData ω L R h
  · intro p hp1 hp0 hdata; exact bau_bk_of_subforestData p hp1 hp0 hdata
  · exact ⟨bau_star_witness.1, bau_star_witness.2.1, bau_star_witness.2.2.1⟩

end StatMech.Walls
