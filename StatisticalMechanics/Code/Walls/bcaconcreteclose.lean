/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















































import Mathlib
import Code.Walls.bauacyclicarm
import Code.Walls.bcvcutvertex

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






theorem bca_bk_of_subforestData (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bau_ArmSubforestData ω L R) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 :=
  bau_bk_of_subforestData p hp1 hp0 hdata

















theorem bca_datum_implies_count (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ)
    (h : bau_ArmSubforestData ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R :=
  bc69_count_via_leafBound ω L R (bau_bc69_of_subforestData ω L R h)




theorem bca_datum_implies_globalForest (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ)
    (h : bau_ArmSubforestData ω L R) : bc69_Gn_globalForest ω L R :=
  bau_bc69_of_subforestData ω L R h










theorem bca_fieldB_free {V : Type*} {H : SimpleGraph V} (hH : H.Connected) :
    ∃ T : SimpleGraph V, T ≤ H ∧ T.IsTree :=
  bau_exists_spanningTree_infinite hH




theorem bca_fieldC_free {V : Type*} {T G : SimpleGraph V} (hT : T.IsTree) (hle : G ≤ T) :
    G.IsAcyclic :=
  bau_isAcyclic_of_le_tree hT hle





theorem bca_fieldD_free {V : Type*} [Fintype V] {H T : SimpleGraph V} [DecidableRel T.Adj]
    (hTH : T ≤ H) (hTconn : T.Connected) {x a₁ a₂ a₃ : V}
    (hne₁ : a₁ ≠ x) (hne₂ : a₂ ≠ x) (hne₃ : a₃ ≠ x)
    (hsep₁₂ : ¬ (bkg_deleteVertex H x).Reachable a₁ a₂)
    (hsep₁₃ : ¬ (bkg_deleteVertex H x).Reachable a₁ a₃)
    (hsep₂₃ : ¬ (bkg_deleteVertex H x).Reachable a₂ a₃) :
    3 ≤ T.degree x :=
  bcv_trif_degree_ge_three hTH hTconn hne₁ hne₂ hne₃ hsep₁₂ hsep₁₃ hsep₂₃







theorem bca_star_witness :
    bau_star.IsTree ∧ bau_star.IsAcyclic ∧ bau_star.degree 0 = 3 ∧
    bau_star.degree 1 = 1 ∧ bau_star.degree 2 = 1 ∧ bau_star.degree 3 = 1 :=
  bau_star_witness










































theorem bca_status :
    
    (∀ (p : ℝ≥0) (hp1 : p ≤ 1), 0 < p →
      (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bau_ArmSubforestData ω L R) →
      bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ),
      bau_ArmSubforestData ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R) ∧
    
    (∀ {V : Type} {H : SimpleGraph V}, H.Connected → ∃ T : SimpleGraph V, T ≤ H ∧ T.IsTree) ∧
    
    (∀ {V : Type} {T G : SimpleGraph V}, T.IsTree → G ≤ T → G.IsAcyclic) ∧
    
    (bau_star.IsTree ∧ bau_star.IsAcyclic ∧ bau_star.degree 0 = 3) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p hp1 hp0 hdata; exact bca_bk_of_subforestData p hp1 hp0 hdata
  · intro ω L R h; exact bca_datum_implies_count ω L R h
  · intro V H hH; exact bca_fieldB_free hH
  · intro V T G hT hle; exact bca_fieldC_free hT hle
  · exact ⟨bca_star_witness.1, bca_star_witness.2.1, bca_star_witness.2.2.1⟩

end StatMech.Walls
