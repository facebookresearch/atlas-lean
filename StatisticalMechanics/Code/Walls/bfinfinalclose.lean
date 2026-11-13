/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















































import Mathlib
import Code.Walls.bsgspantreegn
import Code.Walls.bcaconcreteclose

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






theorem bfin_bk_of_subforestData (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bau_ArmSubforestData ω L R) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 :=
  bau_bk_of_subforestData p hp1 hp0 hdata

#check @bfin_bk_of_subforestData









theorem bfin_acyclic_free {V : Type*} {T G : SimpleGraph V} (hT : T.IsAcyclic) (hle : G ≤ T) :
    G.IsAcyclic :=
  bau_isAcyclic_of_le_acyclic hT hle





theorem bfin_GnBranchRay_reaches_boundary {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ)
    (T : SimpleGraph (Site d)) [LocallyFinite T] (hT : T ≤ bgn_Gn ω L)
    {w x : Site d} {R : ℕ} (hR : 1 ≤ R) (hwx : w ≠ x) (hw : w ∈ box d R)
    (hinf : (ray34_AvoidCluster T {x} w).Infinite) :
    ∃ r : ℕ → Site d, r 0 = w ∧ Function.Injective r ∧
      (∀ k, T.Adj (r k) (r (k + 1))) ∧ (∀ k, r k ≠ x) ∧ (∃ k, r k ∈ vertexBoundary d R) :=
  bsg_GnBranchRay_reaches_boundary ω L T hT hR hwx hw hinf





theorem bfin_Gn_le_lattice {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) :
    bgn_Gn ω L ≤ hypercubicLattice d :=
  bsg_Gn_le_lattice ω L











theorem bfin_datum_implies_count (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ)
    (h : bau_ArmSubforestData ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R :=
  bca_datum_implies_count ω L R h


















theorem bfin_datum_of_noTrif (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ) (hR : 1 ≤ R)
    (hno : ∀ y, y ∈ box 2 R → ¬ bc67_IsGnTrifurcation ω L y) :
    bau_ArmSubforestData ω L R := by
  classical
  set p : Site 2 := ![(R:ℤ), 0] with hp
  set q : Site 2 := ![(-(R:ℤ)), 0] with hq
  have hpq : p ≠ q := by
    intro h; have := congrFun h 0; simp only [hp, hq, Matrix.cons_val_zero] at this; omega
  have hpbd : p ∈ vertexBoundary 2 R := by
    refine ⟨?_, ?_⟩
    · intro i; fin_cases i <;> simp [hp, Int.natAbs_natCast]
    · intro h; have := h 0; simp only [hp, Matrix.cons_val_zero, Int.natAbs_natCast] at this; omega
  have hqbd : q ∈ vertexBoundary 2 R := by
    refine ⟨?_, ?_⟩
    · intro i; fin_cases i <;> simp [hq, Int.natAbs_neg, Int.natAbs_natCast]
    · intro h; have := h 0; simp only [hq, Matrix.cons_val_zero, Int.natAbs_neg, Int.natAbs_natCast] at this; omega
  set S : Set (Site 2) := {p, q} with hS
  have hSfin : Fintype ↑S := ((Set.finite_singleton q).insert p).fintype
  have hpS : p ∈ S := by left; rfl
  have hqS : q ∈ S := by right; rfl
  have hSne : Nonempty ↑S := ⟨⟨p, hpS⟩⟩
  have hmemBd : ∀ v : ↑S, (v : Site 2) ∈ vertexBoundary 2 R := by
    rintro ⟨v, hv⟩
    rcases hv with hvp | hvq
    · simpa [hvp] using hpbd
    · simp only [Set.mem_singleton_iff] at hvq; simpa [hvq] using hqbd
  refine ⟨S, hSfin, hSne, (⊤ : SimpleGraph ↑S), (⊤ : SimpleGraph ↑S), (⊤ : SimpleGraph ↑S),
    (inferInstance : DecidableRel (⊤ : SimpleGraph ↑S).Adj), (fun _ => ⟨p, hpS⟩),
    connected_top, le_rfl, ⟨connected_top, ?_⟩, le_rfl, ?_, ?_, ?_, ?_⟩
  · 
    apply IsAcyclic.of_card_le_two
    rw [ENat.card_coe_set_eq, hS, Set.encard_pair hpq]
  · 
    intro v
    obtain ⟨w, hw⟩ : ∃ w : ↑S, (⊤ : SimpleGraph ↑S).Adj v w := by
      rcases v with ⟨v, hv⟩
      rcases hv with hvp | hvq
      · exact ⟨⟨q, hqS⟩, by rw [SimpleGraph.top_adj]; intro h; apply hpq; rw [← hvp]; exact congrArg Subtype.val h⟩
      · simp only [Set.mem_singleton_iff] at hvq
        exact ⟨⟨p, hpS⟩, by rw [SimpleGraph.top_adj]; intro h; apply hpq; rw [← hvq]; exact (congrArg Subtype.val h).symm⟩
    have hne : ((⊤ : SimpleGraph ↑S).neighborFinset v).Nonempty :=
      ⟨w, (SimpleGraph.mem_neighborFinset _ _ _).mpr hw⟩
    exact Finset.Nonempty.card_pos hne
  · 
    intro y hy htri; exact absurd htri (hno y hy)
  · 
    intro y hy htri; exact absurd htri (hno y hy)
  · 
    intro v hv; exact absurd (hmemBd v) hv

#check @bfin_datum_of_noTrif















def bfin_SuperCutBridge (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) : Prop :=
  ∀ y : Site 2, bc67_IsGnTrifurcation ω L y →
    ∃ w₁ w₂ w₃ : Site 2,
      w₁ ≠ bgn_idx L y ∧ w₂ ≠ bgn_idx L y ∧ w₃ ≠ bgn_idx L y ∧
      (bgn_Gn ω L).Adj (bgn_idx L y) w₁ ∧ (bgn_Gn ω L).Adj (bgn_idx L y) w₂ ∧
      (bgn_Gn ω L).Adj (bgn_idx L y) w₃ ∧
      ¬ (bkg_deleteVertex (bgn_Gn ω L) (bgn_idx L y)).Reachable w₁ w₂ ∧
      ¬ (bkg_deleteVertex (bgn_Gn ω L) (bgn_idx L y)).Reachable w₁ w₃ ∧
      ¬ (bkg_deleteVertex (bgn_Gn ω L) (bgn_idx L y)).Reachable w₂ w₃ ∧
      (ray34_AvoidCluster (bgn_Gn ω L) {bgn_idx L y} w₁).Infinite ∧
      (ray34_AvoidCluster (bgn_Gn ω L) {bgn_idx L y} w₂).Infinite ∧
      (ray34_AvoidCluster (bgn_Gn ω L) {bgn_idx L y} w₃).Infinite








def bfin_GlobalArmForest (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ) : Prop :=
  bau_ArmSubforestData ω L R



theorem bfin_bk_of_globalArmForest (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bfin_GlobalArmForest ω L R) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 :=
  bfin_bk_of_subforestData p hp1 hp0 hdata














































theorem bfin_status :
    
    (∀ (p : ℝ≥0) (hp1 : p ≤ 1), 0 < p →
      (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bau_ArmSubforestData ω L R) →
      bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0) ∧
    
    (∀ {V : Type} {T G : SimpleGraph V}, T.IsAcyclic → G ≤ T → G.IsAcyclic) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), 1 ≤ R →
      (∀ y, y ∈ box 2 R → ¬ bc67_IsGnTrifurcation ω L y) → bau_ArmSubforestData ω L R) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ),
      bau_ArmSubforestData ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp1 hp0 hdata; exact bfin_bk_of_subforestData p hp1 hp0 hdata
  · intro V T G hT hle; exact bfin_acyclic_free hT hle
  · intro ω L R hR hno; exact bfin_datum_of_noTrif ω L R hR hno
  · intro ω L R h; exact bfin_datum_implies_count ω L R h

end StatMech.Walls


#print axioms StatMech.Walls.bfin_bk_of_subforestData
#print axioms StatMech.Walls.bfin_datum_of_noTrif
#print axioms StatMech.Walls.bfin_datum_implies_count
#print axioms StatMech.Walls.bfin_status
