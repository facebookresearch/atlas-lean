/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




























































import Mathlib
import Code.Walls.bflleafclose
import Code.Walls.bcaconcreteclose
import Code.Percolation.ForestLeafCountClose

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












theorem bfk_forestHandshake {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hacyc : G.IsAcyclic) (hmin : ∀ v, 1 ≤ G.degree v) :
    (Finset.univ.filter (fun v => 3 ≤ G.degree v)).card
      ≤ (Finset.univ.filter (fun v => G.degree v = 1)).card :=
  flc2_forest_internal_le_leaves G hacyc hmin















theorem bfk_forestCount {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hacyc : G.IsAcyclic) (hmin : ∀ v, 1 ≤ G.degree v)
    {ι : Type*} [Fintype ι] (f : ι → V) (hf : Function.Injective f)
    (hdeg3 : ∀ i, 3 ≤ G.degree (f i))
    (B : Finset V) (hleaf : ∀ v, G.degree v = 1 → v ∈ B) :
    Fintype.card ι ≤ B.card := by
  classical
  have hbranch : Finset.univ.image f ⊆ Finset.univ.filter (fun v => 3 ≤ G.degree v) := by
    intro v hv
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hv
    obtain ⟨i, rfl⟩ := hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hdeg3 i
  calc Fintype.card ι = (Finset.univ.image f).card := by
          rw [Finset.card_image_of_injective _ hf, Finset.card_univ]
    _ ≤ (Finset.univ.filter (fun v => 3 ≤ G.degree v)).card := Finset.card_le_card hbranch
    _ ≤ (Finset.univ.filter (fun v => G.degree v = 1)).card := bfk_forestHandshake G hacyc hmin
    _ ≤ B.card := by
          apply Finset.card_le_card
          intro v hv
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
          exact hleaf v hv








theorem bfk_armForest_acyclic {V : Type*} {T : SimpleGraph V} (hT : T.IsTree)
    {ι : Type*} (Gs : ι → SimpleGraph V) (hle : ∀ i, Gs i ≤ T) :
    (⨆ i, Gs i).IsAcyclic :=
  bfl_armUnion_acyclic hT Gs hle





theorem bfk_armRay_reaches_boundary {ω : ConfigSpace (Sym2 (Site d))} (T : SimpleGraph (Site d))
    [LocallyFinite T] (hT : T ≤ openSubgraph d ω) {w x : Site d} {R : ℕ} (hR : 1 ≤ R) (hwx : w ≠ x)
    (hw : w ∈ box d R) (hinf : (ray34_AvoidCluster T {x} w).Infinite) :
    ∃ r : ℕ → Site d, r 0 = w ∧ Function.Injective r ∧
      (∀ k, T.Adj (r k) (r (k + 1))) ∧ (∀ k, r k ≠ x) ∧ (∃ k, r k ∈ vertexBoundary d R) :=
  bfl_fineArm_reaches_boundary T hT hR hwx hw hinf












theorem bfk_star_count_witness :
    Fintype.card (Fin 1) ≤ ({1, 2, 3} : Finset (Fin 4)).card := by
  refine bfk_forestCount bau_star bau_star_witness.1.isAcyclic ?_
    (fun _ => (0 : Fin 4)) ?_ ?_ {1, 2, 3} ?_
  · decide
  · intro a b _; exact Subsingleton.elim a b
  · intro i; exact (by decide : (3 : ℕ) ≤ bau_star.degree 0)
  · decide




















theorem bfk_datum_implies_count (ω : ConfigSpace (Sym2 (Site 2))) (R : ℕ)
    (h : bau_ArmSubforestData ω 0 R) :
    bc61_coarseTcount ω 0 R ≤ boxSV_boundaryCard 2 R :=
  bca_datum_implies_count ω 0 R h





theorem bfk_bk_of_datum (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bau_ArmSubforestData ω L R) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 :=
  bau_bk_of_subforestData p hp1 hp0 hdata














































theorem bfk_forestCount_status :
    
    (∀ {V : Type} [Fintype V] [Nonempty V] {G : SimpleGraph V} [_i : DecidableRel G.Adj],
      G.IsAcyclic → (∀ v, 1 ≤ G.degree v) →
      (Finset.univ.filter (fun v => 3 ≤ G.degree v)).card
        ≤ (Finset.univ.filter (fun v => G.degree v = 1)).card) ∧
    
    (∀ {V : Type} [Fintype V] [Nonempty V] {G : SimpleGraph V} [_i : DecidableRel G.Adj],
      G.IsAcyclic → (∀ v, 1 ≤ G.degree v) →
      ∀ {ι : Type} [Fintype ι] (f : ι → V), Function.Injective f → (∀ i, 3 ≤ G.degree (f i)) →
      ∀ (B : Finset V), (∀ v, G.degree v = 1 → v ∈ B) → Fintype.card ι ≤ B.card) ∧
    
    (∀ {V : Type} {T : SimpleGraph V}, T.IsTree → ∀ {ι : Type} (Gs : ι → SimpleGraph V),
      (∀ i, Gs i ≤ T) → (⨆ i, Gs i).IsAcyclic) ∧
    
    (Fintype.card (Fin 1) ≤ ({1, 2, 3} : Finset (Fin 4)).card) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (R : ℕ),
      bau_ArmSubforestData ω 0 R → bc61_coarseTcount ω 0 R ≤ boxSV_boundaryCard 2 R) ∧
    
    (∀ (p : ℝ≥0) (hp1 : p ≤ 1), 0 < p →
      (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bau_ArmSubforestData ω L R) →
      bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro V _ _ G _ hacyc hmin; exact bfk_forestHandshake G hacyc hmin
  · intro V _ _ G _ hacyc hmin ι _ f hf hdeg3 B hleaf
    exact bfk_forestCount G hacyc hmin f hf hdeg3 B hleaf
  · intro V T hT ι Gs hle; exact bfk_armForest_acyclic hT Gs hle
  · exact bfk_star_count_witness
  · intro ω R h; exact bfk_datum_implies_count ω R h
  · intro p hp1 hp0 hdata; exact bfk_bk_of_datum p hp1 hp0 hdata

end StatMech.Walls
