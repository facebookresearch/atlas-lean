/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/















































import Mathlib
import Code.Walls.bof2leafcount

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








theorem blf_leaf_of_interiorDeg2 {V : Type*} [Fintype V] [DecidableEq V]
    {F : SimpleGraph V} [DecidableRel F.Adj] {B : V → Prop}
    (h2 : ∀ v, ¬ B v → 2 ≤ F.degree v) :
    ∀ v, F.degree v = 1 → B v := by
  intro v hv
  by_contra hB
  have := h2 v hB
  omega













theorem blf_bc69_of_interiorDeg2 {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (S : Set (Site d)) (hSfin : Fintype (↑S : Type)) (hSne : Nonempty (↑S : Type))
    (G : SimpleGraph (↑S : Type)) (hGdec : DecidableRel G.Adj) (ιU : Site d → (↑S : Type))
    (hac : G.IsAcyclic) (hmin : ∀ v, 1 ≤ G.degree v)
    (hdeg3 : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → 3 ≤ G.degree (ιU y))
    (hinj : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box d R →
      bc67_IsGnTrifurcation ω L z → ιU y = ιU z → y = z)
    (hint : ∀ v : (↑S : Type), ((v : Site d) ∉ vertexBoundary d R) → 2 ≤ G.degree v) :
    bc69_Gn_globalForest ω L R := by
  refine ⟨S, hSfin, hSne, G, hGdec, ιU, hac, hmin, hdeg3, hinj, ?_⟩
  intro v hv
  by_contra hvb
  have := hint v hvb
  omega








def blf_AcyclicArmUnion (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ) : Prop :=
  ∃ (S : Set (Site 2)) (_ : Fintype (↑S : Type)) (_ : Nonempty (↑S : Type))
    (G : SimpleGraph (↑S : Type)) (_ : DecidableRel G.Adj) (ιU : Site 2 → (↑S : Type)),
    G.IsAcyclic ∧ (∀ v, 1 ≤ G.degree v) ∧
    (∀ y, y ∈ box 2 R → bc67_IsGnTrifurcation ω L y → 3 ≤ G.degree (ιU y)) ∧
    (∀ y, y ∈ box 2 R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box 2 R →
      bc67_IsGnTrifurcation ω L z → ιU y = ιU z → y = z) ∧
    (∀ v : (↑S : Type), ((v : Site 2) ∉ vertexBoundary 2 R) → 2 ≤ G.degree v)


theorem blf_bc69_of_acyclicArmUnion (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ)
    (h : blf_AcyclicArmUnion ω L R) : bc69_Gn_globalForest ω L R := by
  obtain ⟨S, hSfin, hSne, G, hGdec, ιU, hac, hmin, hdeg3, hinj, hint⟩ := h
  exact blf_bc69_of_interiorDeg2 ω L R S hSfin hSne G hGdec ιU hac hmin hdeg3 hinj hint






theorem blf_bk_of_acyclicArmUnion (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), blf_AcyclicArmUnion ω L R) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 := by
  apply bgn_bk_of_forest p hp1 hp0
  intro ω L R
  rw [bgn_forest_iff_bc69]
  exact blf_bc69_of_acyclicArmUnion ω L R (hdata ω L R)
















def blf_pathG : SimpleGraph (Fin 3) := SimpleGraph.fromEdgeSet {s(0,1), s(1,2)}

instance : DecidableRel blf_pathG.Adj := by unfold blf_pathG; infer_instance





theorem blf_acyclic_closes_witness :
    blf_pathG.degree 0 = 1 ∧ blf_pathG.degree 1 = 2 ∧ blf_pathG.degree 2 = 1 ∧
    (∀ v : Fin 3, blf_pathG.degree v = 1 → (v = 0 ∨ v = 2)) := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  exact blf_leaf_of_interiorDeg2 (B := fun v => v = 0 ∨ v = 2)
    (by intro v hv; fin_cases v <;> first | exact absurd (by decide) hv | decide)







theorem blf_interiorCycle_obstructs :
    bof2_advT ≤ bof2_advG ∧ bof2_advT.IsAcyclic ∧
    bof2_advG.degree 2 = 2 ∧ bof2_advT.degree 2 = 1 ∧ (2 : Fin 4) ∉ ({0} : Finset (Fin 4)) := by
  have hle : bof2_advT ≤ bof2_advG := by
    change ∀ a b, bof2_advT.Adj a b → bof2_advG.Adj a b; decide
  have htree : bof2_advT.IsTree := by
    rw [isTree_iff_connected_and_card]
    refine ⟨by decide, ?_⟩
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
    decide
  exact ⟨hle, htree.isAcyclic, by decide, by decide, by decide⟩




































theorem blf_status :
    
    (∀ {V : Type} [Fintype V] [DecidableEq V] {F : SimpleGraph V} [_i : DecidableRel F.Adj]
      {B : V → Prop}, (∀ v, ¬ B v → 2 ≤ F.degree v) → ∀ v, F.degree v = 1 → B v) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ),
      blf_AcyclicArmUnion ω L R → bc69_Gn_globalForest ω L R) ∧
    
    (∀ (p : ℝ≥0) (hp1 : p ≤ 1), 0 < p →
      (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), blf_AcyclicArmUnion ω L R) →
      bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0) ∧
    
    (bof2_advT ≤ bof2_advG ∧ bof2_advT.IsAcyclic ∧
      bof2_advG.degree 2 = 2 ∧ bof2_advT.degree 2 = 1 ∧ (2 : Fin 4) ∉ ({0} : Finset (Fin 4))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro V _ _ F _ B h2; exact blf_leaf_of_interiorDeg2 h2
  · intro ω L R h; exact blf_bc69_of_acyclicArmUnion ω L R h
  · intro p hp1 hp0 hdata; exact blf_bk_of_acyclicArmUnion p hp1 hp0 hdata
  · exact blf_interiorCycle_obstructs

end StatMech.Walls
