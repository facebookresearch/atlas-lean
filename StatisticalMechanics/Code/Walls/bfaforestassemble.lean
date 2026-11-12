/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













import Mathlib
import Code.Walls.bkgclassicalforest
import Code.Walls.bskspanningtree
import Code.Walls.bgctrifgraph
import Code.Walls.bc70globalforest

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












theorem bfa_notin_support_of_isolated {V : Type*} {H : SimpleGraph V} {t : V}
    (hiso : ∀ z, ¬ H.Adj t z) : ∀ {a b : V} (w : H.Walk a b), a ≠ t → t ∉ w.support := by
  intro a b w
  induction w with
  | nil => intro ha; simp only [SimpleGraph.Walk.support_nil, List.mem_singleton]; exact fun h => ha h.symm
  | @cons a v b hav w ih =>
    intro ha
    have hv : v ≠ t := fun hvt => hiso a (hvt ▸ hav.symm)
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons, not_or]
    exact ⟨fun h => ha h.symm, ih hv⟩




theorem bfa_singleVertexCut_of_acyclic {V : Type*} (G : SimpleGraph V) (hG : G.IsAcyclic)
    (t a b : V) (hta : G.Adj t a) (htb : G.Adj t b) (hab : a ≠ b) :
    ¬ (bkg_deleteVertex G t).Reachable a b := by
  classical
  rintro ⟨w⟩
  have hle : bkg_deleteVertex G t ≤ G := fun x y h => h.1
  
  have hiso : ∀ z, ¬ (bkg_deleteVertex G t).Adj t z := fun z h => h.2.1 rfl
  have hane : a ≠ t := (hta.symm).ne
  have hnotinW : t ∉ w.support := bfa_notin_support_of_isolated hiso w hane
  
  have hnotin : t ∉ (w.mapLe hle).support := by
    rw [SimpleGraph.Walk.support_mapLe_eq_support hle w]; exact hnotinW
  
  set p : G.Path a b := (w.mapLe hle).toPath with hp
  have hp_notin : t ∉ (p.1).support :=
    fun hmem => hnotin (SimpleGraph.Walk.support_toPath_subset _ hmem)
  
  have hbne : t ≠ b := htb.ne
  have qpath : (SimpleGraph.Walk.cons hta.symm
      (SimpleGraph.Walk.cons htb SimpleGraph.Walk.nil)).IsPath := by
    rw [SimpleGraph.Walk.cons_isPath_iff, SimpleGraph.Walk.cons_isPath_iff]
    refine ⟨⟨SimpleGraph.Walk.IsPath.nil, ?_⟩, ?_⟩
    · simp only [SimpleGraph.Walk.support_nil, List.mem_singleton]; exact hbne
    · simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
        not_or]
      exact ⟨hane, hab, by simp⟩
  set q : G.Path a b := ⟨_, qpath⟩ with hq
  have hq_in : t ∈ (q.1).support := by
    show t ∈ (SimpleGraph.Walk.cons hta.symm
      (SimpleGraph.Walk.cons htb SimpleGraph.Walk.nil)).support
    rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_cons]
    exact List.mem_cons_of_mem a (List.mem_cons_self ..)
  
  have huniq := (SimpleGraph.isAcyclic_iff_path_unique.mp hG) p q
  rw [huniq] at hp_notin
  exact hp_notin hq_in







theorem bfa_classicalForestData_of_bc69 (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc69_Gn_globalForest ω L R) : bkg_ClassicalForestData ω L R := by
  obtain ⟨S, hSfin, hSne, G, hGdec, ιU, hacyc, hmin, hdeg3, hιinj, hlammap⟩ := h
  exact ⟨S, hSfin, hSne, G, hGdec, G, ιU, le_rfl,
    (fun t a b => bfa_singleVertexCut_of_acyclic G hacyc t a b), hmin, hdeg3, hιinj, hlammap⟩





theorem bfa_classical_iff_bc69 (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) :
    bkg_ClassicalForestData ω L R ↔ bc69_Gn_globalForest ω L R :=
  ⟨bkg_globalForest_of_classical ω L R, bfa_classicalForestData_of_bc69 ω L R⟩













theorem bfa_classicalForestData_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d R) (hz₁ : z₁ ∈ vertexBoundary d R) (hzne : z₀ ≠ z₁)
    (hno : ∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) :
    bkg_ClassicalForestData ω L R :=
  bfa_classicalForestData_of_bc69 ω L R (bc69_globalForest_of_noTrif ω L R hz₀ hz₁ hzne hno)








theorem bfa_classicalForestData_of_singleStar (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {x : Site d} (a : Fin 3 → Site d)
    (hxbox : x ∈ box d R)
    (hxtri : bc67_IsGnTrifurcation ω L x)
    (hsingle : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → y = x)
    (habdry : ∀ i, a i ∈ vertexBoundary d R)
    (hxne : ∀ i, a i ≠ x)
    (hainj : Function.Injective a) :
    bkg_ClassicalForestData ω L R :=
  bfa_classicalForestData_of_bc69 ω L R
    (bc70_globalForest_of_singleStar ω L R a hxbox hxtri hsingle habdry hxne hainj)














theorem bfa_datum_implies_count (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bkg_ClassicalForestData ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R :=
  bkg_coarseTcount_of_classical ω L R h












theorem bfa_bk_of_classicalForest (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bkg_ClassicalForestData ω L R) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 :=
  (bkg_bk_uniqueness_of_classical p hp1 hp0 hdata).2.1





theorem bfa_bk_of_bc69Forest (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bc69_Gn_globalForest ω L R) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 :=
  bfa_bk_of_classicalForest p hp1 hp0
    (fun ω L R => (bfa_classical_iff_bc69 ω L R).mpr (hdata ω L R))











































theorem bfa_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      bkg_ClassicalForestData ω L R ↔ bc69_Gn_globalForest ω L R) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (z₀ z₁ : Site d),
      z₀ ∈ vertexBoundary d R → z₁ ∈ vertexBoundary d R → z₀ ≠ z₁ →
      (∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) →
      bkg_ClassicalForestData ω L R) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      bkg_ClassicalForestData ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) ∧
    
    (∀ (p : ℝ≥0) (hp1 : p ≤ 1), 0 < p →
      (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bkg_ClassicalForestData ω L R) →
      bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ω L R; exact bfa_classical_iff_bc69 ω L R
  · intro ω L R z₀ z₁ hz₀ hz₁ hzne hno; exact bfa_classicalForestData_of_noTrif ω L R hz₀ hz₁ hzne hno
  · intro ω L R h; exact bfa_datum_implies_count ω L R h
  · intro p hp1 hp0 hdata; exact bfa_bk_of_classicalForest p hp1 hp0 hdata

end StatMech.Walls
