/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




















































import Mathlib
import Code.Walls.bftfinetrif
import Code.Walls.briraysintree
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











theorem bfl_tree_le_lattice {ω : ConfigSpace (Sym2 (Site d))} {T : SimpleGraph (Site d)}
    (hT : T ≤ openSubgraph d ω) : T ≤ hypercubicLattice d :=
  le_trans hT (openSubgraph_le ω)










theorem bfl_fineArm_reaches_boundary {ω : ConfigSpace (Sym2 (Site d))} (T : SimpleGraph (Site d))
    [LocallyFinite T] (hT : T ≤ openSubgraph d ω) {w x : Site d} {R : ℕ} (hR : 1 ≤ R) (hwx : w ≠ x)
    (hw : w ∈ box d R) (hinf : (ray34_AvoidCluster T {x} w).Infinite) :
    ∃ r : ℕ → Site d, r 0 = w ∧ Function.Injective r ∧
      (∀ k, T.Adj (r k) (r (k + 1))) ∧ (∀ k, r k ≠ x) ∧ (∃ k, r k ∈ vertexBoundary d R) :=
  bri_branchRay_reaches_boundary T (bfl_tree_le_lattice hT) hR hwx hw hinf




theorem bfl_treeRay_reaches_boundary {ω : ConfigSpace (Sym2 (Site d))} (T : SimpleGraph (Site d))
    [LocallyFinite T] (hT : T ≤ openSubgraph d ω) {w : Site d} {R : ℕ} (hR : 1 ≤ R)
    (hw : w ∈ box d R) (hinf : (ray34_AvoidCluster T ∅ w).Infinite) :
    ∃ r : ℕ → Site d, r 0 = w ∧ Function.Injective r ∧
      (∀ k, T.Adj (r k) (r (k + 1))) ∧ (∃ k, r k ∈ vertexBoundary d R) :=
  bri_treeRay_reaches_boundary T (bfl_tree_le_lattice hT) hR hw hinf








theorem bfl_armUnion_acyclic {V : Type*} {T : SimpleGraph V} (hT : T.IsTree)
    {ι : Type*} (Gs : ι → SimpleGraph V) (hle : ∀ i, Gs i ≤ T) :
    (⨆ i, Gs i).IsAcyclic :=
  bri_union_le_acyclic hT Gs hle



theorem bfl_rayGraph_le {V : Type*} (T : SimpleGraph V) (r : ℕ → V) (N : ℕ)
    (hadj : ∀ k, T.Adj (r k) (r (k + 1))) : bri_rayGraph r N ≤ T :=
  bri_rayGraph_le T r N hadj













theorem bfl_fineTrif_iff_bc67_zero (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) :
    bft_FineTrif ω x ↔ bc67_IsGnTrifurcation ω 0 x := Iff.rfl







theorem bfl_fineCount_of_armSubforest (ω : ConfigSpace (Sym2 (Site 2))) (R : ℕ)
    (h : bau_ArmSubforestData ω 0 R) :
    bc61_coarseTcount ω 0 R ≤ boxSV_boundaryCard 2 R :=
  bca_datum_implies_count ω 0 R h





theorem bfl_bk_of_fineArmSubforest (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bau_ArmSubforestData ω L R) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 :=
  bau_bk_of_subforestData p hp1 hp0 hdata




















theorem bfl_arbitrary_tree_fails_hleaf :
    ∃ (G T : SimpleGraph (Fin 4)) (_ : DecidableRel G.Adj) (_ : DecidableRel T.Adj)
      (B : Finset (Fin 4)),
      T ≤ G ∧ T.IsTree ∧
      (∃ v, G.degree v = 2 ∧ T.degree v = 1 ∧ v ∉ B) ∧
      ¬ (∀ v, T.degree v = 1 → v ∈ B) :=
  bof2_interiorLeaf_obstruction
















































theorem bfl_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) {T : SimpleGraph (Site 2)},
      T ≤ openSubgraph 2 ω → T ≤ hypercubicLattice 2) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (T : SimpleGraph (Site 2)) [LocallyFinite T],
      T ≤ openSubgraph 2 ω → ∀ {w x : Site 2} {R : ℕ}, 1 ≤ R → w ≠ x → w ∈ box 2 R →
      (ray34_AvoidCluster T {x} w).Infinite →
      ∃ r : ℕ → Site 2, r 0 = w ∧ Function.Injective r ∧
        (∀ k, T.Adj (r k) (r (k + 1))) ∧ (∀ k, r k ≠ x) ∧ (∃ k, r k ∈ vertexBoundary 2 R)) ∧
    
    (∀ {V : Type} {T : SimpleGraph V}, T.IsTree → ∀ {ι : Type} (Gs : ι → SimpleGraph V),
      (∀ i, Gs i ≤ T) → (⨆ i, Gs i).IsAcyclic) ∧
    
    (∃ (G T : SimpleGraph (Fin 4)) (_ : DecidableRel G.Adj) (_ : DecidableRel T.Adj)
      (B : Finset (Fin 4)),
      T ≤ G ∧ T.IsTree ∧ (∃ v, G.degree v = 2 ∧ T.degree v = 1 ∧ v ∉ B) ∧
      ¬ (∀ v, T.degree v = 1 → v ∈ B)) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (R : ℕ),
      bau_ArmSubforestData ω 0 R → bc61_coarseTcount ω 0 R ≤ boxSV_boundaryCard 2 R) ∧
    
    (∀ (p : ℝ≥0) (hp1 : p ≤ 1), 0 < p →
      (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bau_ArmSubforestData ω L R) →
      bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ω T hT; exact bfl_tree_le_lattice hT
  · intro ω T _ hT w x R hR hwx hw hinf; exact bfl_fineArm_reaches_boundary T hT hR hwx hw hinf
  · intro V T hT ι Gs hle; exact bfl_armUnion_acyclic hT Gs hle
  · exact bfl_arbitrary_tree_fails_hleaf
  · intro ω R h; exact bfl_fineCount_of_armSubforest ω R h
  · intro p hp1 hp0 hdata; exact bfl_bk_of_fineArmSubforest p hp1 hp0 hdata

end StatMech.Walls
