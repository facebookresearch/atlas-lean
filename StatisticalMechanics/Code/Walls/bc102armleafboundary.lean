/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/























































































































import Mathlib
import Code.Walls.bc69count
import Code.Walls.bc65connected
import Code.Walls.bc80gntrifcount
import Code.Walls.bc101mengergap

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}















theorem bc102_count_forest_derivable (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc69_Gn_globalForest ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R :=
  bc69_count_via_leafBound ω L R h





theorem bc102_bc64_gives_count (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d R) (hz₁ : z₁ ∈ vertexBoundary d R)
    (hzne : z₀ ≠ z₁) (hinj : bc64_CoarseBoundaryInjection ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R :=
  bc64_coarseTcount_le_boundary_of_boundaryInjection ω L R hz₀ hz₁ hzne hinj






theorem bc102_bc64_gives_connectedForest (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d R) (hz₁ : z₁ ∈ vertexBoundary d R)
    (hzne : z₀ ≠ z₁) (hinj : bc64_CoarseBoundaryInjection ω L R) :
    bc65_ConnectedCoarseForest ω L R :=
  bc65_connectedForest_of_boundaryInjection ω L R hz₀ hz₁ hzne hinj















theorem bc102_leaf_count_absorbs_shared {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hacyc : G.IsAcyclic) (hmin : ∀ v, 1 ≤ G.degree v) :
    (univ.filter (fun v => 3 ≤ G.degree v)).card
      ≤ (univ.filter (fun v => G.degree v = 1)).card :=
  bc69_leaf_count_absorbs_shared G hacyc hmin





theorem bc102_leaf_boundary_free_on_subtype {p : Site d → Prop} (S : Set (Subtype p)) :
    Set.InjOn (Subtype.val : Subtype p → Site d) S :=
  bc69_subtypeVal_injOn S






theorem bc102_spanForest_branch_le_leaf (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (S : Set (Site d)) [Fintype (↑S : Type)] [Nonempty (↑S : Type)]
    (hmin : ∀ v : (↑S : Type), 1 ≤ (bc75_spanForest ω L R c S).degree v) :
    (bc80_branchFinset ω L R c S).card ≤ (bc80_leafFinset ω L R c S).card :=
  bc80_branch_le_leaf ω L R c S (fun v => by convert hmin v using 2)


















theorem bc102_bc64_crossSV_refuted (L : ℕ) :
    Disjoint (bc61_boxAround 2 L (0 : Site 2))
        (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧
      Connected 2 bc60_upperLines
        (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1) :=
  bc64_arms_can_share_boundary L







theorem bc102_bc64_disjointStar_degrees :
    bc64_starG.degree 0 = 3 ∧ (∀ i : Fin 4, i ≠ 0 → bc64_starG.degree i = 1) :=
  ⟨bc64_starG_centre_deg, bc64_starG_leaf_deg⟩
















theorem bc102_BK_count_reduces_to_connectedForest (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) :
    (bc69_Gn_globalForest ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) ∧
    (∀ {z₀ z₁ : Site d}, z₀ ∈ vertexBoundary d R → z₁ ∈ vertexBoundary d R → z₀ ≠ z₁ →
      bc64_CoarseBoundaryInjection ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) :=
  ⟨bc102_count_forest_derivable ω L R,
   fun hz₀ hz₁ hzne hinj => bc102_bc64_gives_count ω L R hz₀ hz₁ hzne hinj⟩






theorem bc102_connectedForest_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d R) (hz₁ : z₁ ∈ vertexBoundary d R) (hzne : z₀ ≠ z₁)
    (hno : ∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) :
    bc69_Gn_globalForest ω L R :=
  bc69_globalForest_of_noTrif ω L R hz₀ hz₁ hzne hno














theorem bc102_upperLines_count_via_connectedForest {L R : ℕ}
    (h : bc69_Gn_globalForest bc60_upperLines L R) :
    bc61_coarseTcount bc60_upperLines L R ≤ boxSV_boundaryCard 2 R :=
  bc69_upperLines_globalForest_count h








































theorem bc102_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      bc69_Gn_globalForest ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) ∧
    
    (∀ {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V) [_inst : DecidableRel G.Adj],
      G.IsAcyclic → (∀ v, 1 ≤ G.degree v) →
      (univ.filter (fun v => 3 ≤ G.degree v)).card
        ≤ (univ.filter (fun v => G.degree v = 1)).card) ∧
    
    (bc64_starG.degree 0 = 3 ∧ (∀ i : Fin 4, i ≠ 0 → bc64_starG.degree i = 1)) ∧
    
    (∀ (L : ℕ),
      Disjoint (bc61_boxAround 2 L (0 : Site 2))
          (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧
        Connected 2 bc60_upperLines
          (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1)) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (z₀ z₁ : Site d),
      z₀ ∈ vertexBoundary d R → z₁ ∈ vertexBoundary d R → z₀ ≠ z₁ →
      bc64_CoarseBoundaryInjection ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ω L R h; exact bc102_count_forest_derivable ω L R h
  · intro V _ _ G _ hacyc hmin; exact bc102_leaf_count_absorbs_shared G hacyc hmin
  · exact bc102_bc64_disjointStar_degrees
  · intro L; exact bc102_bc64_crossSV_refuted L
  · intro ω L R z₀ z₁ hz₀ hz₁ hzne hinj; exact bc102_bc64_gives_count ω L R hz₀ hz₁ hzne hinj

end StatMech.Walls
