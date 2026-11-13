/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
























































































import Mathlib
import Code.Walls.bc116armproof
import Code.Walls.bc110globalforest
import Code.Walls.bc102armleafboundary

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

















theorem bc118_interiorPendant_not_covered {V : Type*}
    (F : SimpleGraph V) {B H : V → Prop} {v : V}
    (hnotint : ¬ bc114_IsInternal F v) (hvB : ¬ B v) (hvH : ¬ H v) :
    ¬ bc116_ThroughPathCovered F B H := by
  intro hcov
  obtain ⟨s, t, p, hp, hmem, hvs, hvt⟩ := hcov v hvB hvH
  exact hnotint (bc116_isInternal_of_throughPath F p hp hmem hvs hvt)




theorem bc118_degreeOnePendant_not_covered {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) [DecidableRel F.Adj] {B H : V → Prop} {v : V}
    (hdeg : F.degree v = 1) (hvB : ¬ B v) (hvH : ¬ H v) :
    ¬ bc116_ThroughPathCovered F B H :=
  bc118_interiorPendant_not_covered F (bc116_pendant_not_covered F hdeg) hvB hvH





theorem bc118_concrete_interiorPendant_not_covered :
    ¬ bc116_ThroughPathCovered (SimpleGraph.fromEdgeSet {s((0 : Fin 2), 1)})
        (fun w => w = 0) (fun _ => False) := by
  classical
  
  have hdeg1 : (SimpleGraph.fromEdgeSet {s((0 : Fin 2), 1)}).degree 1 = 1 :=
    bc69_single_edge_degree_b (0 : Fin 2) 1 (by decide)
  have hnotint : ¬ bc114_IsInternal (SimpleGraph.fromEdgeSet {s((0 : Fin 2), 1)}) 1 :=
    bc114_leaf_not_internal _ hdeg1
  exact bc118_interiorPendant_not_covered _ hnotint (by decide) (by simp)

















theorem bc118_pathUnion_can_have_pendant :
    ∃ (F' : SimpleGraph (Fin 3)) (_ : DecidableRel F'.Adj) (v : Fin 3),
      F'.degree v = 1 ∧ ¬ bc114_IsInternal F' v := by
  classical
  
  refine ⟨SimpleGraph.fromEdgeSet {s((0 : Fin 3), 1)}, inferInstance, 1, ?_, ?_⟩
  · exact bc69_single_edge_degree_b (0 : Fin 3) 1 (by decide)
  · exact bc114_leaf_not_internal _ (bc69_single_edge_degree_b (0 : Fin 3) 1 (by decide))














theorem bc118_count_unconditional_leaf_bound {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hacyc : G.IsAcyclic) (hmin : ∀ v, 1 ≤ G.degree v) :
    (univ.filter (fun v => 3 ≤ G.degree v)).card
      ≤ (univ.filter (fun v => G.degree v = 1)).card :=
  bc102_leaf_count_absorbs_shared G hacyc hmin

variable {d : ℕ}







theorem bc118_count_closes_via_forest (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc69_Gn_globalForest ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R :=
  bc102_count_forest_derivable ω L R h
















theorem bc118_membership_NOT_needed_for_count (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) :
    (bc69_Gn_globalForest ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) ∧
    (∀ {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.IsAcyclic → (∀ v, 1 ≤ G.degree v) →
      (univ.filter (fun v => 3 ≤ G.degree v)).card
        ≤ (univ.filter (fun v => G.degree v = 1)).card) := by
  refine ⟨bc118_count_closes_via_forest ω L R, ?_⟩
  intro V _ _ G _ hacyc hmin
  exact bc118_count_unconditional_leaf_bound G hacyc hmin











theorem bc118_membership_suffices_but_is_not_the_route {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) [DecidableRel F.Adj] {B H : V → Prop}
    (hcov : bc116_ThroughPathCovered F B H)
    (hhub : ∀ v, H v → 3 ≤ F.degree v) (hac : F.IsAcyclic) (hmin : ∀ v, 1 ≤ F.degree v) :
    F.IsAcyclic ∧ (∀ v, 1 ≤ F.degree v) ∧ (∀ v, F.degree v = 1 → B v) :=
  bc116_armForest_boundaryAnchored F hcov hhub hac hmin







theorem bc118_count_nonvacuous (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d R) (hz₁ : z₁ ∈ vertexBoundary d R) (hzne : z₀ ≠ z₁)
    (hno : ∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R :=
  bc118_count_closes_via_forest ω L R (bc110_globalForest_of_noTrif ω L R hz₀ hz₁ hzne hno)



































theorem bc118_status :
    
    (∀ {V : Type} [Fintype V] [DecidableEq V] (F : SimpleGraph V) [DecidableRel F.Adj]
      (B H : V → Prop) (v : V), F.degree v = 1 → ¬ B v → ¬ H v →
      ¬ bc116_ThroughPathCovered F B H) ∧
    
    (∃ (F' : SimpleGraph (Fin 3)) (_ : DecidableRel F'.Adj) (v : Fin 3),
      F'.degree v = 1 ∧ ¬ bc114_IsInternal F' v) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      bc69_Gn_globalForest ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) ∧
    
    (∀ {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.IsAcyclic → (∀ v, 1 ≤ G.degree v) →
      (univ.filter (fun v => 3 ≤ G.degree v)).card
        ≤ (univ.filter (fun v => G.degree v = 1)).card) := by
  refine ⟨?_, bc118_pathUnion_can_have_pendant, ?_, ?_⟩
  · intro V _ _ F _ B H v hdeg hvB hvH
    exact bc118_degreeOnePendant_not_covered F hdeg hvB hvH
  · intro ω L R h; exact bc118_count_closes_via_forest ω L R h
  · intro V _ _ G _ hacyc hmin; exact bc118_count_unconditional_leaf_bound G hacyc hmin

end StatMech.Walls
