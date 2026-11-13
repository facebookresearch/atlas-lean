/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



























































































import Mathlib
import Code.Walls.bc86finiteNcount
import Code.Walls.bc84leafboundary
import Code.Walls.bc80gntrifcount
import Code.Walls.bc75spanningtree
import Code.Walls.bc69count

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













theorem bc87_arm_reaches_outside_box (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y a : Site d)
    (hinf : (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite) (n : ℕ) :
    ∃ z, z ∉ box d n ∧ Connected d (removeSites (bc61_boxAround d L y) ω) a z :=
  (cluster_infinite_iff (removeSites (bc61_boxAround d L y) ω) a).mp hinf n






theorem bc87_coarseTrif_arms_reach_outside (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) {y : Site d}
    (h : bc61_IsCoarseTrifurcation ω L y) (n : ℕ) :
    ∃ a₁ a₂ a₃ : Site d,
      (∃ z, z ∉ box d n ∧ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ z) ∧
      (∃ z, z ∉ box d n ∧ Connected d (removeSites (bc61_boxAround d L y) ω) a₂ z) ∧
      (∃ z, z ∉ box d n ∧ Connected d (removeSites (bc61_boxAround d L y) ω) a₃ z) := by
  obtain ⟨a₁, a₂, a₃, _, _, _, ⟨hi₁, hi₂, hi₃⟩, _⟩ := h
  exact ⟨a₁, a₂, a₃,
    bc87_arm_reaches_outside_box ω L y a₁ hi₁ n,
    bc87_arm_reaches_outside_box ω L y a₂ hi₂ n,
    bc87_arm_reaches_outside_box ω L y a₃ hi₃ n⟩























theorem bc87_pruning_preserves_branch_le_leaf (R : ℕ) {S : Set (Site d)} [Fintype (↑S : Type)]
    [Nonempty (↑S : Type)] (G : SimpleGraph (↑S : Type)) [DecidableRel G.Adj]
    (hacyc : G.IsAcyclic) (hmin : ∀ v : (↑S : Type), 1 ≤ G.degree v)
    (hbdry : ∀ v : (↑S : Type), G.degree v = 1 → (v : Site d) ∈ vertexBoundary d R) :
    (univ.filter (fun v : (↑S : Type) => 3 ≤ G.degree v)).card ≤ boxSV_boundaryCard d R := by
  classical
  refine le_trans (flc2_forest_internal_le_leaves G hacyc hmin) ?_
  exact flc2_leaf_card_le_boundary G R (Subtype.val : (↑S : Type) → Site d) hbdry
    (bc69_subtypeVal_injOn _)








theorem bc87_leaves_on_boundary_free_of_boundaryLeafClause (R : ℕ) {S : Set (Site d)}
    [Fintype (↑S : Type)] (G : SimpleGraph (↑S : Type)) [DecidableRel G.Adj]
    (hbdry : ∀ v : (↑S : Type), G.degree v = 1 → (v : Site d) ∈ vertexBoundary d R) :
    (univ.filter (fun v : (↑S : Type) => G.degree v = 1)).card ≤ boxSV_boundaryCard d R :=
  flc2_leaf_card_le_boundary G R (Subtype.val : (↑S : Type) → Site d) hbdry
    (bc69_subtypeVal_injOn _)













theorem bc87_prune_step_acyclic {V : Type*} (G : SimpleGraph V) (hacyc : G.IsAcyclic)
    (s : Set (Sym2 V)) :
    (G.deleteEdges s).IsAcyclic :=
  hacyc.anti (SimpleGraph.deleteEdges_le s)







theorem bc87_prune_step_degree_le {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Set (Sym2 V)) [DecidableRel (G.deleteEdges s).Adj] (v : V) :
    (G.deleteEdges s).degree v ≤ G.degree v :=
  SimpleGraph.degree_le_of_le (SimpleGraph.deleteEdges_le s)
























theorem bc87_leaf_boundary_fully_perConfig_given_forest (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (h : bc75_FiberGnTrifData ω L R c) :
    (bc73_fiber ω L R c).card ≤ boxSV_boundaryCard d R :=
  bc84_fiber_bound_of_gnTrifData ω L R c h











theorem bc87_prune_reduces_to_cut (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) {y y' : Site d}
    (hN : numInfiniteClusters d ω ≤ 1)
    (h : bc61_IsCoarseTrifurcation ω L y) (h' : bc61_IsCoarseTrifurcation ω L y') :
    ∃ a a' : Site d,
      (cluster d ω a).Infinite ∧ (cluster d ω a').Infinite ∧ Connected d ω a a' :=
  bc86_fiber_arms_can_coincide ω L hN h h'

















theorem bc87_witness_upperLines_arms_reach {L : ℕ} (hL : 3 ≤ L) (n : ℕ) :
    ∃ a₁ a₂ a₃ : Site 2,
      (∃ z, z ∉ box 2 n ∧ Connected 2 (removeSites (bc61_boxAround 2 L (0 : Site 2)) bc60_upperLines) a₁ z) ∧
      (∃ z, z ∉ box 2 n ∧ Connected 2 (removeSites (bc61_boxAround 2 L (0 : Site 2)) bc60_upperLines) a₂ z) ∧
      (∃ z, z ∉ box 2 n ∧ Connected 2 (removeSites (bc61_boxAround 2 L (0 : Site 2)) bc60_upperLines) a₃ z) :=
  bc87_coarseTrif_arms_reach_outside bc60_upperLines L (bc61_wholeBox_severs_upperLines hL) n








theorem bc87_witness_upperLines_N_top_cut_fails (L : ℕ) :
    numInfiniteClusters 2 bc60_upperLines = ⊤ ∧
      (Disjoint (bc61_boxAround 2 L (0 : Site 2))
          (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧
        Connected 2 bc60_upperLines
          (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1)) :=
  ⟨bc86_upperLines_N_top, bc86_upperLines_gnCut_needs_buffer L⟩




































theorem bc87_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (y : Site 2),
      bc61_IsCoarseTrifurcation ω L y → ∀ n : ℕ,
      ∃ a₁ a₂ a₃ : Site 2,
        (∃ z, z ∉ box 2 n ∧ Connected 2 (removeSites (bc61_boxAround 2 L y) ω) a₁ z) ∧
        (∃ z, z ∉ box 2 n ∧ Connected 2 (removeSites (bc61_boxAround 2 L y) ω) a₂ z) ∧
        (∃ z, z ∉ box 2 n ∧ Connected 2 (removeSites (bc61_boxAround 2 L y) ω) a₃ z)) ∧
    
    (∀ (R : ℕ) (S : Set (Site 2)) (_ : Fintype (↑S : Type)) (G : SimpleGraph (↑S : Type))
        (_ : DecidableRel G.Adj),
      (∀ v : (↑S : Type), G.degree v = 1 → (v : Site 2) ∈ vertexBoundary 2 R) →
      (univ.filter (fun v : (↑S : Type) => G.degree v = 1)).card ≤ boxSV_boundaryCard 2 R) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ) (c : Fin 2 → Fin (2 * L + 1)),
      bc75_FiberGnTrifData ω L R c → (bc73_fiber ω L R c).card ≤ boxSV_boundaryCard 2 R) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (y y' : Site 2), numInfiniteClusters 2 ω ≤ 1 →
      bc61_IsCoarseTrifurcation ω L y → bc61_IsCoarseTrifurcation ω L y' →
      ∃ a a' : Site 2,
        (cluster 2 ω a).Infinite ∧ (cluster 2 ω a').Infinite ∧ Connected 2 ω a a') ∧
    
    (numInfiniteClusters 2 bc60_upperLines = ⊤) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ω L y h n; exact bc87_coarseTrif_arms_reach_outside ω L h n
  · intro R S _ G _ hbdry; exact bc87_leaves_on_boundary_free_of_boundaryLeafClause R G hbdry
  · intro ω L R c h; exact bc87_leaf_boundary_fully_perConfig_given_forest ω L R c h
  · intro ω L y y' hN h h'; exact bc87_prune_reduces_to_cut ω L hN h h'
  · exact bc86_upperLines_N_top

end StatMech.Walls
