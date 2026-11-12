/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









































































import Mathlib
import Code.Walls.bc113boundaryforest

open Set SimpleGraph Finset

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace StatMech.Walls

variable {V : Type*} [Fintype V] [DecidableEq V]









variable {G : SimpleGraph V}




theorem bc114_internal_two_neighbours (F : SimpleGraph V) {s t : V} (p : F.Walk s t)
    (hp : p.IsPath) {i : ℕ} (hi0 : 0 < i) (hilt : i < p.length) :
    F.Adj (p.getVert i) (p.getVert (i - 1)) ∧ F.Adj (p.getVert i) (p.getVert (i + 1)) ∧
      p.getVert (i - 1) ≠ p.getVert (i + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · 
    have hprev : (i - 1) < p.length := by omega
    have hadj : F.Adj (p.getVert (i - 1)) (p.getVert ((i - 1) + 1)) := p.adj_getVert_succ hprev
    have : (i - 1) + 1 = i := by omega
    rw [this] at hadj
    exact hadj.symm
  · exact p.adj_getVert_succ hilt
  · 
    have hinj := hp.getVert_injOn
    intro heq
    have h1 : (i - 1) ∈ {j | j ≤ p.length} := by simp; omega
    have h2 : (i + 1) ∈ {j | j ≤ p.length} := by simp; omega
    have := hinj h1 h2 heq
    omega



theorem bc114_internal_degree_ge_two (F : SimpleGraph V) [DecidableRel F.Adj] {s t : V}
    (p : F.Walk s t) (hp : p.IsPath) {i : ℕ} (hi0 : 0 < i) (hilt : i < p.length) :
    2 ≤ F.degree (p.getVert i) := by
  obtain ⟨hadj1, hadj2, hne⟩ := bc114_internal_two_neighbours F p hp hi0 hilt
  have hsub : {p.getVert (i - 1), p.getVert (i + 1)} ⊆ F.neighborFinset (p.getVert i) := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rw [SimpleGraph.mem_neighborFinset]
    rcases hz with rfl | rfl
    · exact hadj1
    · exact hadj2
  calc 2 = ({p.getVert (i - 1), p.getVert (i + 1)} : Finset V).card := by
          rw [Finset.card_pair hne]
    _ ≤ (F.neighborFinset (p.getVert i)).card := Finset.card_le_card hsub
    _ = F.degree (p.getVert i) := SimpleGraph.card_neighborFinset_eq_degree _ _











def bc114_IsInternal (F : SimpleGraph V) (v : V) : Prop :=
  ∃ (s t : V) (p : F.Walk s t) (i : ℕ), p.IsPath ∧ 0 < i ∧ i < p.length ∧ p.getVert i = v


theorem bc114_isInternal_degree_ge_two (F : SimpleGraph V) [DecidableRel F.Adj] {v : V}
    (hv : bc114_IsInternal F v) : 2 ≤ F.degree v := by
  obtain ⟨s, t, p, i, hp, hi0, hilt, hveq⟩ := hv
  rw [← hveq]
  exact bc114_internal_degree_ge_two F p hp hi0 hilt



theorem bc114_leaf_not_internal (F : SimpleGraph V) [DecidableRel F.Adj] {v : V}
    (hdeg : F.degree v = 1) : ¬ bc114_IsInternal F v := by
  intro hv
  have := bc114_isInternal_degree_ge_two F hv
  omega














def bc114_ArmCovered (F : SimpleGraph V) (B H : V → Prop) : Prop :=
  ∀ v, ¬ B v → ¬ H v → bc114_IsInternal F v






theorem bc114_leaf_on_boundary_of_armCovered (F : SimpleGraph V) [DecidableRel F.Adj]
    {B H : V → Prop} (hcov : bc114_ArmCovered F B H)
    (hhub : ∀ v, H v → 3 ≤ F.degree v)
    {v : V} (hdeg : F.degree v = 1) : B v := by
  by_contra hvB
  by_cases hvH : H v
  · 
    have := hhub v hvH
    omega
  · 
    have hint := hcov v hvB hvH
    have := bc114_isInternal_degree_ge_two F hint
    omega













theorem bc114_isInternal_of_mem_support (F : SimpleGraph V) {s t : V} (p : F.Walk s t)
    (hp : p.IsPath) {v : V} (hv : v ∈ p.support) (hvs : v ≠ s) (hvt : v ≠ t) :
    bc114_IsInternal F v := by
  
  rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hv
  obtain ⟨i, hvi, hile⟩ := hv
  refine ⟨s, t, p, i, hp, ?_, ?_, hvi⟩
  · rcases Nat.eq_zero_or_pos i with h0 | hpos
    · exfalso; apply hvs; rw [← hvi, h0, p.getVert_zero]
    · exact hpos
  · rcases Nat.lt_or_ge i p.length with hlt | hge
    · exact hlt
    · exfalso; apply hvt
      have : i = p.length := by omega
      rw [← hvi, this, p.getVert_length]





theorem bc114_internal_of_reachable_boundary (F : SimpleGraph V) {a z : V} (hr : F.Reachable a z)
    {v : V} (hva : v ≠ a) (hvz : v ≠ z)
    (hmem : ∃ p : F.Walk a z, p.IsPath ∧ v ∈ p.support) :
    bc114_IsInternal F v := by
  obtain ⟨p, hp, hvp⟩ := hmem
  exact bc114_isInternal_of_mem_support F p hp hvp hva hvz















theorem bc114_hasChild_of_forestNeighbour_up (G : SimpleGraph V) (B : V → Prop)
    (hreach : bc113_ReachesB G B)
    (hup : ∀ v, ¬ B v → ∃ w, (bc113_bForest G B hreach).Adj v w ∧
      bc113_toB G B v < bc113_toB G B w) :
    bc113_HasChild G B hreach := hup













theorem bc114_bForest_internal_has_child (G : SimpleGraph V) (B : V → Prop)
    (hreach : bc113_ReachesB G B) [DecidableRel (bc113_bForest G B hreach).Adj]
    {v : V} (hv : ¬ B v)
    (hint : bc114_IsInternal (bc113_bForest G B hreach) v) :
    ∃ w, (bc113_bForest G B hreach).Adj v w ∧ bc113_toB G B v < bc113_toB G B w := by
  classical
  set F := bc113_bForest G B hreach with hF
  
  have hdeg2 : 2 ≤ F.degree v := bc114_isInternal_degree_ge_two F hint
  
  have hpar : F.Adj v (bc113_parent G B hreach v) := bc113_bForest_adj_parent G B hreach hv
  have hparlt : bc113_toB G B (bc113_parent G B hreach v) < bc113_toB G B v :=
    (bc113_parent_spec G B hreach hv).2
  
  have hcard : 2 ≤ (F.neighborFinset v).card := by
    rwa [SimpleGraph.card_neighborFinset_eq_degree]
  
  have hpmem : bc113_parent G B hreach v ∈ F.neighborFinset v := by
    rw [SimpleGraph.mem_neighborFinset]; exact hpar
  obtain ⟨w, hwmem, hwne⟩ := Finset.exists_mem_ne (by omega : 1 < (F.neighborFinset v).card)
    (bc113_parent G B hreach v)
  rw [SimpleGraph.mem_neighborFinset] at hwmem
  refine ⟨w, hwmem, ?_⟩
  
  
  have hsep : bc113_toB G B v ≠ bc113_toB G B w := bc113_bForest_toB_ne G B hreach hwmem
  rcases lt_or_gt_of_ne hsep with hlt | hgt
  · exact hlt
  · 
    exfalso
    have := bc113_bForest_down_unique G B hreach hwmem hpar hgt hparlt
    exact hwne this






theorem bc114_hasChild_of_armCovered (G : SimpleGraph V) (B : V → Prop)
    (hreach : bc113_ReachesB G B) [DecidableRel (bc113_bForest G B hreach).Adj]
    (hcov : ∀ v, ¬ B v → bc114_IsInternal (bc113_bForest G B hreach) v) :
    bc113_HasChild G B hreach := by
  intro v hv
  exact bc114_bForest_internal_has_child G B hreach hv (hcov v hv)






















theorem bc114_armForest_boundaryAnchored (F : SimpleGraph V) [DecidableRel F.Adj]
    {B H : V → Prop} (hcov : bc114_ArmCovered F B H) (hhub : ∀ v, H v → 3 ≤ F.degree v)
    (hac : F.IsAcyclic) (hmin : ∀ v, 1 ≤ F.degree v) :
    F.IsAcyclic ∧ (∀ v, 1 ≤ F.degree v) ∧ (∀ v, F.degree v = 1 → B v) :=
  ⟨hac, hmin, fun v hdeg => bc114_leaf_on_boundary_of_armCovered F hcov hhub hdeg⟩











theorem bc114_obstruction_real :
    ¬ ∃ (F : SimpleGraph (Fin 3)) (_ : DecidableRel F.Adj),
        F ≤ (⊤ : SimpleGraph (Fin 3)) ∧ F.IsAcyclic ∧ (∀ v, 1 ≤ F.degree v) ∧
        (∀ v, F.degree v = 1 → v = 0) :=
  bc113_no_boundaryAnchored_on_triangle








theorem bc114_leaf_not_armCovered (F : SimpleGraph V) [DecidableRel F.Adj] {v : V}
    (hdeg : F.degree v = 1) : ¬ bc114_IsInternal F v :=
  bc114_leaf_not_internal F hdeg












theorem bc114_armCovered_nonvacuous :
    bc114_IsInternal (SimpleGraph.fromEdgeSet {s((0 : Fin 3), 1), s((1 : Fin 3), 2)}) 1 := by
  classical
  set F := SimpleGraph.fromEdgeSet {s((0 : Fin 3), 1), s((1 : Fin 3), 2)} with hF
  have h01 : F.Adj 0 1 := by rw [hF, SimpleGraph.fromEdgeSet_adj]; exact ⟨by simp, by decide⟩
  have h12 : F.Adj 1 2 := by rw [hF, SimpleGraph.fromEdgeSet_adj]; exact ⟨by simp, by decide⟩
  
  set p : F.Walk 0 2 := SimpleGraph.Walk.cons h01 (SimpleGraph.Walk.cons h12 SimpleGraph.Walk.nil)
    with hp
  have hpath : p.IsPath := by
    rw [hp, SimpleGraph.Walk.isPath_def]
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil]
    decide
  refine ⟨0, 2, p, 1, hpath, by norm_num, ?_, ?_⟩
  · rw [hp]; simp [SimpleGraph.Walk.length_cons]
  · rw [hp]; rfl

















































theorem bc114_status :
    
    (¬ ∃ (F : SimpleGraph (Fin 3)) (_ : DecidableRel F.Adj),
        F ≤ (⊤ : SimpleGraph (Fin 3)) ∧ F.IsAcyclic ∧ (∀ v, 1 ≤ F.degree v) ∧
        (∀ v, F.degree v = 1 → v = 0)) ∧
    
    (∀ (F : SimpleGraph V) [DecidableRel F.Adj] (B H : V → Prop),
      bc114_ArmCovered F B H → (∀ v, H v → 3 ≤ F.degree v) →
      ∀ v, F.degree v = 1 → B v) ∧
    
    (∀ (F : SimpleGraph V) [DecidableRel F.Adj] (B H : V → Prop),
      bc114_ArmCovered F B H → (∀ v, H v → 3 ≤ F.degree v) →
      F.IsAcyclic → (∀ v, 1 ≤ F.degree v) →
      F.IsAcyclic ∧ (∀ v, 1 ≤ F.degree v) ∧ (∀ v, F.degree v = 1 → B v)) ∧
    
    (∀ (F : SimpleGraph V) [DecidableRel F.Adj] (v : V),
      F.degree v = 1 → ¬ bc114_IsInternal F v) := by
  refine ⟨bc114_obstruction_real, ?_, ?_, ?_⟩
  · intro F _ B H hcov hhub v hdeg
    exact bc114_leaf_on_boundary_of_armCovered F hcov hhub hdeg
  · intro F _ B H hcov hhub hac hmin
    exact bc114_armForest_boundaryAnchored F hcov hhub hac hmin
  · intro F _ v hdeg
    exact bc114_leaf_not_armCovered F hdeg

end StatMech.Walls
