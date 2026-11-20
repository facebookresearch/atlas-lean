/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
































































import Mathlib
import Code.Walls.bc114haschild
import Code.Walls.bc101mengergap

open Set SimpleGraph Finset

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace StatMech.Walls

variable {V : Type*}
variable {G : SimpleGraph V}











theorem bc116_isInternal_of_mem_support_free (F : SimpleGraph V) {s t : V} (p : F.Walk s t)
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







theorem bc116_isInternal_of_throughPath (F : SimpleGraph V) {s t : V} (p : F.Walk s t)
    (hp : p.IsPath) {v : V} (hv : v ∈ p.support) (hvs : v ≠ s) (hvt : v ≠ t) :
    bc114_IsInternal F v :=
  bc116_isInternal_of_mem_support_free F p hp hv hvs hvt







def bc116_ThroughPathCovered (F : SimpleGraph V) (B H : V → Prop) : Prop :=
  ∀ v, ¬ B v → ¬ H v →
    ∃ (s t : V) (p : F.Walk s t), p.IsPath ∧ v ∈ p.support ∧ v ≠ s ∧ v ≠ t




theorem bc116_armCovered_of_throughPathCovered (F : SimpleGraph V) {B H : V → Prop}
    (hcov : bc116_ThroughPathCovered F B H) : bc114_ArmCovered F B H := by
  intro v hvB hvH
  obtain ⟨s, t, p, hp, hmem, hvs, hvt⟩ := hcov v hvB hvH
  exact bc116_isInternal_of_throughPath F p hp hmem hvs hvt

end StatMech.Walls









namespace StatMech.Walls

variable {V : Type*}




theorem bc116_path_of_reachable (F : SimpleGraph V) {a z : V} (hr : F.Reachable a z) :
    ∃ p : F.Walk a z, p.IsPath :=
  ⟨hr.exists_path_of_dist.choose, hr.exists_path_of_dist.choose_spec.1⟩





theorem bc116_interior_of_arm_path_covered (F : SimpleGraph V) {a z v : V}
    (hva : v ≠ a) (hvz : v ≠ z)
    (hmem : ∃ p : F.Walk a z, p.IsPath ∧ v ∈ p.support) :
    bc114_IsInternal F v := by
  obtain ⟨p, hp, hvp⟩ := hmem
  exact bc116_isInternal_of_mem_support_free F p hp hvp hva hvz




theorem bc116_covered_of_on_hub_boundary_path (F : SimpleGraph V) {s t v : V}
    (p : F.Walk s t) (hp : p.IsPath) (hmem : v ∈ p.support) (hvs : v ≠ s) (hvt : v ≠ t) :
    bc114_IsInternal F v :=
  bc116_isInternal_of_mem_support_free F p hp hmem hvs hvt

end StatMech.Walls







namespace StatMech.Walls

variable {V : Type*} [Fintype V] [DecidableEq V]





theorem bc116_leaf_on_boundary (F : SimpleGraph V) [DecidableRel F.Adj] {B H : V → Prop}
    (hcov : bc116_ThroughPathCovered F B H) (hhub : ∀ v, H v → 3 ≤ F.degree v)
    {v : V} (hdeg : F.degree v = 1) : B v :=
  bc114_leaf_on_boundary_of_armCovered F (bc116_armCovered_of_throughPathCovered F hcov) hhub hdeg




theorem bc116_armForest_boundaryAnchored (F : SimpleGraph V) [DecidableRel F.Adj] {B H : V → Prop}
    (hcov : bc116_ThroughPathCovered F B H) (hhub : ∀ v, H v → 3 ≤ F.degree v)
    (hac : F.IsAcyclic) (hmin : ∀ v, 1 ≤ F.degree v) :
    F.IsAcyclic ∧ (∀ v, 1 ≤ F.degree v) ∧ (∀ v, F.degree v = 1 → B v) :=
  bc114_armForest_boundaryAnchored F (bc116_armCovered_of_throughPathCovered F hcov) hhub hac hmin













theorem bc116_pendant_not_covered (F : SimpleGraph V) [DecidableRel F.Adj] {v : V}
    (hdeg : F.degree v = 1) : ¬ bc114_IsInternal F v :=
  bc114_leaf_not_internal F hdeg




theorem bc116_covered_nonvacuous :
    bc114_IsInternal (SimpleGraph.fromEdgeSet {s((0 : Fin 3), 1), s((1 : Fin 3), 2)}) 1 :=
  bc114_armCovered_nonvacuous

end StatMech.Walls










namespace StatMech.Walls

open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

variable {d : ℕ}






theorem bc116_arm_boundary_path_concrete (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (hR : 1 ≤ R)
    (y a : Site d) (habox : a ∈ box d R)
    (hinf : (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite) :
    ∃ z ∈ vertexBoundary d R, ∃ _p : (bc67_contractedLattice ω L y).Walk a z, True := by
  obtain ⟨z, hzb, hrz⟩ := bc101_arm_reaches_boundary ω L R hR y a habox hinf
  obtain ⟨p, _hp⟩ := bc116_path_of_reachable (bc67_contractedLattice ω L y) hrz
  exact ⟨z, hzb, p, trivial⟩





theorem bc116_arm_interior_covered_concrete (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ)
    (y a z v : Site d) (hva : v ≠ a) (hvz : v ≠ z)
    (hmem : ∃ p : (bc67_contractedLattice ω L y).Walk a z, p.IsPath ∧ v ∈ p.support) :
    bc114_IsInternal (bc67_contractedLattice ω L y) v :=
  bc116_interior_of_arm_path_covered (bc67_contractedLattice ω L y) hva hvz hmem







def bc116_ArmPathMembership (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d)
    (B H : Site d → Prop) : Prop :=
  bc116_ThroughPathCovered (bc67_contractedLattice ω L y) B H






theorem bc116_armCovered_concrete_of_membership (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d)
    {B H : Site d → Prop} (hmem : bc116_ArmPathMembership ω L y B H) :
    bc114_ArmCovered (bc67_contractedLattice ω L y) B H :=
  bc116_armCovered_of_throughPathCovered (bc67_contractedLattice ω L y) hmem






























theorem bc116_status :
    
    (∀ (F : SimpleGraph V) (B H : V → Prop),
      bc116_ThroughPathCovered F B H → bc114_ArmCovered F B H) ∧
    
    (∀ (F : SimpleGraph V) (v : V), bc114_IsInternal F v →
      ∃ (s t : V) (p : F.Walk s t), p.IsPath ∧ v ∈ p.support ∧ v ≠ s ∧ v ≠ t) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), 1 ≤ R → ∀ (y a : Site d), a ∈ box d R →
      (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite →
      ∃ z ∈ vertexBoundary d R, ∃ _p : (bc67_contractedLattice ω L y).Walk a z, True) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d) (B H : Site d → Prop),
      bc116_ArmPathMembership ω L y B H →
      bc114_ArmCovered (bc67_contractedLattice ω L y) B H) ∧
    
    (∀ (F : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel F.Adj] (v : V),
      F.degree v = 1 → ¬ bc114_IsInternal F v) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro F B H hcov; exact bc116_armCovered_of_throughPathCovered F hcov
  · intro F v hv
    obtain ⟨s, t, p, i, hp, hi0, hilt, hveq⟩ := hv
    subst hveq
    refine ⟨s, t, p, hp, p.getVert_mem_support i, ?_, ?_⟩
    · intro h
      have h0 : p.getVert i = p.getVert 0 := by rw [p.getVert_zero]; exact h
      exact absurd (hp.getVert_injOn (by simp; omega) (by simp) h0) (by omega)
    · intro h
      have hL : p.getVert i = p.getVert p.length := by rw [p.getVert_length]; exact h
      exact absurd (hp.getVert_injOn (by simp; omega) (by simp) hL) (by omega)
  · intro ω L R hR y a habox hinf
    exact bc116_arm_boundary_path_concrete ω L R hR y a habox hinf
  · intro ω L y B H hmem
    exact bc116_armCovered_concrete_of_membership ω L y hmem
  · intro F _ _ _ v hdeg
    exact bc116_pendant_not_covered F hdeg

end StatMech.Walls
