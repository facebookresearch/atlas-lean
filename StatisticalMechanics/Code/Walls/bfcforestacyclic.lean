/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










































































import Mathlib
import Code.Walls.bc112sepcontract
import Code.Walls.bc69count

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


















theorem bfc_acyclic_of_walkInjHom {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (hH : H.IsAcyclic)
    (hinj : ∀ {v : V} (c : G.Walk v v), c.IsCycle →
      Set.InjOn f {x | x ∈ c.support}) :
    G.IsAcyclic := by
  intro v c hc
  have hinjc := hinj c hc
  have hcm : (c.map f).IsCycle := by
    rw [SimpleGraph.Walk.isCycle_def] at hc ⊢
    obtain ⟨htr, hne, hnodup⟩ := hc
    refine ⟨?_, ?_, ?_⟩
    · rw [SimpleGraph.Walk.isTrail_def] at htr ⊢
      rw [SimpleGraph.Walk.edges_map]
      apply List.Nodup.map_on _ htr
      intro e1 he1 e2 he2 hee
      induction e1 using Sym2.ind with | _ a1 b1 =>
      induction e2 using Sym2.ind with | _ a2 b2 =>
      simp only [Sym2.map_mk] at hee
      have ha1 : a1 ∈ c.support := c.fst_mem_support_of_mem_edges he1
      have hb1 : b1 ∈ c.support := c.snd_mem_support_of_mem_edges he1
      have ha2 : a2 ∈ c.support := c.fst_mem_support_of_mem_edges he2
      have hb2 : b2 ∈ c.support := c.snd_mem_support_of_mem_edges he2
      rw [Sym2.eq_iff] at hee ⊢
      rcases hee with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · left; exact ⟨hinjc ha1 ha2 e1, hinjc hb1 hb2 e2⟩
      · right; exact ⟨hinjc ha1 hb2 e1, hinjc hb1 ha2 e2⟩
    · intro h
      apply hne
      cases c with
      | nil => rfl
      | cons hh w => simp [SimpleGraph.Walk.map_cons] at h
    · rw [SimpleGraph.Walk.support_map, ← List.map_tail]
      apply List.Nodup.map_on _ hnodup
      intro x hx y hy hxy
      exact hinjc (List.mem_of_mem_tail hx) (List.mem_of_mem_tail hy) hxy
  exact hH (c.map f) hcm
















theorem bfc_disjointStar_acyclic (β : Type) : (bc64_starForest β).IsAcyclic :=
  bfc_acyclic_of_walkInjHom (bc64_sndHom β) bc64_starG_isTree.isAcyclic
    (fun c _ => bc64_snd_injOn_support c)



















theorem bfc_disjointStar_leaves_interior (hd : 1 ≤ d) {R : ℕ} (hR : 2 ≤ R) :
    bc112_leaf hd (0 : Site d) 1 ∉ vertexBoundary d R := by
  rw [vertexBoundary, Set.mem_diff, not_and_or, not_not]
  right
  rw [mem_box]
  intro i
  by_cases hi : i = ⟨0, hd⟩
  · subst hi
    rw [bc112_leaf_coord0]
    simp only [Pi.zero_apply, zero_add]
    rw [Int.natAbs_one]; omega
  · rw [bc112_leaf_coord_ne hd (0 : Site d) 1 hi]
    simp















theorem bfc_gap1_free (hd : 1 ≤ d) (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (hL : 3 ≤ L) :
    bc112_SeparatedArmGraph ω L R :=
  bc112_separatedArmGraph_holds hd ω L R hL





theorem bfc_bc69_nonvacuous (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d R) (hz₁ : z₁ ∈ vertexBoundary d R)
    (hzne : z₀ ≠ z₁) (hno : ∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) :
    bc69_Gn_globalForest ω L R :=
  bc69_globalForest_of_noTrif ω L R hz₀ hz₁ hzne hno


































theorem bfc_status (hd : 1 ≤ d) :
    
    (∀ (β : Type), (bc64_starForest β).IsAcyclic) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), 3 ≤ L → bc112_SeparatedArmGraph ω L R) ∧
    
    (∀ {R : ℕ}, 2 ≤ R → bc112_leaf hd (0 : Site d) 1 ∉ vertexBoundary d R) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (z₀ z₁ : Site d),
      z₀ ∈ vertexBoundary d R → z₁ ∈ vertexBoundary d R → z₀ ≠ z₁ →
      (∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) → bc69_Gn_globalForest ω L R) := by
  refine ⟨bfc_disjointStar_acyclic, ?_, ?_, ?_⟩
  · intro ω L R hL; exact bfc_gap1_free hd ω L R hL
  · intro R hR; exact bfc_disjointStar_leaves_interior hd hR
  · intro ω L R z₀ z₁ hz₀ hz₁ hzne hno; exact bfc_bc69_nonvacuous ω L R hz₀ hz₁ hzne hno

end StatMech.Walls
