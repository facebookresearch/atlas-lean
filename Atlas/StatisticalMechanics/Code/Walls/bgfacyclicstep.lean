/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/















































































import Mathlib
import Code.Walls.bc67supervertex

open Set SimpleGraph Finset
open scoped BigOperators

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation




















theorem bgf_acyclic_of_regionSep {V : Type*} {σ : V → Type*} (G : SimpleGraph V)
    (region : (t : V) → V → σ t)
    (H1 : ∀ t a b, G.Adj t a → G.Adj t b → a ≠ b → region t a ≠ region t b)
    (H2 : ∀ t a b (w : G.Walk a b), t ∉ w.support → region t a = region t b) :
    G.IsAcyclic := by
  intro v c hc
  cases c with
  | nil => exact SimpleGraph.Walk.IsCycle.not_of_nil hc
  | cons hva p =>
    rename_i a0
    
    have hp : p.IsPath := ((SimpleGraph.Walk.cons_isCycle_iff p hva).mp hc).1
    have h3 : 3 ≤ (SimpleGraph.Walk.cons hva p).length := hc.three_le_length
    have hplen : 2 ≤ p.length := by
      rw [SimpleGraph.Walk.length_cons] at h3; omega
    have hpnn : ¬ p.Nil := by rw [← SimpleGraph.Walk.length_eq_zero_iff]; omega
    have hprnn : ¬ p.reverse.Nil := by
      rw [← SimpleGraph.Walk.length_eq_zero_iff, SimpleGraph.Walk.length_reverse]; omega
    have hprpath : p.reverse.IsPath := hp.reverse
    
    set b := p.penultimate with hbdef
    have hvb : G.Adj v b := (p.adj_penultimate hpnn).symm
    
    have hab : a0 ≠ b := by
      intro hcon
      have h0 : p.getVert 0 = a0 := p.getVert_zero
      have hL : p.getVert (p.length - 1) = b := by rw [hbdef]
      have hidx : (0 : ℕ) = p.length - 1 :=
        hp.getVert_injOn (by rw [Set.mem_setOf_eq]; omega) (by rw [Set.mem_setOf_eq]; omega)
          (by rw [h0, hL]; exact hcon)
      omega
    
    have hsnd : p.reverse.snd = b := by
      rw [hbdef]
      change p.reverse.getVert 1 = p.getVert (p.length - 1)
      rw [SimpleGraph.Walk.getVert_reverse]
    
    have hvnotin : v ∉ ((p.reverse.tail).reverse).support := by
      rw [SimpleGraph.Walk.support_reverse, List.mem_reverse]
      intro hmem
      have hnd : (p.reverse.support).Nodup := (SimpleGraph.Walk.isPath_def _).1 hprpath
      rw [← SimpleGraph.Walk.cons_support_tail hprnn] at hnd
      exact (List.nodup_cons.mp hnd).1 hmem
    have key : region v a0 = region v (p.reverse.snd) :=
      H2 v a0 (p.reverse.snd) ((p.reverse.tail).reverse) hvnotin
    rw [hsnd] at key
    exact H1 v a0 b hva hvb hab key













theorem bgf_walkReach {V : Type*} (G : SimpleGraph V) (H : V → SimpleGraph V) (t : V)
    (hlift : ∀ a b, G.Adj a b → t ≠ a → t ≠ b → (H t).Reachable a b) :
    ∀ a b (w : G.Walk a b), t ∉ w.support → (H t).Reachable a b := by
  intro a b w
  induction w with
  | nil => intro _; exact SimpleGraph.Reachable.refl _
  | cons hadj p ih =>
    rename_i a' x _
    intro hnotin
    rw [SimpleGraph.Walk.support_cons, List.mem_cons, not_or] at hnotin
    obtain ⟨hne_a, hrest⟩ := hnotin
    have hne_x : t ≠ x := fun h => hrest (h ▸ p.start_mem_support)
    exact (hlift a' x hadj hne_a hne_x).trans (ih hrest)















theorem bgf_acyclic_of_reachSep {V : Type*} (G : SimpleGraph V) (H : V → SimpleGraph V)
    (H1 : ∀ t a b, G.Adj t a → G.Adj t b → a ≠ b → ¬ (H t).Reachable a b)
    (H2 : ∀ t a b (w : G.Walk a b), t ∉ w.support → (H t).Reachable a b) :
    G.IsAcyclic := by
  refine bgf_acyclic_of_regionSep G (fun t s => (H t).connectedComponentMk s) ?_ ?_
  · intro t a b hta htb hab hcc
    exact H1 t a b hta htb hab (SimpleGraph.ConnectedComponent.eq.mp hcc)
  · intro t a b w hnotin
    exact SimpleGraph.ConnectedComponent.eq.mpr (H2 t a b w hnotin)





theorem bgf_acyclic_of_edgeLift {V : Type*} (G : SimpleGraph V) (H : V → SimpleGraph V)
    (Hcut : ∀ t a b, G.Adj t a → G.Adj t b → a ≠ b → ¬ (H t).Reachable a b)
    (Hlift : ∀ t a b, G.Adj a b → t ≠ a → t ≠ b → (H t).Reachable a b) :
    G.IsAcyclic :=
  bgf_acyclic_of_reachSep G H Hcut
    (fun t a b w hnotin => bgf_walkReach G H t (Hlift t) a b w hnotin)













theorem bgf_step3_witness :
    (SimpleGraph.fromEdgeSet
      {s((0 : Fin 4), 1), s((0 : Fin 4), 2), s((0 : Fin 4), 3)}).IsAcyclic := by
  classical
  set G : SimpleGraph (Fin 4) := SimpleGraph.fromEdgeSet {s((0 : Fin 4), 1), s(0, 2), s(0, 3)} with hG
  
  have hedge0 : ∀ a b : Fin 4, G.Adj a b → a = 0 ∨ b = 0 := by
    intro a b hadj
    rw [hG, SimpleGraph.fromEdgeSet_adj] at hadj
    obtain ⟨hmem, _⟩ := hadj
    fin_cases a <;> fin_cases b <;> revert hmem <;> decide
  
  have havoid0 : ∀ a b (w : G.Walk a b), (0 : Fin 4) ∉ w.support → a = b := by
    intro a b w
    induction w with
    | nil => intro _; rfl
    | cons hadj p ih =>
      rename_i a' x _
      intro hnotin
      exfalso
      rw [SimpleGraph.Walk.support_cons, List.mem_cons, not_or] at hnotin
      obtain ⟨hne_a, hrest⟩ := hnotin
      rcases hedge0 a' x hadj with h | h
      · exact hne_a h.symm
      · exact hrest (h ▸ p.start_mem_support)
  refine bgf_acyclic_of_regionSep G (σ := fun _ => Fin 4)
    (fun t s => if t = 0 then s else 0) ?_ ?_
  · 
    intro t a b hta htb hab
    by_cases ht : t = 0
    · subst ht; simpa using hab
    · 
      exfalso
      have ha0 : a = 0 := (hedge0 t a hta).resolve_left ht
      have hb0 : b = 0 := (hedge0 t b htb).resolve_left ht
      exact hab (ha0.trans hb0.symm)
  · 
    intro t a b w hnotin
    by_cases ht : t = 0
    · subst ht; exact havoid0 a b w hnotin
    · simp only [if_neg ht]
















theorem bgf_bc67_walkReach {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ)
    {V : Type*} (G : SimpleGraph V) (embed : V → Site d) (t : V)
    (hlift : ∀ a b, G.Adj a b → t ≠ a → t ≠ b →
      (bc67_contractedLattice ω L (embed t)).Reachable (embed a) (embed b)) :
    ∀ a b (w : G.Walk a b), t ∉ w.support →
      (bc67_contractedLattice ω L (embed t)).Reachable (embed a) (embed b) := by
  intro a b w
  induction w with
  | nil => intro _; exact SimpleGraph.Reachable.refl _
  | cons hadj p ih =>
    rename_i a' x _
    intro hnotin
    rw [SimpleGraph.Walk.support_cons, List.mem_cons, not_or] at hnotin
    obtain ⟨hne_a, hrest⟩ := hnotin
    have hne_x : t ≠ x := fun h => hrest (h ▸ p.start_mem_support)
    exact (hlift a' x hadj hne_a hne_x).trans (ih hrest)










theorem bgf_bc67_acyclic {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ)
    {V : Type*} (G : SimpleGraph V) (embed : V → Site d)
    (Hcut : ∀ t a b, G.Adj t a → G.Adj t b → a ≠ b →
      ¬ (bc67_contractedLattice ω L (embed t)).Reachable (embed a) (embed b))
    (Hlift : ∀ t a b, G.Adj a b → t ≠ a → t ≠ b →
      (bc67_contractedLattice ω L (embed t)).Reachable (embed a) (embed b)) :
    G.IsAcyclic := by
  refine bgf_acyclic_of_regionSep G
    (fun t s => (bc67_contractedLattice ω L (embed t)).connectedComponentMk (embed s)) ?_ ?_
  · intro t a b hta htb hab hcc
    exact Hcut t a b hta htb hab (SimpleGraph.ConnectedComponent.eq.mp hcc)
  · intro t a b w hnotin
    exact SimpleGraph.ConnectedComponent.eq.mpr
      (bgf_bc67_walkReach ω L G embed t (Hlift t) a b w hnotin)

























theorem bgf_acyclicStep_status {d : ℕ} :
    
    (∀ {V : Type} {σ : V → Type} (G : SimpleGraph V) (region : (t : V) → V → σ t),
      (∀ t a b, G.Adj t a → G.Adj t b → a ≠ b → region t a ≠ region t b) →
      (∀ t a b (w : G.Walk a b), t ∉ w.support → region t a = region t b) →
      G.IsAcyclic) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) {V : Type} (G : SimpleGraph V) (embed : V → Site d),
      (∀ t a b, G.Adj t a → G.Adj t b → a ≠ b →
        ¬ (bc67_contractedLattice ω L (embed t)).Reachable (embed a) (embed b)) →
      (∀ t a b, G.Adj a b → t ≠ a → t ≠ b →
        (bc67_contractedLattice ω L (embed t)).Reachable (embed a) (embed b)) →
      G.IsAcyclic) ∧
    
    ((SimpleGraph.fromEdgeSet
      {s((0 : Fin 4), 1), s((0 : Fin 4), 2), s((0 : Fin 4), 3)}).IsAcyclic) := by
  refine ⟨?_, ?_, ?_⟩
  · intro V σ G region H1 H2; exact bgf_acyclic_of_regionSep G region H1 H2
  · intro ω L V G embed Hcut Hlift; exact bgf_bc67_acyclic ω L G embed Hcut Hlift
  · exact bgf_step3_witness

end StatMech.Walls
