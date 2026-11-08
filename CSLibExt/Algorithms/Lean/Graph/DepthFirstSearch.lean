/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.DirectedAdjacency

import Mathlib.Data.Finset.Card
import Std.Data.HashSet.Lemmas

/-!
# Depth-first search on ordered directed-adjacency graphs

This module implements left-first depth-first search with discovery order,
finish order, and discovering-parent edges. The executable uses a linearly
threaded `Std.HashSet` for visited vertices and reverse-list accumulators.
With expected constant-time lawful hashing and adjacency lists whose total
length is `E`, traversal takes expected `O(R + V + E)` time for `R` scheduled
roots and `V` discovered vertices.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.DepthFirstSearch

universe u

set_option warn.classDefReducibility false in
attribute [local instance 5] instDecidableEqOfLawfulBEq

/-- The ordered, duplicate-free output of a depth-first traversal. Parent pairs
are stored as `(child, parent)`. -/
structure Traversal (V : Type u) where
  preorder : List V
  postorder : List V
  parents : List (V × V)
deriving Repr, DecidableEq

private def RootedReachable {V : Type u} (graph : DirectedAdjacency V)
    (roots : List V) (vertex : V) : Prop :=
  ∃ root ∈ roots, graph.Reachable root vertex

namespace Internal

inductive Frame (V : Type u) where
  | enter (parent : Option V) (vertex : V)
  | exit (vertex : V)
deriving DecidableEq

structure Machine (V : Type u) [BEq V] [Hashable V] where
  work : List (Frame V)
  visited : Std.HashSet V
  preorderRev : List V
  postorderRev : List V
  parentsRev : List (V × V)

def enterFrames {V : Type u} (parent : Option V) (xs : List V) : List (Frame V) :=
  xs.map (Frame.enter parent)

def initial {V : Type u} [BEq V] [Hashable V] [LawfulBEq V] (roots : List V) : Machine V where
  work := enterFrames none roots
  visited := ∅
  preorderRev := []
  postorderRev := []
  parentsRev := []

def finish {V : Type u} [BEq V] [Hashable V] (s : Machine V) : Traversal V where
  preorder := s.preorderRev.reverse
  postorder := s.postorderRev.reverse
  parents := s.parentsRev.reverse

def loop {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) (s : Machine V) : Machine V :=
  match _hwork : s.work with
  | [] => s
  | Frame.exit v :: work =>
      loop adj roots { s with work := work, postorderRev := v :: s.postorderRev }
  | Frame.enter parent v :: work =>
      if _hv : v ∈ s.visited then
        loop adj roots { s with work := work }
      else
        let parentsRev :=
          match parent with
          | none => s.parentsRev
          | some u => (v, u) :: s.parentsRev
        loop adj roots {
          work := enterFrames (some v) (adj.adjacency v) ++ Frame.exit v :: work
          visited := s.visited.insert v
          preorderRev := v :: s.preorderRev
          postorderRev := s.postorderRev
          parentsRev := parentsRev
        }
termination_by (adj.vertices.length - s.visited.size, s.work.length)
decreasing_by
  · apply Prod.Lex.right
    simp [_hwork]
  · apply Prod.Lex.right
    simp [_hwork]
  · apply Prod.Lex.left
    rw [Std.HashSet.size_insert]
    simp only [_hv, ↓reduceIte]
    have hnodup : s.visited.toList.Nodup := by
      apply List.nodup_iff_pairwise_ne.mpr
      simpa only [beq_eq_false_iff_ne] using s.visited.distinct_toList
    have hproper : s.visited.toList.toFinset ⊂ adj.vertices.toFinset :=
      Finset.ssubset_iff_subset_ne.mpr ⟨by
        intro vertex _
        exact List.mem_toFinset.mpr (adj.vertices_complete vertex), by
        intro h
        apply _hv
        have : v ∈ adj.vertices.toFinset :=
          List.mem_toFinset.mpr (adj.vertices_complete v)
        have : v ∈ s.visited.toList.toFinset := by rwa [h]
        exact Std.HashSet.mem_toList.mp (List.mem_toFinset.mp this)⟩
    have hcard : s.visited.size < adj.vertices.length := by
      rw [← Std.HashSet.length_toList,
        ← List.toFinset_card_of_nodup hnodup,
        ← List.toFinset_card_of_nodup adj.vertices_nodup]
      exact Finset.card_lt_card hproper
    omega

end Internal

open Internal

/-- Execute left-to-right depth-first search from an ordered list of roots. -/
def dfs {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) : Traversal V :=
  finish (loop adj roots (initial roots))

namespace Internal

inductive Step {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) :
    Machine V → Machine V → Prop where
  | skip (s : Machine V) (parent : Option V) (v : V) (work : List (Frame V))
      (hw : s.work = Frame.enter parent v :: work) (hv : v ∈ s.visited) :
      Step adj roots s { s with work := work }
  | discover (s : Machine V) (parent : Option V) (v : V) (work : List (Frame V))
      (hw : s.work = Frame.enter parent v :: work) (hv : v ∉ s.visited) :
      Step adj roots s {
        work := enterFrames (some v) (adj.adjacency v) ++ Frame.exit v :: work
        visited := s.visited.insert v
        preorderRev := v :: s.preorderRev
        postorderRev := s.postorderRev
        parentsRev :=
          match parent with
          | none => s.parentsRev
          | some u => (v, u) :: s.parentsRev
      }
  | exit (s : Machine V) (v : V) (work : List (Frame V))
      (hw : s.work = Frame.exit v :: work) :
      Step adj roots s { s with work := work, postorderRev := v :: s.postorderRev }

/-- Zero or more independent DFS machine steps. -/
abbrev Steps {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) :=
  Relation.ReflTransGen (Step adj roots)

end Internal

private def exitVertices {V : Type u} : List (Frame V) → List V
  | [] => []
  | Frame.enter _ _ :: work => exitVertices work
  | Frame.exit v :: work => v :: exitVertices work

@[simp] private theorem exitVertices_append {V : Type u} (a b : List (Frame V)) :
    exitVertices (a ++ b) = exitVertices a ++ exitVertices b := by
  induction a with
  | nil => rfl
  | cons f a ih => cases f <;> simp [exitVertices, ih]

@[simp] private theorem exitVertices_enterFrames {V : Type u}
    (parent : Option V) (xs : List V) : exitVertices (enterFrames parent xs) = [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change exitVertices (Frame.enter parent x :: enterFrames parent xs) = []
    simp [exitVertices, ih]

@[simp] private theorem exitVertices_map_enter {V : Type u}
    (parent : Option V) (xs : List V) :
    exitVertices (xs.map (Frame.enter parent)) = [] := by
  change exitVertices (enterFrames parent xs) = []
  exact exitVertices_enterFrames parent xs

private def DiscoveryInv {V : Type u} [BEq V] [Hashable V] [LawfulBEq V] (s : Machine V) : Prop :=
  (∀ v, v ∈ s.visited ↔ v ∈ s.preorderRev) ∧ s.preorderRev.Nodup

private def FinishInv {V : Type u} [BEq V] [Hashable V] [LawfulBEq V] (s : Machine V) : Prop :=
  (∀ v, v ∈ s.visited ↔ v ∈ exitVertices s.work ∨ v ∈ s.postorderRev) ∧
  (exitVertices s.work).Nodup ∧ s.postorderRev.Nodup ∧
  List.Disjoint (exitVertices s.work) s.postorderRev

private theorem discoveryInv_initial {V : Type u}
    [BEq V] [Hashable V] [LawfulBEq V] (roots : List V) :
    DiscoveryInv (initial roots) := by
  simp [DiscoveryInv, initial]

private theorem finishInv_initial {V : Type u} [BEq V] [Hashable V] [LawfulBEq V] (roots : List V) :
    FinishInv (initial roots) := by
  simp [FinishInv, initial, enterFrames]

private theorem discoveryInv_step {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) (a b : Machine V)
    (hab : Step adj roots a b) (ha : DiscoveryInv a) : DiscoveryInv b := by
  cases hab with
  | skip parent v work hw hv => exact ha
  | exit v work hw => exact ha
  | discover parent v work hw hv =>
      rcases ha with ⟨hmem, hnodup⟩
      constructor
      · intro x
        change x ∈ a.visited.insert v ↔ x ∈ v :: a.preorderRev
        constructor
        · intro hx
          rcases Std.HashSet.mem_insert.mp hx with hx | hx
          · exact List.mem_cons.mpr (Or.inl (beq_iff_eq.mp hx).symm)
          · exact List.mem_cons.mpr (Or.inr ((hmem x).mp hx))
        · intro hx
          rcases List.mem_cons.mp hx with hx | hx
          · exact Std.HashSet.mem_insert.mpr (Or.inl (beq_iff_eq.mpr hx.symm))
          · exact Std.HashSet.mem_insert.mpr (Or.inr ((hmem x).mpr hx))
      · exact List.nodup_cons.mpr ⟨fun h => hv ((hmem v).mpr h), hnodup⟩

private theorem finishInv_step {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) (a b : Machine V)
    (hab : Step adj roots a b) (ha : FinishInv a) : FinishInv b := by
  cases hab <;> simp_all [FinishInv, exitVertices, enterFrames, List.disjoint_cons_left,
    List.disjoint_cons_right] <;> aesop

private def ReachInv {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) (s : Machine V) : Prop :=
  (∀ parent v, Frame.enter parent v ∈ s.work → RootedReachable adj roots v) ∧
  (∀ v, v ∈ s.visited → RootedReachable adj roots v)

private theorem reachable_edge {V : Type u} {adj : DirectedAdjacency V} {roots : List V} {u v : V}
    (hu : RootedReachable adj roots u) (huv : adj.Edge u v) : RootedReachable adj roots v := by
  rcases hu with ⟨r, hr, hru⟩
  exact ⟨r, hr, hru.tail huv⟩

private theorem reachInv_initial {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V)
    (roots : List V) : ReachInv adj roots (initial roots) := by
  constructor
  · intro parent v h
    have h' : v ∈ roots ∧ none = parent := by
      simpa [initial, enterFrames] using h
    rcases h' with ⟨hv, rfl⟩
    exact ⟨v, hv, .refl⟩
  · simp [initial]

private theorem reachInv_step {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) (a b : Machine V)
    (hab : Step adj roots a b) (ha : ReachInv adj roots a) : ReachInv adj roots b := by
  rcases ha with ⟨hwork, hvisited⟩
  cases hab with
  | skip parent v work hw hv =>
      constructor
      · intro p x hx
        apply hwork p x
        rw [hw]
        exact List.mem_cons_of_mem _ hx
      · exact hvisited
  | discover parent v work hw hv =>
      have hreachv : RootedReachable adj roots v := hwork parent v (by simp [hw])
      constructor
      · intro p x hx
        have hx' : (x ∈ adj.adjacency v ∧ some v = p) ∨
            Frame.enter p x ∈ work := by
          simpa [enterFrames] using hx
        rcases hx' with hx | hx
        · rcases hx with ⟨hEdge, _⟩
          exact reachable_edge hreachv hEdge
        · apply hwork p x
          rw [hw]
          exact List.mem_cons_of_mem _ hx
      · intro x hx
        rw [Std.HashSet.mem_insert] at hx
        rcases hx with hx | hx
        · have : v = x := by simpa using hx
          subst x
          exact hreachv
        · exact hvisited x hx
  | exit v work hw =>
      constructor
      · intro p x hx
        exact hwork p x (by simp [hw, hx])
      · exact hvisited

private def PendingInv {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) (s : Machine V) : Prop :=
  (∀ r, r ∈ roots → r ∈ s.visited ∨ ∃ parent, Frame.enter parent r ∈ s.work) ∧
  (∀ u, u ∈ s.visited → ∀ v, adj.Edge u v →
    v ∈ s.visited ∨ ∃ parent, Frame.enter parent v ∈ s.work)

private theorem pendingInv_initial {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V)
    (roots : List V) : PendingInv adj roots (initial roots) := by
  constructor
  · intro r hr
    right
    exact ⟨none, by simp [initial, enterFrames, hr]⟩
  · simp [initial]

private theorem pendingInv_step {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) (a b : Machine V)
    (hab : Step adj roots a b) (ha : PendingInv adj roots a) : PendingInv adj roots b := by
  rcases ha with ⟨hroots, hedges⟩
  cases hab with
  | skip parent v work hw hv =>
      constructor
      · intro r hr
        rcases hroots r hr with h | ⟨p, hp⟩
        · exact Or.inl h
        · rw [hw] at hp
          simp only [List.mem_cons, Frame.enter.injEq] at hp
          rcases hp with ⟨rfl, rfl⟩ | hp
          · exact Or.inl hv
          · exact Or.inr ⟨p, hp⟩
      · intro u hu x hux
        rcases hedges u hu x hux with h | ⟨p, hp⟩
        · exact Or.inl h
        · rw [hw] at hp
          simp only [List.mem_cons, Frame.enter.injEq] at hp
          rcases hp with ⟨rfl, rfl⟩ | hp
          · exact Or.inl hv
          · exact Or.inr ⟨p, hp⟩
  | discover parent v work hw hv =>
      constructor
      · intro r hr
        rcases hroots r hr with h | ⟨p, hp⟩
        · exact Or.inl (Std.HashSet.mem_insert.mpr (Or.inr h))
        · rw [hw] at hp
          simp only [List.mem_cons, Frame.enter.injEq] at hp
          rcases hp with ⟨rfl, rfl⟩ | hp
          · exact Or.inl Std.HashSet.mem_insert_self
          · exact Or.inr ⟨p, by simp [hp]⟩
      · intro u hu x hux
        rw [Std.HashSet.mem_insert] at hu
        rcases hu with hu | hu
        · have : v = u := by simpa using hu
          subst u
          right
          refine ⟨some v, ?_⟩
          simp only [List.mem_append]
          left
          simpa [enterFrames, DirectedAdjacency.Edge] using hux
        · rcases hedges u hu x hux with h | ⟨p, hp⟩
          · exact Or.inl (Std.HashSet.mem_insert.mpr (Or.inr h))
          · rw [hw] at hp
            simp only [List.mem_cons, Frame.enter.injEq] at hp
            rcases hp with ⟨rfl, rfl⟩ | hp
            · exact Or.inl Std.HashSet.mem_insert_self
            · exact Or.inr ⟨p, by simp [hp]⟩
  | exit v work hw =>
      constructor
      · intro r hr
        rcases hroots r hr with h | ⟨p, hp⟩
        · exact Or.inl h
        · exact Or.inr ⟨p, by simpa [hw] using hp⟩
      · intro u hu x hux
        rcases hedges u hu x hux with h | ⟨p, hp⟩
        · exact Or.inl h
        · exact Or.inr ⟨p, by simpa [hw] using hp⟩

private theorem discoveryInv_steps {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) (a b : Machine V)
    (hab : Steps adj roots a b) (ha : DiscoveryInv a) : DiscoveryInv b := by
  induction hab with
  | refl => exact ha
  | tail h step ih => exact discoveryInv_step adj roots _ _ step ih

private theorem finishInv_steps {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) (a b : Machine V)
    (hab : Steps adj roots a b) (ha : FinishInv a) : FinishInv b := by
  induction hab with
  | refl => exact ha
  | tail h step ih => exact finishInv_step adj roots _ _ step ih

private theorem reachInv_steps {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) (a b : Machine V)
    (hab : Steps adj roots a b) (ha : ReachInv adj roots a) : ReachInv adj roots b := by
  induction hab with
  | refl => exact ha
  | tail h step ih => exact reachInv_step adj roots _ _ step ih

private theorem pendingInv_steps {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) (a b : Machine V)
    (hab : Steps adj roots a b) (ha : PendingInv adj roots a) : PendingInv adj roots b := by
  induction hab with
  | refl => exact ha
  | tail h step ih => exact pendingInv_step adj roots _ _ step ih

private theorem loop_steps {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) (s : Machine V) :
    Steps adj roots s (loop adj roots s) ∧ (loop adj roots s).work = [] := by
  fun_induction loop adj roots s
  case case1 s hw => exact ⟨Relation.ReflTransGen.refl, hw⟩
  case case2 s v work hw ih =>
    exact ⟨Relation.ReflTransGen.head
      (Step.exit (adj := adj) (roots := roots) s v work hw) ih.1, ih.2⟩
  case case3 s parent v work hw hv ih =>
    exact ⟨Relation.ReflTransGen.head
      (Step.skip (adj := adj) (roots := roots) s parent v work hw hv) ih.1, ih.2⟩
  case case4 s parent v work hw hv parents ih =>
    exact ⟨Relation.ReflTransGen.head
      (Step.discover (adj := adj) (roots := roots) s parent v work hw hv) ih.1, ih.2⟩

/-- A traversal conforms to left-first DFS when it is the result of the declarative
machine relation that consumes roots from left to right and, on discovery, places
the ordered adjacency list before the vertex's exit and all remaining work. -/
def IsLeftFirstDFS {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) (traversal : Traversal V) : Prop :=
  ∃ final, Steps adj roots (initial roots) final ∧ final.work = [] ∧
    finish final = traversal

/-- The executable traversal conforms to the ordered relational DFS specification. -/
theorem dfs_is_left_first {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) :
    IsLeftFirstDFS adj roots (dfs adj roots) := by
  exact ⟨loop adj roots (initial roots), (loop_steps adj roots (initial roots)).1,
    (loop_steps adj roots (initial roots)).2, rfl⟩

private theorem loop_eq_of_step {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) (a b : Machine V)
    (hab : Step adj roots a b) : loop adj roots a = loop adj roots b := by
  cases hab with
  | skip parent v work hw hv =>
      cases a with
      | mk scheduled visited preorderRev postorderRev parentsRev =>
          simp only at hw
          subst scheduled
          simp only at hv
          rw (occs := .pos [1]) [loop.eq_1]
          simp only
          split <;> rename_i h
          · rfl
          · exact (h hv).elim
  | discover parent v work hw hv =>
      cases a with
      | mk scheduled visited preorderRev postorderRev parentsRev =>
          simp only at hw
          subst scheduled
          simp only at hv
          rw (occs := .pos [1]) [loop.eq_1]
          simp only
          split <;> rename_i h
          · exact (hv h).elim
          · cases parent <;> rfl
  | exit v work hw =>
      cases a with
      | mk scheduled visited preorderRev postorderRev parentsRev =>
          simp only at hw
          subst scheduled
          simp only at ⊢
          rw (occs := .pos [1]) [loop.eq_1]

private theorem loop_eq_of_steps {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) (a b : Machine V)
    (hab : Steps adj roots a b) : loop adj roots a = loop adj roots b := by
  induction hab with
  | refl => rfl
  | tail h step ih => exact ih.trans (loop_eq_of_step adj roots _ _ step)

/-- The ordered relational specification determines exactly the executable traversal. -/
theorem IsLeftFirstDFS.eq_dfs {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    {adj : DirectedAdjacency V} {roots : List V} {traversal : Traversal V}
    (h : IsLeftFirstDFS adj roots traversal) : traversal = dfs adj roots := by
  rcases h with ⟨final, hsteps, hwork, hfinish⟩
  have hloop := loop_eq_of_steps adj roots _ _ hsteps
  have hterminal : loop adj roots final = final := by
    cases final with
    | mk work visited preorderRev postorderRev parentsRev =>
        simp only at hwork
        subst work
        rw [loop.eq_1]
  rw [hterminal] at hloop
  rw [← hfinish, dfs, hloop]

private theorem final_discoveryInv {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) :
    DiscoveryInv (loop adj roots (initial roots)) :=
  discoveryInv_steps adj roots _ _ (loop_steps adj roots (initial roots)).1
    (discoveryInv_initial roots)

private theorem final_finishInv {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) :
    FinishInv (loop adj roots (initial roots)) :=
  finishInv_steps adj roots _ _ (loop_steps adj roots (initial roots)).1
    (finishInv_initial roots)

private theorem final_reachInv {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) :
    ReachInv adj roots (loop adj roots (initial roots)) :=
  reachInv_steps adj roots _ _ (loop_steps adj roots (initial roots)).1
    (reachInv_initial adj roots)

private theorem final_pendingInv {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) :
    PendingInv adj roots (loop adj roots (initial roots)) :=
  pendingInv_steps adj roots _ _ (loop_steps adj roots (initial roots)).1
    (pendingInv_initial adj roots)

/-- Every vertex in DFS preorder is directed-reachable from a supplied root. -/
theorem preorder_sound {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) (v : V)
    (hv : v ∈ (dfs adj roots).preorder) :
    ∃ root ∈ roots, adj.Reachable root v := by
  change RootedReachable adj roots v
  have hmem : v ∈ (loop adj roots (initial roots)).preorderRev := by
    simpa [dfs, finish] using hv
  have hvisited := (final_discoveryInv adj roots).1 v |>.mpr hmem
  exact (final_reachInv adj roots).2 v hvisited

private theorem final_roots_visited {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) (r : V) (hr : r ∈ roots) :
    r ∈ (loop adj roots (initial roots)).visited := by
  rcases (final_pendingInv adj roots).1 r hr with h | ⟨parent, hp⟩
  · exact h
  · have hempty := (loop_steps adj roots (initial roots)).2
    rw [hempty] at hp
    simp at hp

private theorem final_edge_closed {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) (u v : V)
    (hu : u ∈ (loop adj roots (initial roots)).visited) (huv : adj.Edge u v) :
    v ∈ (loop adj roots (initial roots)).visited := by
  rcases (final_pendingInv adj roots).2 u hu v huv with h | ⟨parent, hp⟩
  · exact h
  · have hempty := (loop_steps adj roots (initial roots)).2
    rw [hempty] at hp
    simp at hp

/-- Every directed-reachable vertex occurs in DFS preorder. -/
theorem preorder_complete {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) (v : V)
    (hv : ∃ root ∈ roots, adj.Reachable root v) :
    v ∈ (dfs adj roots).preorder := by
  change RootedReachable adj roots v at hv
  rcases hv with ⟨r, hr, hrv⟩
  have hvisited : v ∈ (loop adj roots (initial roots)).visited := by
    induction hrv with
    | refl => exact final_roots_visited adj roots r hr
    | tail h huv ih => exact final_edge_closed adj roots _ _ ih huv
  have hmem := (final_discoveryInv adj roots).1 v |>.mp hvisited
  simpa [dfs, finish] using hmem

/-- DFS preorder enumerates exactly the vertices reachable from the roots. -/
theorem mem_preorder_iff_reachable {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) (v : V) :
    v ∈ (dfs adj roots).preorder ↔
      ∃ root ∈ roots, adj.Reachable root v :=
  ⟨preorder_sound adj roots v, preorder_complete adj roots v⟩

/-- DFS discovers each reachable vertex at most once. -/
theorem preorder_nodup {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) : (dfs adj roots).preorder.Nodup := by
  simpa [dfs, finish] using (final_discoveryInv adj roots).2

private theorem final_mem_postorderRev_iff_visited {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) (v : V) :
    v ∈ (loop adj roots (initial roots)).postorderRev ↔
      v ∈ (loop adj roots (initial roots)).visited := by
  have h := (final_finishInv adj roots).1 v
  rw [(loop_steps adj roots (initial roots)).2] at h
  simpa [exitVertices] using h.symm

/-- Finish order contains exactly the vertices reachable from the roots. -/
theorem mem_postorder_iff_reachable {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) (v : V) :
    v ∈ (dfs adj roots).postorder ↔
      ∃ root ∈ roots, adj.Reachable root v := by
  rw [← mem_preorder_iff_reachable adj roots v]
  simp only [dfs, finish, List.mem_reverse]
  exact (final_mem_postorderRev_iff_visited adj roots v).trans
    ((final_discoveryInv adj roots).1 v)

/-- Every discovered vertex finishes exactly once. -/
theorem postorder_nodup {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) : (dfs adj roots).postorder.Nodup := by
  have h := (final_finishInv adj roots).2.2.1
  simpa [dfs, finish] using h

/-- `Before x y xs` means that `x` occurs strictly before `y` in `xs`. -/
def Before {V : Type u} (x y : V) (xs : List V) : Prop :=
  ∃ a b c, xs = a ++ x :: b ++ y :: c

/-- The parent relation represented by `(child, parent)` pairs. -/
def ParentRel {V : Type u} (parents : List (V × V)) (child parent : V) : Prop :=
  (child, parent) ∈ parents

private def WorkForestInv {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) (s : Machine V) : Prop :=
  ∀ parent v, Frame.enter parent v ∈ s.work →
    match parent with
    | none => v ∈ roots
    | some u => u ∈ s.visited ∧ adj.Edge u v

private theorem workForestInv_initial {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) : WorkForestInv adj roots (initial roots) := by
  intro parent v h
  have h' : v ∈ roots ∧ none = parent := by
    simpa [initial, enterFrames] using h
  rcases h' with ⟨hv, rfl⟩
  exact hv

private theorem workForestInv_step {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) (a b : Machine V)
    (hab : Step adj roots a b) (ha : WorkForestInv adj roots a) :
    WorkForestInv adj roots b := by
  cases hab with
  | skip parent v work hw hv =>
      intro p x hx
      apply ha p x
      rw [hw]
      exact List.mem_cons_of_mem _ hx
  | discover parent v work hw hv =>
      intro p x hx
      have hx' : (x ∈ adj.adjacency v ∧ some v = p) ∨
          Frame.enter p x ∈ work := by
        simpa [enterFrames] using hx
      rcases hx' with hx | hx
      · rcases hx with ⟨hEdge, hp⟩
        cases hp
        exact ⟨Std.HashSet.mem_insert_self, hEdge⟩
      · have hold := ha p x (by
          rw [hw]
          exact List.mem_cons_of_mem _ hx)
        cases p with
        | none => exact hold
        | some u =>
            exact ⟨Std.HashSet.mem_insert.mpr (Or.inr hold.1), hold.2⟩
  | exit v work hw =>
      intro p x hx
      apply ha p x
      rw [hw]
      exact List.mem_cons_of_mem _ hx

private theorem before_cons {V : Type u} {x y z : V} {xs : List V}
    (h : Before x y xs) : Before x y (z :: xs) := by
  rcases h with ⟨a, b, c, rfl⟩
  exact ⟨z :: a, b, c, by simp⟩

private theorem before_cons_of_mem {V : Type u} {x y : V} {xs : List V}
    (hy : y ∈ xs) : Before x y (x :: xs) := by
  rcases List.append_of_mem hy with ⟨a, b, rfl⟩
  exact ⟨[], a, b, by simp⟩

private theorem before_cons_cases {V : Type u} {x y z : V} {xs : List V}
    (h : Before x y (z :: xs)) : (x = z ∧ y ∈ xs) ∨ Before x y xs := by
  rcases h with ⟨a, b, c, h⟩
  cases a with
  | nil =>
      simp only [List.nil_append] at h
      rcases h with ⟨rfl, rfl⟩
      exact Or.inl ⟨rfl, by simp⟩
  | cons q a =>
      simp only [List.cons_append, List.cons.injEq] at h
      rcases h with ⟨rfl, h⟩
      exact Or.inr ⟨a, b, c, h⟩

private def WorkOrder {V : Type u} : List (Frame V) → Prop
  | [] => True
  | Frame.enter none _ :: work => WorkOrder work
  | Frame.enter (some parent) _ :: work => Frame.exit parent ∈ work ∧ WorkOrder work
  | Frame.exit _ :: work => WorkOrder work

private theorem workOrder_enterNone {V : Type u} (roots : List V) :
    WorkOrder (enterFrames none roots) := by
  induction roots with
  | nil => trivial
  | cons r roots ih => exact ih

private theorem workOrder_push {V : Type u} (v : V) (neighbors : List V)
    (work : List (Frame V)) (h : WorkOrder work) :
    WorkOrder (enterFrames (some v) neighbors ++ Frame.exit v :: work) := by
  induction neighbors with
  | nil => exact h
  | cons x xs ih =>
      constructor
      · simp
      · exact ih

private theorem workOrder_step {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) (a b : Machine V)
    (hab : Step adj roots a b) (ha : WorkOrder a.work) : WorkOrder b.work := by
  cases hab with
  | skip parent v work hw hv =>
      rw [hw] at ha
      cases parent with
      | none => exact ha
      | some u => exact ha.2
  | discover parent v work hw hv =>
      rw [hw] at ha
      have htail : WorkOrder work := by
        cases parent with
        | none => exact ha
        | some u => exact ha.2
      exact workOrder_push v (adj.adjacency v) work htail
  | exit v work hw =>
      rw [hw] at ha
      exact ha

private theorem exit_mem_exitVertices {V : Type u} {v : V} {work : List (Frame V)}
    (h : Frame.exit v ∈ work) : v ∈ exitVertices work := by
  induction work with
  | nil => simp at h
  | cons f work ih =>
      cases f with
      | enter parent x =>
          simp only [List.mem_cons] at h
          rcases h with h | h
          · cases h
          · exact ih h
      | exit x =>
          simp only [List.mem_cons, Frame.exit.injEq] at h
          simp only [exitVertices, List.mem_cons]
          rcases h with rfl | h
          · exact Or.inl rfl
          · exact Or.inr (ih h)

private def FinishForestInv {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (s : Machine V) : Prop :=
  ∀ child parent, (child, parent) ∈ s.parentsRev →
    Before child parent (exitVertices s.work) ∨
    (child ∈ s.postorderRev ∧ parent ∈ exitVertices s.work) ∨
    Before parent child s.postorderRev

private theorem finishForestInv_step {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) (a b : Machine V)
    (hab : Step adj roots a b) (horder : WorkOrder a.work)
    (ha : FinishForestInv a) : FinishForestInv b := by
  cases hab with
  | skip parent v work hw hv =>
      simpa [FinishForestInv, hw, exitVertices] using ha
  | discover parent v work hw hv =>
      unfold FinishForestInv at ha ⊢
      rw [hw] at ha horder
      intro child p hcp
      cases parent with
      | none =>
          rcases ha child p hcp with hactive | hfinished | hdone
          · exact Or.inl (by simpa [exitVertices] using before_cons (z := v) hactive)
          · have hpactive : p ∈ exitVertices (Frame.exit v :: work) := by
              simpa [exitVertices] using List.mem_cons_of_mem v hfinished.2
            exact Or.inr (Or.inl ⟨hfinished.1, by simpa [exitVertices] using hpactive⟩)
          · exact Or.inr (Or.inr hdone)
      | some u =>
          simp only [List.mem_cons, Prod.mk.injEq] at hcp
          rcases hcp with hnew | hcp
          · have hc : child = v := hnew.1
            have hp : p = u := hnew.2
            subst child
            subst p
            have hexit : Frame.exit u ∈ work := horder.1
            exact Or.inl (by simpa [exitVertices] using
              before_cons_of_mem (x := v) (exit_mem_exitVertices hexit))
          · rcases ha child p hcp with hactive | hfinished | hdone
            · exact Or.inl (by simpa [exitVertices] using before_cons (z := v) hactive)
            · have hpactive : p ∈ exitVertices (Frame.exit v :: work) := by
                simpa [exitVertices] using List.mem_cons_of_mem v hfinished.2
              exact Or.inr (Or.inl ⟨hfinished.1, by simpa [exitVertices] using hpactive⟩)
            · exact Or.inr (Or.inr hdone)
  | exit v work hw =>
      intro child parent hcp
      rcases ha child parent hcp with hactive | hfinished | hdone
      · rw [hw] at hactive
        simp only [exitVertices] at hactive
        rcases before_cons_cases hactive with ⟨rfl, hparent⟩ | hactive
        · exact Or.inr (Or.inl ⟨by simp, hparent⟩)
        · exact Or.inl hactive
      · rw [hw] at hfinished
        simp only [exitVertices, List.mem_cons] at hfinished
        rcases hfinished.2 with rfl | hparent
        · exact Or.inr (Or.inr (before_cons_of_mem hfinished.1))
        · exact Or.inr (Or.inl ⟨by simp [hfinished.1], hparent⟩)
      · exact Or.inr (Or.inr (before_cons hdone))

private def FullFinishInv {V : Type u} [BEq V] [Hashable V] [LawfulBEq V] (s : Machine V) : Prop :=
  WorkOrder s.work ∧ FinishForestInv s

private theorem fullFinishInv_initial {V : Type u}
    [BEq V] [Hashable V] [LawfulBEq V] (roots : List V) :
    FullFinishInv (initial roots) := by
  constructor
  · exact workOrder_enterNone roots
  · simp [FinishForestInv, initial]

private theorem fullFinishInv_step {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) (a b : Machine V)
    (hab : Step adj roots a b) (ha : FullFinishInv a) : FullFinishInv b :=
  ⟨workOrder_step adj roots a b hab ha.1,
    finishForestInv_step adj roots a b hab ha.1 ha.2⟩

private theorem fullFinishInv_steps {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) (a b : Machine V)
    (hab : Steps adj roots a b) (ha : FullFinishInv a) : FullFinishInv b := by
  induction hab with
  | refl => exact ha
  | tail h step ih => exact fullFinishInv_step adj roots _ _ step ih

private theorem final_finishForestInv {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) :
    FinishForestInv (loop adj roots (initial roots)) :=
  (fullFinishInv_steps adj roots _ _ (loop_steps adj roots (initial roots)).1
    (fullFinishInv_initial roots)).2

private def ForestInv {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) (s : Machine V) : Prop :=
  (∀ child parent, (child, parent) ∈ s.parentsRev →
    adj.Edge parent child ∧ child ∈ s.visited ∧ parent ∈ s.visited ∧
      Before child parent s.preorderRev) ∧
  (s.parentsRev.map Prod.fst).Nodup ∧
  (∀ v, v ∈ s.visited → ∃ r ∈ roots,
    Relation.ReflTransGen (ParentRel s.parentsRev) v r)

private theorem forestInv_initial {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) : ForestInv adj roots (initial roots) := by
  simp [ForestInv, initial]

private theorem forestInv_step {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) (a b : Machine V)
    (hab : Step adj roots a b) (hwork : WorkForestInv adj roots a)
    (hdisc : DiscoveryInv a) (ha : ForestInv adj roots a) : ForestInv adj roots b := by
  cases hab with
  | skip parent v work hw hv => exact ha
  | exit v work hw => exact ha
  | discover parent v work hw hv =>
      rcases ha with ⟨hfacts, hnodup, hchains⟩
      have hparent := hwork parent v (by simp [hw])
      cases parent with
      | none =>
          change (∀ child p, (child, p) ∈ a.parentsRev →
              adj.Edge p child ∧ child ∈ a.visited.insert v ∧
                p ∈ a.visited.insert v ∧ Before child p (v :: a.preorderRev)) ∧
            (a.parentsRev.map Prod.fst).Nodup ∧
            (∀ x, x ∈ a.visited.insert v → ∃ r ∈ roots,
              Relation.ReflTransGen (ParentRel a.parentsRev) x r)
          refine ⟨?_, hnodup, ?_⟩
          · intro child p hcp
            rcases hfacts child p hcp with ⟨hedge, hc, hp, hbefore⟩
            exact ⟨hedge, Std.HashSet.mem_insert.mpr (Or.inr hc),
              Std.HashSet.mem_insert.mpr (Or.inr hp), before_cons hbefore⟩
          · intro x hx
            rw [Std.HashSet.mem_insert] at hx
            rcases hx with hxv | hx
            · have : v = x := by simpa using hxv
              subst x
              exact ⟨v, hparent, .refl⟩
            · exact hchains x hx
      | some u =>
          rcases hparent with ⟨hu, hedge⟩
          have humem : u ∈ a.preorderRev := (hdisc.1 u).mp hu
          have hvchildren : v ∉ a.parentsRev.map Prod.fst := by
            intro h
            simp only [List.mem_map, Prod.exists] at h
            rcases h with ⟨child, p, hcp, hchild⟩
            subst child
            exact hv (hfacts v p hcp).2.1
          change (∀ child p, (child, p) ∈ (v, u) :: a.parentsRev →
              adj.Edge p child ∧ child ∈ a.visited.insert v ∧
                p ∈ a.visited.insert v ∧ Before child p (v :: a.preorderRev)) ∧
            (((v, u) :: a.parentsRev).map Prod.fst).Nodup ∧
            (∀ x, x ∈ a.visited.insert v → ∃ r ∈ roots,
              Relation.ReflTransGen (ParentRel ((v, u) :: a.parentsRev)) x r)
          refine ⟨?_, ?_, ?_⟩
          · intro child p hcp
            simp only [List.mem_cons, Prod.mk.injEq] at hcp
            rcases hcp with hnew | hcp
            · have hc : child = v := hnew.1
              have hp : p = u := hnew.2
              subst child
              subst p
              exact ⟨hedge, Std.HashSet.mem_insert_self,
                Std.HashSet.mem_insert.mpr (Or.inr hu), before_cons_of_mem humem⟩
            · rcases hfacts child p hcp with ⟨he, hc, hp, hb⟩
              exact ⟨he, Std.HashSet.mem_insert.mpr (Or.inr hc),
                Std.HashSet.mem_insert.mpr (Or.inr hp), before_cons hb⟩
          · simpa using List.Nodup.cons hvchildren hnodup
          · intro x hx
            rw [Std.HashSet.mem_insert] at hx
            rcases hx with hxv | hx
            · have : v = x := by simpa using hxv
              subst x
              rcases hchains u hu with ⟨r, hroot, hchain⟩
              have hchain' : Relation.ReflTransGen
                  (ParentRel ((v, u) :: a.parentsRev)) u r :=
                Relation.ReflTransGen.mono
                  (r := ParentRel a.parentsRev)
                  (p := ParentRel ((v, u) :: a.parentsRev))
                  (by intro c p h; exact List.mem_cons_of_mem _ h) u r hchain
              exact ⟨r, hroot, Relation.ReflTransGen.head
                (r := ParentRel ((v, u) :: a.parentsRev))
                (a := v) (b := u) (c := r) (by simp [ParentRel]) hchain'⟩
            · rcases hchains x hx with ⟨r, hroot, hchain⟩
              have hchain' : Relation.ReflTransGen
                  (ParentRel ((v, u) :: a.parentsRev)) x r :=
                Relation.ReflTransGen.mono
                  (r := ParentRel a.parentsRev)
                  (p := ParentRel ((v, u) :: a.parentsRev))
                  (by intro c p h; exact List.mem_cons_of_mem _ h) x r hchain
              exact ⟨r, hroot, hchain'⟩

private def FullForestInv {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) (s : Machine V) : Prop :=
  DiscoveryInv s ∧ WorkForestInv adj roots s ∧ ForestInv adj roots s

private theorem fullForestInv_initial {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) : FullForestInv adj roots (initial roots) :=
  ⟨discoveryInv_initial roots, workForestInv_initial adj roots,
    forestInv_initial adj roots⟩

private theorem fullForestInv_step {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) (a b : Machine V)
    (hab : Step adj roots a b) (ha : FullForestInv adj roots a) :
    FullForestInv adj roots b :=
  ⟨discoveryInv_step adj roots a b hab ha.1,
    workForestInv_step adj roots a b hab ha.2.1,
    forestInv_step adj roots a b hab ha.2.1 ha.1 ha.2.2⟩

private theorem fullForestInv_steps {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) (a b : Machine V)
    (hab : Steps adj roots a b) (ha : FullForestInv adj roots a) :
    FullForestInv adj roots b := by
  induction hab with
  | refl => exact ha
  | tail h step ih => exact fullForestInv_step adj roots _ _ step ih

private theorem final_forestInv {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) :
    ForestInv adj roots (loop adj roots (initial roots)) :=
  (fullForestInv_steps adj roots _ _ (loop_steps adj roots (initial roots)).1
    (fullForestInv_initial adj roots)).2.2

private theorem before_reverse {V : Type u} {x y : V} {xs : List V}
    (h : Before x y xs) : Before y x xs.reverse := by
  rcases h with ⟨a, b, c, rfl⟩
  refine ⟨c.reverse, b.reverse, a.reverse, ?_⟩
  simp [List.reverse_append]

/-- The actual roots of the DFS forest, in discovery order. -/
def Traversal.forestRoots {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (traversal : Traversal V) : List V :=
  let parented : Std.HashSet V := Std.HashSet.ofList (traversal.parents.map Prod.fst)
  traversal.preorder.filter fun vertex => vertex ∉ parented

/-- Actual forest roots contain no duplicates. -/
theorem forestRoots_nodup {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) :
    (dfs adj roots).forestRoots.Nodup := by
  exact (preorder_nodup adj roots).filter _

/-- An actual forest root has no recorded discovering parent. -/
theorem forestRoot_has_no_parent {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) (root parent : V)
    (hroot : root ∈ (dfs adj roots).forestRoots) :
    (root, parent) ∉ (dfs adj roots).parents := by
  have hroot' : root ∈ (dfs adj roots).preorder ∧
      ∀ candidate, (root, candidate) ∉ (dfs adj roots).parents := by
    simpa [Traversal.forestRoots] using hroot
  intro hparent
  exact hroot'.2 parent hparent

/-- Every recorded parent is an actual directed graph edge. -/
theorem parent_edge {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) (child parent : V)
    (h : (child, parent) ∈ (dfs adj roots).parents) : adj.Edge parent child := by
  have hrev : (child, parent) ∈ (loop adj roots (initial roots)).parentsRev := by
    simpa [dfs, finish] using h
  exact (final_forestInv adj roots).1 child parent hrev |>.1

/-- Parent entries have no duplicate child. -/
theorem parent_children_nodup {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) :
    ((dfs adj roots).parents.map Prod.fst).Nodup := by
  simpa [dfs, finish] using (final_forestInv adj roots).2.1

/-- Every discovered vertex is either an actual root or has a unique parent. -/
theorem mem_forestRoots_or_existsUnique_parent {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) (v : V)
    (hv : v ∈ (dfs adj roots).preorder) :
    v ∈ (dfs adj roots).forestRoots ∨
      ∃! parent, (v, parent) ∈ (dfs adj roots).parents := by
  by_cases hchild : v ∈ (dfs adj roots).parents.map Prod.fst
  · right
    simp only [List.mem_map, Prod.exists] at hchild
    rcases hchild with ⟨child, parent, hp, hchild⟩
    subst child
    refine ⟨parent, hp, ?_⟩
    intro other hother
    have hparentsNodup := (parent_children_nodup adj roots).of_map Prod.fst
    have hinj := (List.nodup_map_iff_inj_on hparentsNodup).mp
      (parent_children_nodup adj roots)
    have heq := hinj (v, other) hother (v, parent) hp rfl
    exact congrArg Prod.snd heq
  · left
    simp [Traversal.forestRoots, hv, hchild]

/-- A parent is discovered before its child in preorder. -/
theorem parent_before_child {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) (child parent : V)
    (h : (child, parent) ∈ (dfs adj roots).parents) :
    Before parent child (dfs adj roots).preorder := by
  have hrev : (child, parent) ∈ (loop adj roots (initial roots)).parentsRev := by
    simpa [dfs, finish] using h
  have hb := (final_forestInv adj roots).1 child parent hrev |>.2.2.2
  simpa [dfs, finish] using before_reverse hb

/-- A child finishes before its discovering parent. -/
theorem child_before_parent_postorder {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) (child parent : V)
    (h : (child, parent) ∈ (dfs adj roots).parents) :
    Before child parent (dfs adj roots).postorder := by
  have hrev : (child, parent) ∈ (loop adj roots (initial roots)).parentsRev := by
    simpa [dfs, finish] using h
  have hf := final_finishForestInv adj roots child parent hrev
  rw [(loop_steps adj roots (initial roots)).2] at hf
  have hf' : Before parent child (loop adj roots (initial roots)).postorderRev := by
    simpa [Before, exitVertices, List.append_assoc] using hf
  simpa [dfs, finish] using before_reverse hf'

/-- Vertices ordered from latest finish to earliest finish. -/
def decreasingFinish {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) : List V :=
  (dfs adj roots).postorder.reverse

/-- In decreasing finish order a parent precedes every child it discovered. -/
theorem parent_before_child_decreasingFinish {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) (child parent : V)
    (h : (child, parent) ∈ (dfs adj roots).parents) :
    Before parent child (decreasingFinish adj roots) := by
  exact before_reverse (child_before_parent_postorder adj roots child parent h)

/-- Decreasing finish order contains exactly the rooted reachable vertices. -/
theorem mem_decreasingFinish_iff_reachable {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) (v : V) :
    v ∈ decreasingFinish adj roots ↔
      ∃ root ∈ roots, adj.Reachable root v := by
  simpa [decreasingFinish] using mem_postorder_iff_reachable adj roots v

/-- Decreasing finish order has no duplicate vertices. -/
theorem decreasingFinish_nodup {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) :
    (decreasingFinish adj roots).Nodup := by
  simpa [decreasingFinish] using postorder_nodup adj roots

private theorem parent_chain_reaches_scheduled_root {V : Type u}
    [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) (v : V)
    (hv : v ∈ (dfs adj roots).preorder) :
    ∃ r ∈ roots, Relation.ReflTransGen (ParentRel (dfs adj roots).parents) v r := by
  have hpre : v ∈ (loop adj roots (initial roots)).preorderRev := by
    simpa [dfs, finish] using hv
  have hvisited := (final_discoveryInv adj roots).1 v |>.mpr hpre
  rcases (final_forestInv adj roots).2.2 v hvisited with ⟨r, hr, hchain⟩
  have hchain' : Relation.ReflTransGen (ParentRel (dfs adj roots).parents) v r :=
    Relation.ReflTransGen.mono
      (r := ParentRel (loop adj roots (initial roots)).parentsRev)
      (p := ParentRel (dfs adj roots).parents)
      (by intro c p h; simpa [dfs, finish, ParentRel] using h) v r hchain
  exact ⟨r, hr, hchain'⟩

private theorem idxOf_lt_of_before {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    {x y : V} {xs : List V} (hn : xs.Nodup) (h : Before x y xs) :
    xs.idxOf x < xs.idxOf y := by
  rcases h with ⟨a, b, c, rfl⟩
  rw [List.append_assoc] at hn
  rcases List.nodup_append.mp hn with ⟨ha, htail, hdisjA⟩
  rcases List.nodup_cons.mp htail with ⟨hxNotRest, hrest⟩
  rcases List.nodup_append.mp hrest with ⟨hb, hyc, hdisjB⟩
  rcases List.nodup_cons.mp hyc with ⟨hyNotC, hc⟩
  have hxNotA : x ∉ a := by
    intro hx
    exact hdisjA x hx x (by simp) rfl
  have hyNotA : y ∉ a := by
    intro hy
    exact hdisjA y hy y (by simp) rfl
  have hyNotB : y ∉ b := by
    intro hy
    exact hdisjB y hy y (by simp) rfl
  have hxy : x ≠ y := by
    intro hxy
    subst y
    exact hxNotRest (by simp)
  simp [List.idxOf_append, hxNotA, hyNotA, hyNotB, hxy]

private theorem parent_chain_reaches_forestRoot_aux {V : Type u}
    [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) (n : Nat) :
    ∀ v, v ∈ (dfs adj roots).preorder →
      (dfs adj roots).preorder.idxOf v ≤ n →
      ∃ r ∈ (dfs adj roots).forestRoots,
        Relation.ReflTransGen (ParentRel (dfs adj roots).parents) v r := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro v hv hidx
      rcases mem_forestRoots_or_existsUnique_parent adj roots v hv with hroot | hparent
      · exact ⟨v, hroot, .refl⟩
      · rcases hparent with ⟨parent, hvp, _⟩
        have hbefore := parent_before_child adj roots v parent hvp
        have hparentMem : parent ∈ (dfs adj roots).preorder := by
          rcases hbefore with ⟨a, b, c, heq⟩
          rw [heq]
          simp
        have hlt := idxOf_lt_of_before (preorder_nodup adj roots) hbefore
        rcases ih _ (Nat.lt_of_lt_of_le hlt hidx) parent hparentMem
            (Nat.le_refl _) with ⟨r, hr, hchain⟩
        exact ⟨r, hr, Relation.ReflTransGen.head hvp hchain⟩

/-- Following recorded parents from a discovered vertex reaches an actual
parentless root of the DFS forest. -/
theorem parent_chain_reaches_root {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) (v : V)
    (hv : v ∈ (dfs adj roots).preorder) :
    ∃ r ∈ (dfs adj roots).forestRoots,
      Relation.ReflTransGen (ParentRel (dfs adj roots).parents) v r := by
  exact parent_chain_reaches_forestRoot_aux adj roots
    ((dfs adj roots).preorder.idxOf v) v hv (Nat.le_refl _)

private theorem transGen_rank_decreases {V : Type u} (rel : V → V → Prop) (rank : V → Nat)
    (hstep : ∀ a b, rel a b → rank b < rank a) (a b : V)
    (h : Relation.TransGen rel a b) : rank b < rank a := by
  induction h with
  | single h => exact hstep _ _ h
  | tail h₁ h₂ ih => exact Nat.lt_trans (hstep _ _ h₂) ih

/-- The discovering-parent relation has no directed cycle. -/
theorem parent_relation_acyclic {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) (v : V) :
    ¬ Relation.TransGen (ParentRel (dfs adj roots).parents) v v := by
  intro hcycle
  have hdecrease := transGen_rank_decreases
    (ParentRel (dfs adj roots).parents)
    (fun x => (dfs adj roots).preorder.idxOf x)
    (by
      intro child parent hparent
      exact idxOf_lt_of_before (preorder_nodup adj roots)
        (parent_before_child adj roots child parent hparent)) v v hcycle
  omega


private theorem reflTransGen_eq_of_no_head {V : Type u} {relation : V → V → Prop}
    {source target : V} (steps : Relation.ReflTransGen relation source target)
    (noStep : ∀ next, ¬ relation source next) : source = target := by
  induction steps with
  | refl => rfl
  | tail steps step induction =>
      cases induction
      exact (noStep _ step).elim

/-- Every actual forest root came from the supplied root schedule. -/
theorem forestRoot_mem_roots {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) (root : V)
    (hroot : root ∈ (dfs adj roots).forestRoots) : root ∈ roots := by
  have hroot' : root ∈ (dfs adj roots).preorder ∧
      root ∉ (dfs adj roots).parents.map Prod.fst := by
    simpa [Traversal.forestRoots] using hroot
  have hpre : root ∈ (dfs adj roots).preorder := hroot'.1
  rcases parent_chain_reaches_scheduled_root adj roots root hpre with
    ⟨scheduled, hs, chain⟩
  have noStep : ∀ parent,
      ¬ ParentRel (dfs adj roots).parents root parent := by
    intro parent hparent
    exact forestRoot_has_no_parent adj roots root parent hroot hparent
  have : root = scheduled := reflTransGen_eq_of_no_head chain noStep
  rwa [this]

/-- Traverse every vertex, using the graph's certified vertex order as the root schedule. -/
def dfsAll {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) : Traversal V :=
  dfs adj adj.vertices

/-- Every vertex occurs in the preorder of a whole-graph traversal. -/
theorem mem_dfsAll_preorder {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (vertex : V) :
    vertex ∈ (dfsAll adj).preorder := by
  apply preorder_complete adj adj.vertices vertex
  exact ⟨vertex, adj.vertices_complete vertex, Relation.ReflTransGen.refl⟩

/-- Every vertex occurs in the postorder of a whole-graph traversal. -/
theorem mem_dfsAll_postorder {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (vertex : V) :
    vertex ∈ (dfsAll adj).postorder := by
  change vertex ∈ (dfs adj adj.vertices).postorder
  rw [mem_postorder_iff_reachable]
  exact ⟨vertex, adj.vertices_complete vertex, Relation.ReflTransGen.refl⟩

/-- Vertices of a whole-graph traversal, ordered from latest finish to earliest finish. -/
def decreasingFinishAll {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) : List V :=
  decreasingFinish adj adj.vertices

/-- Every vertex occurs in whole-graph decreasing finish order. -/
theorem mem_decreasingFinishAll {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (vertex : V) :
    vertex ∈ decreasingFinishAll adj := by
  change vertex ∈ decreasingFinish adj adj.vertices
  rw [mem_decreasingFinish_iff_reachable]
  exact ⟨vertex, adj.vertices_complete vertex, Relation.ReflTransGen.refl⟩

/-- Whole-graph decreasing finish order contains no duplicate vertices. -/
theorem decreasingFinishAll_nodup {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) : (decreasingFinishAll adj).Nodup := by
  exact decreasingFinish_nodup adj adj.vertices

end Cslib.Algorithms.Lean.DepthFirstSearch
