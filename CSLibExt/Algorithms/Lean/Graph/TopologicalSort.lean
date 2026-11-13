/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Init.Data.Queue
public import CSLibExt.Algorithms.Lean.Graph.DirectedAdjacency
public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.Nodup

import CSLibExt.Algorithms.Lean.DataStructures.Queue.Semantics
import Mathlib.Data.Bool.Basic
import all Init.Data.Queue
import Mathlib.Data.List.Count
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Perm.Basic
import Mathlib.Logic.Function.Iterate
import Std.Data.HashMap.Basic
import Std.Data.HashMap.Lemmas
import Std.Data.HashSet.Basic
import Std.Data.HashSet.Lemmas

/-!
# Deterministic FIFO topological sorting

This file implements Kahn topological sorting for finite executable directed graphs. A successful
run returns a complete duplicate-free order whose edges point forward. A failed run returns the
exact remaining vertices and yields a contained simple directed cycle.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Cslib.Algorithms.Lean

namespace TopologicalSort

/-- **Indegree within a vertex list.** For a finite directed graph $G$, a list $R$ of vertices and
a vertex $v$, the indegree of $v$ within $R$ is the number of entries $u$ of $R$, counted with
multiplicity, such that $G$ has an edge from $u$ to $v$. -/
public def indegreeWithin {α : Type u} [DecidableEq α]
    (g : DirectedAdjacency α) (remaining : List α) (v : α) : Nat :=
  remaining.countP (fun u => g.hasEdge u v)

/-- **Indegree.** The indegree of a vertex $v$ in a finite directed graph $G$ is the number of
vertices $u$ such that $G$ has an edge from $u$ to $v$; repeated entries in adjacency lists
count once. -/
public def indegree {α : Type u} [DecidableEq α]
    (g : DirectedAdjacency α) (v : α) : Nat :=
  indegreeWithin g g.vertices v

private abbrev State (α : Type u) :=
  List α × (α → Nat) × Std.Queue α × List α

private abbrev State.remaining {α : Type u} (s : State α) : List α := s.1

private abbrev State.degrees {α : Type u} (s : State α) : α → Nat := s.2.1

private abbrev State.queue {α : Type u} (s : State α) : Std.Queue α := s.2.2.1

private abbrev State.output {α : Type u} (s : State α) : List α := s.2.2.2

@[simp] private theorem State.remaining_mk {α : Type u} (remaining : List α)
    (degrees : α → Nat) (queue : Std.Queue α) (output : List α) :
    State.remaining (remaining, degrees, queue, output) = remaining := rfl

@[simp] private theorem State.degrees_mk {α : Type u} (remaining : List α)
    (degrees : α → Nat) (queue : Std.Queue α) (output : List α) :
    State.degrees (remaining, degrees, queue, output) = degrees := rfl

@[simp] private theorem State.queue_mk {α : Type u} (remaining : List α)
    (degrees : α → Nat) (queue : Std.Queue α) (output : List α) :
    State.queue (remaining, degrees, queue, output) = queue := rfl

@[simp] private theorem State.output_mk {α : Type u} (remaining : List α)
    (degrees : α → Nat) (queue : Std.Queue α) (output : List α) :
    State.output (remaining, degrees, queue, output) = output := rfl

private abbrev initialState {α : Type u} [DecidableEq α] (g : DirectedAdjacency α) : State α :=
  (g.vertices,
    indegreeWithin g g.vertices,
    Std.Queue.mk [] (g.vertices.filter fun v => indegreeWithin g g.vertices v == 0),
    [])

private def dedupNeighbors {α : Type u} [DecidableEq α]
    (seen : α → Bool) : List α → List α
  | [] => []
  | vertex :: neighbors =>
      if seen vertex then dedupNeighbors seen neighbors
      else vertex :: dedupNeighbors (Function.update seen vertex true) neighbors

private theorem mem_dedupNeighbors {α : Type u} [DecidableEq α]
    (seen : α → Bool) (neighbors : List α) (vertex : α) :
    vertex ∈ dedupNeighbors seen neighbors ↔ vertex ∈ neighbors ∧ seen vertex = false := by
  induction neighbors generalizing seen with
  | nil => simp [dedupNeighbors]
  | cons target neighbors induction =>
      by_cases hseen : seen target = true
      · by_cases hvt : vertex = target
        · subst target
          simp [dedupNeighbors, hseen, induction]
        · simp [dedupNeighbors, hseen, induction, hvt]
      · have hseenfalse : seen target = false := Bool.eq_false_of_not_eq_true hseen
        by_cases hvt : vertex = target
        · subst target
          simp [dedupNeighbors, hseenfalse]
        · simp [dedupNeighbors, hseenfalse, induction, hvt, Function.update]

private theorem dedupNeighbors_nodup {α : Type u} [DecidableEq α]
    (seen : α → Bool) (neighbors : List α) : (dedupNeighbors seen neighbors).Nodup := by
  induction neighbors generalizing seen with
  | nil => simp [dedupNeighbors]
  | cons vertex neighbors induction =>
      by_cases hseen : seen vertex = true
      · simp [dedupNeighbors, hseen, induction]
      · have hseenfalse : seen vertex = false := Bool.eq_false_of_not_eq_true hseen
        rw [dedupNeighbors]
        simp only [hseenfalse, Bool.false_eq_true, ↓reduceIte, List.nodup_cons]
        constructor
        · rw [mem_dedupNeighbors]
          simp [Function.update]
        · exact induction _

private abbrev neighborScan {α : Type u} [DecidableEq α]
    (g : DirectedAdjacency α) (source : α) : List α :=
  dedupNeighbors (fun _ => false) (g.adjacency source)

private theorem neighborScan_nodup {α : Type u} [DecidableEq α]
    (g : DirectedAdjacency α) (source : α) : (neighborScan g source).Nodup := by
  exact dedupNeighbors_nodup _ _

private theorem mem_neighborScan {α : Type u} [DecidableEq α]
    (g : DirectedAdjacency α) (source target : α) :
    target ∈ neighborScan g source ↔ g.hasEdge source target = true := by
  simp [neighborScan, mem_dedupNeighbors, DirectedAdjacency.hasEdge]

private def updateNeighbors {α : Type u} [DecidableEq α] (g : DirectedAdjacency α) (removed : α)
    (remaining : List α) (scan : List α) (degrees : α → Nat) (queue : Std.Queue α) :
    (α → Nat) × Std.Queue α :=
  match scan with
  | [] => (degrees, queue)
  | v :: scan =>
      if v ∈ remaining && g.hasEdge removed v then
        let old := degrees v
        let degrees := Function.update degrees v (old - 1)
        let queue := if old == 1 then queue.enqueue v else queue
        updateNeighbors g removed remaining scan degrees queue
      else
        updateNeighbors g removed remaining scan degrees queue

private def newlyReady {α : Type u} [DecidableEq α] (g : DirectedAdjacency α) (removed : α)
    (remaining scan : List α) (degrees : α → Nat) : List α :=
  scan.filter fun v =>
    (v ∈ remaining && g.hasEdge removed v) && degrees v == 1

private theorem filter_update_of_not_mem {α : Type u} {β : Type v} [DecidableEq α]
    (scan : List α) (v : α) (hnot : v ∉ scan) (f : α → β) (b : β)
    (p : α → β → Bool) :
    scan.filter (fun x => p x (Function.update f v b x)) =
      scan.filter (fun x => p x (f x)) := by
  apply List.filter_congr
  intro x hx
  have hxv : x ≠ v := by
    intro h
    apply hnot
    simpa [h] using hx
  simp [Function.update, hxv]

private theorem updateNeighbors_contents {α : Type u} [DecidableEq α]
    (g : DirectedAdjacency α) (removed : α) (remaining scan : List α)
    (degrees : α → Nat) (queue : Std.Queue α) (hscan : scan.Nodup) :
    Queue.contents (updateNeighbors g removed remaining scan degrees queue).2 =
      Queue.contents queue ++ newlyReady g removed remaining scan degrees := by
  induction scan generalizing degrees queue with
  | nil => simp [updateNeighbors, newlyReady]
  | cons v scan ih =>
    have hvnot : v ∉ scan := (List.nodup_cons.mp hscan).1
    have htail : scan.Nodup := (List.nodup_cons.mp hscan).2
    by_cases hvr : v ∈ remaining
    · by_cases hve : g.hasEdge removed v = true
      · by_cases hold : degrees v = 1
        · rw [show updateNeighbors g removed remaining (v :: scan) degrees queue =
              updateNeighbors g removed remaining scan
                (Function.update degrees v (degrees v - 1)) (queue.enqueue v) by
              simp [updateNeighbors, hvr, hve, hold]]
          rw [ih _ _ htail]
          simp only [newlyReady]
          rw [filter_update_of_not_mem scan v hvnot degrees (degrees v - 1)
            (fun x n => (x ∈ remaining && g.hasEdge removed x) && n == 1)]
          simp [hvr, hve, hold, Queue.contents_enqueue, List.append_assoc]
        · have holdb : (degrees v == 1) = false := by simpa using hold
          rw [show updateNeighbors g removed remaining (v :: scan) degrees queue =
              updateNeighbors g removed remaining scan
                (Function.update degrees v (degrees v - 1)) queue by
              simp [updateNeighbors, hvr, hve, holdb]]
          rw [ih _ _ htail]
          simp only [newlyReady]
          rw [filter_update_of_not_mem scan v hvnot degrees (degrees v - 1)
            (fun x n => (x ∈ remaining && g.hasEdge removed x) && n == 1)]
          simp [hvr, hve, holdb]
      · have hvefalse : g.hasEdge removed v = false := Bool.eq_false_of_not_eq_true hve
        simp [updateNeighbors, newlyReady, hvr, hvefalse, ih _ _ htail]
    · simp [updateNeighbors, newlyReady, hvr, ih _ _ htail]

private theorem updateNeighbors_degree_apply {α : Type u} [DecidableEq α]
    (g : DirectedAdjacency α) (removed : α) (remaining scan : List α)
    (degrees : α → Nat) (queue : Std.Queue α) (x : α)
    (hscan : scan.Nodup) :
    (updateNeighbors g removed remaining scan degrees queue).1 x =
      if x ∈ scan ∧ x ∈ remaining ∧ g.hasEdge removed x = true
      then degrees x - 1 else degrees x := by
  induction scan generalizing degrees queue with
  | nil => simp [updateNeighbors]
  | cons v scan ih =>
    have hvnot : v ∉ scan := (List.nodup_cons.mp hscan).1
    have htail : scan.Nodup := (List.nodup_cons.mp hscan).2
    by_cases hvr : v ∈ remaining
    · by_cases hve : g.hasEdge removed v = true
      · by_cases hx : x = v
        · subst x
          simp [updateNeighbors, hvr, hve, ih _ _ htail, hvnot]
        · simp [updateNeighbors, hvr, hve, ih _ _ htail, hx, Function.update]
      · have hvefalse : g.hasEdge removed v = false := Bool.eq_false_of_not_eq_true hve
        by_cases hx : x = v
        · subst x
          simp [updateNeighbors, hvr, hvefalse, ih _ _ htail, hvnot]
        · simp [updateNeighbors, hvr, hvefalse, ih _ _ htail, hx]
    · by_cases hx : x = v
      · subst x
        simp [updateNeighbors, hvr, ih _ _ htail, hvnot]
      · simp [updateNeighbors, hvr, ih _ _ htail, hx]

private theorem updateNeighbors_queue_invariant {α : Type u} [DecidableEq α]
    (g : DirectedAdjacency α) (removed : α) (remaining scan : List α)
    (degrees : α → Nat) (queue : Std.Queue α)
    (hscan : scan.Nodup) (hqnodup : (Queue.contents queue).Nodup)
    (hqremaining : ∀ x ∈ Queue.contents queue, x ∈ remaining)
    (hqzero : ∀ x ∈ Queue.contents queue, degrees x = 0) :
    let result := updateNeighbors g removed remaining scan degrees queue
    (Queue.contents result.2).Nodup ∧
      ∀ x ∈ Queue.contents result.2, x ∈ remaining ∧ result.1 x = 0 := by
  let ready := newlyReady g removed remaining scan degrees
  have hready_nodup : ready.Nodup := hscan.filter _
  have hready_properties : ∀ x ∈ ready,
      x ∈ scan ∧ x ∈ remaining ∧
        g.hasEdge removed x = true ∧ degrees x = 1 := by
    intro x hx
    simp only [ready, newlyReady, List.mem_filter] at hx
    rcases hx with ⟨hxscan, hxbool⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hxbool
    exact ⟨hxscan, hxbool.1.1, hxbool.1.2, hxbool.2⟩
  have hcross : ∀ a ∈ Queue.contents queue, ∀ b ∈ ready, a ≠ b := by
    intro a ha b hb hab
    subst b
    have hzero := hqzero a ha
    have hone := (hready_properties a hb).2.2.2
    omega
  have hview :
      Queue.contents (updateNeighbors g removed remaining scan degrees queue).2 =
        Queue.contents queue ++ ready := by
    simpa [ready] using
      updateNeighbors_contents g removed remaining scan degrees queue hscan
  dsimp only
  constructor
  · rw [hview, List.nodup_append]
    exact ⟨hqnodup, hready_nodup, hcross⟩
  · intro x hx
    rw [hview] at hx
    rcases List.mem_append.mp hx with hxold | hxnew
    · constructor
      · exact hqremaining x hxold
      · rw [updateNeighbors_degree_apply g removed remaining scan degrees queue x hscan]
        simp [hqzero x hxold]
    · have hp := hready_properties x hxnew
      constructor
      · exact hp.2.1
      · rw [updateNeighbors_degree_apply g removed remaining scan degrees queue x hscan]
        simp [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2]

private theorem updateNeighbors_preserves_indegree {α : Type u} [DecidableEq α]
    (g : DirectedAdjacency α) (oldRemaining : List α) (removed : α)
    (hremoved : removed ∈ oldRemaining) (degrees : α → Nat)
    (hdegrees : ∀ x ∈ oldRemaining, degrees x = indegreeWithin g oldRemaining x)
    (queue : Std.Queue α) :
    ∀ x ∈ oldRemaining.erase removed,
      (updateNeighbors g removed (oldRemaining.erase removed) (neighborScan g removed)
        degrees queue).1 x = indegreeWithin g (oldRemaining.erase removed) x := by
  intro x hx
  have hxold : x ∈ oldRemaining := List.mem_of_mem_erase hx
  rw [updateNeighbors_degree_apply g removed (oldRemaining.erase removed)
    (neighborScan g removed) degrees queue x (neighborScan_nodup g removed)]
  rw [hdegrees x hxold]
  by_cases he : g.hasEdge removed x = true
  · simp [(mem_neighborScan g removed x).2 he, hx, he, indegreeWithin,
      List.countP_erase, hremoved]
  · have hef : g.hasEdge removed x = false := Bool.eq_false_of_not_eq_true he
    simp [hef, indegreeWithin, List.countP_erase, hremoved]

private def step {α : Type u} [DecidableEq α] (g : DirectedAdjacency α) (s : State α) :
    Option (State α) :=
  match s.queue.dequeue? with
  | none => none
  | some (u, queue) =>
      let remaining := s.remaining.erase u
      let (degrees, queue) :=
        updateNeighbors g u remaining (neighborScan g u) s.degrees queue
      some (remaining, degrees, queue, s.output ++ [u])

private structure StateInvariant {α : Type u} [DecidableEq α]
    (g : DirectedAdjacency α) (s : State α) : Prop where
  remaining_nodup : s.remaining.Nodup
  output_nodup : s.output.Nodup
  coverage : ∀ v, v ∈ g.vertices ↔ v ∈ s.output ∨ v ∈ s.remaining
  disjoint : ∀ v ∈ s.output, v ∉ s.remaining
  length_eq : s.remaining.length + s.output.length = g.vertices.length
  degrees : ∀ v ∈ s.remaining, s.degrees v = indegreeWithin g s.remaining v
  queue_nodup : (Queue.contents s.queue).Nodup
  queue_remaining : ∀ v ∈ Queue.contents s.queue, v ∈ s.remaining
  queue_zero : ∀ v ∈ Queue.contents s.queue, s.degrees v = 0
  zero_queued : ∀ v ∈ s.remaining, s.degrees v = 0 → v ∈ Queue.contents s.queue
  cross_edges : ∀ r ∈ s.remaining, ∀ p ∈ s.output, g.hasEdge r p = false
  output_no_self : ∀ p ∈ s.output, g.hasEdge p p = false
  output_ordered : s.output.Pairwise (fun earlier later => g.hasEdge later earlier = false)

private theorem initialState_invariant {α : Type u} [DecidableEq α] (g : DirectedAdjacency α) :
    StateInvariant g (initialState g) := by
  constructor
  · exact g.vertices_nodup
  · simp [initialState]
  · intro v
    simp [initialState]
  · simp [initialState]
  · simp [initialState]
  · intro v hv
    rfl
  · simpa [initialState, Queue.contents] using
      g.vertices_nodup.filter (fun v => indegreeWithin g g.vertices v == 0)
  · intro v hv
    have hv' : v ∈ g.vertices.filter (fun x => indegreeWithin g g.vertices x == 0) := by
      simpa [Queue.contents, initialState] using hv
    exact List.mem_of_mem_filter hv'
  · intro v hv
    simp only [Queue.contents, List.reverse_nil,
      List.append_nil, List.mem_filter] at hv
    exact of_decide_eq_true hv.2
  · intro v hv hz
    change v ∈ g.vertices at hv
    change indegreeWithin g g.vertices v = 0 at hz
    have : v ∈ g.vertices.filter (fun x => indegreeWithin g g.vertices x == 0) := by
      simp [hv, hz]
    simpa [Queue.contents, initialState] using this
  · simp [initialState]
  · simp [initialState]
  · simp [initialState]

private theorem outgoing_neighbor_degree_positive {α : Type u} [DecidableEq α]
    (g : DirectedAdjacency α) (remaining : List α) (degrees : α → Nat) (removed v : α)
    (hremoved : removed ∈ remaining) (hv : v ∈ remaining)
    (hdegrees : ∀ x ∈ remaining, degrees x = indegreeWithin g remaining x)
    (hedge : g.hasEdge removed v = true) : 0 < degrees v := by
  rw [hdegrees v hv, indegreeWithin, List.countP_eq_length_filter, List.length_pos_iff]
  apply List.ne_nil_of_mem (a := removed)
  simp [hremoved, hedge]

private theorem indegree_zero_edge_false {α : Type u} [DecidableEq α]
    (g : DirectedAdjacency α) (remaining : List α) (v u : α)
    (hu : u ∈ remaining) (hz : indegreeWithin g remaining v = 0) :
    g.hasEdge u v = false := by
  by_contra h
  have ht : g.hasEdge u v = true := Bool.eq_true_of_not_eq_false h
  have : 0 < indegreeWithin g remaining v := by
    rw [indegreeWithin, List.countP_eq_length_filter, List.length_pos_iff]
    apply List.ne_nil_of_mem (a := u)
    simp [hu, ht]
  omega

private theorem step_invariant {α : Type u} [DecidableEq α]
    (g : DirectedAdjacency α) (s s' : State α) (hinv : StateInvariant g s)
    (hstep : step g s = some s') : StateInvariant g s' := by
  cases hq : s.queue.dequeue? with
  | none => simp [step, hq] at hstep
  | some pair =>
      rcases pair with ⟨u, queue⟩
      cases hupd : updateNeighbors g u (s.remaining.erase u) (neighborScan g u)
          s.degrees queue with
      | mk degrees queue' =>
          have hs' : s' =
              (s.remaining.erase u, degrees, queue', s.output ++ [u]) := by
            simpa [step, hq, hupd] using hstep.symm
          subst s'
          have hview := Queue.contents_eq_cons_of_dequeue?_eq_some hq
          have huqueue : u ∈ Queue.contents s.queue := by
            rw [hview]
            simp
          have hurem : u ∈ s.remaining := hinv.queue_remaining u huqueue
          have huzero : s.degrees u = 0 := hinv.queue_zero u huqueue
          have hqtail_nodup : (Queue.contents queue).Nodup := by
            have h := hinv.queue_nodup
            rw [hview] at h
            exact h.tail
          have hqtail_remaining : ∀ x ∈ Queue.contents queue, x ∈ s.remaining.erase u := by
            intro x hx
            have hxold : x ∈ s.remaining := hinv.queue_remaining x (by
              rw [hview]
              simp [hx])
            have hxu : x ≠ u := by
              intro heq
              subst x
              have h := hinv.queue_nodup
              rw [hview] at h
              exact (List.nodup_cons.mp h).1 hx
            exact (hinv.remaining_nodup.mem_erase_iff).mpr ⟨hxu, hxold⟩
          have hqtail_zero : ∀ x ∈ Queue.contents queue, s.degrees x = 0 := by
            intro x hx
            exact hinv.queue_zero x (by rw [hview]; simp [hx])
          have hqupd := updateNeighbors_queue_invariant g u (s.remaining.erase u)
            (neighborScan g u) s.degrees queue (neighborScan_nodup g u) hqtail_nodup
            hqtail_remaining hqtail_zero
          rw [hupd] at hqupd
          constructor
          · exact hinv.remaining_nodup.erase u
          · rw [List.nodup_append]
            refine ⟨hinv.output_nodup, by simp, ?_⟩
            intro p hp x hx
            simp only [List.mem_singleton] at hx
            subst x
            exact fun heq => hinv.disjoint u (heq ▸ hp) hurem
          · intro v
            rw [hinv.coverage v]
            change (v ∈ s.output ∨ v ∈ s.remaining) ↔
              v ∈ s.output ++ [u] ∨ v ∈ s.remaining.erase u
            simp only [List.mem_append, List.mem_singleton]
            rw [hinv.remaining_nodup.mem_erase_iff]
            constructor
            · rintro (hv | hv)
              · exact Or.inl (Or.inl hv)
              · by_cases h : v = u
                · exact Or.inl (Or.inr h)
                · exact Or.inr ⟨h, hv⟩
            · rintro (hv | hv)
              · rcases hv with hv | rfl
                · exact Or.inl hv
                · exact Or.inr hurem
              · exact Or.inr hv.2
          · intro v hvout hverase
            change v ∈ s.output ++ [u] at hvout
            change v ∈ s.remaining.erase u at hverase
            simp only [List.mem_append, List.mem_singleton] at hvout
            rcases hvout with hvout | rfl
            · exact hinv.disjoint v hvout (List.mem_of_mem_erase hverase)
            · exact ((hinv.remaining_nodup.mem_erase_iff.mp hverase).1 rfl).elim
          · rw [List.length_erase_of_mem hurem, List.length_append]
            simp only [List.length_singleton]
            have hpos := List.length_pos_of_mem hurem
            have hlen := hinv.length_eq
            omega
          · intro v hv
            have h := updateNeighbors_preserves_indegree g s.remaining u hurem
              s.degrees hinv.degrees queue v hv
            simpa [hupd] using h
          · exact hqupd.1
          · exact fun v hv => (hqupd.2 v hv).1
          · exact fun v hv => (hqupd.2 v hv).2
          · intro v hvrem hvzero
            change v ∈ Queue.contents queue'
            change degrees v = 0 at hvzero
            have hviewupd := updateNeighbors_contents g u (s.remaining.erase u)
              (neighborScan g u) s.degrees queue (neighborScan_nodup g u)
            rw [hupd] at hviewupd
            rw [hviewupd]
            have hdegreeupd := updateNeighbors_degree_apply g u (s.remaining.erase u)
              (neighborScan g u) s.degrees queue v (neighborScan_nodup g u)
            rw [hupd] at hdegreeupd
            change degrees v = _ at hdegreeupd
            rw [hdegreeupd] at hvzero
            by_cases holdzero : s.degrees v = 0
            · apply List.mem_append_left
              have hvoldq := hinv.zero_queued v (List.mem_of_mem_erase hvrem) holdzero
              rw [hview] at hvoldq
              simp only [List.mem_cons] at hvoldq
              rcases hvoldq with h | h
              · subst v
                exact (((hinv.remaining_nodup.mem_erase_iff).mp hvrem).1 rfl).elim
              · exact h
            · apply List.mem_append_right
              simp only [newlyReady, List.mem_filter]
              have hvedge : g.hasEdge u v = true := by
                by_contra hne
                have hef : g.hasEdge u v = false := Bool.eq_false_of_not_eq_true hne
                simp [hef, holdzero] at hvzero
              have hvscan : v ∈ neighborScan g u := (mem_neighborScan g u v).2 hvedge
              have hdegree : s.degrees v = 1 := by
                simp [hvscan, hvrem, hvedge] at hvzero
                omega
              exact ⟨hvscan, by simp [hvrem, hvedge, hdegree]⟩
          · intro r hr p hp
            change r ∈ s.remaining.erase u at hr
            change p ∈ s.output ++ [u] at hp
            simp only [List.mem_append, List.mem_singleton] at hp
            rcases hp with hp | rfl
            · exact hinv.cross_edges r (List.mem_of_mem_erase hr) p hp
            · exact indegree_zero_edge_false g s.remaining p r
                (List.mem_of_mem_erase hr) (hinv.degrees p hurem ▸ huzero)
          · intro p hp
            change p ∈ s.output ++ [u] at hp
            simp only [List.mem_append, List.mem_singleton] at hp
            rcases hp with hp | rfl
            · exact hinv.output_no_self p hp
            · exact indegree_zero_edge_false g s.remaining p p hurem
                (hinv.degrees p hurem ▸ huzero)
          · rw [List.pairwise_append]
            refine ⟨hinv.output_ordered, by simp, ?_⟩
            intro p hp x hx
            simp only [List.mem_singleton] at hx
            subst x
            exact hinv.cross_edges u hurem p hp

/-- **Outcome of Kahn's topological sort.** The result of Kahn's topological sorting algorithm on a
graph with vertices of type $\alpha$ is either a success, carrying a list of vertices, or a failure,
carrying the list of vertices processed before the queue emptied and the list of vertices that
remain. -/
public inductive Result (α : Type u) where
  /-- Every vertex was processed in this order. -/
  | success (order : List α)
  /-- The queue emptied after `processed`, leaving exactly `remaining`. -/
  | failure (processed remaining : List α)
  deriving DecidableEq, Repr

private def loop {α : Type u} [DecidableEq α] (g : DirectedAdjacency α) : Nat → State α → Result α
  | 0, s =>
      if s.remaining.isEmpty then .success s.output
      else .failure s.output s.remaining
  | fuel + 1, s =>
      if s.remaining.isEmpty then .success s.output
      else
        match step g s with
        | none => .failure s.output s.remaining
        | some s' => loop g fuel s'

private inductive TerminalSpec {α : Type u} [DecidableEq α]
    (g : DirectedAdjacency α) : Result α → Prop
  | success (s : State α) (hinv : StateInvariant g s) (hempty : s.remaining = []) :
      TerminalSpec g (.success s.output)
  | failure (s : State α) (hinv : StateInvariant g s) (hne : s.remaining ≠ [])
      (hq : Queue.contents s.queue = []) : TerminalSpec g (.failure s.output s.remaining)

private theorem step_none_queue_contents_nil {α : Type u} [DecidableEq α]
    (g : DirectedAdjacency α) (s : State α) (h : step g s = none) :
    Queue.contents s.queue = [] := by
  cases hq : s.queue.dequeue? with
  | none => exact (Queue.dequeue?_eq_none_iff s.queue).mp hq
  | some pair => simp [step, hq] at h

private theorem step_remaining_length {α : Type u} [DecidableEq α]
    (g : DirectedAdjacency α) (s s' : State α) (hinv : StateInvariant g s)
    (h : step g s = some s') : s'.remaining.length + 1 = s.remaining.length := by
  cases hq : s.queue.dequeue? with
  | none => simp [step, hq] at h
  | some pair =>
      rcases pair with ⟨u, queue⟩
      have hview := Queue.contents_eq_cons_of_dequeue?_eq_some hq
      have hurem : u ∈ s.remaining := hinv.queue_remaining u (by rw [hview]; simp)
      cases hupd : updateNeighbors g u (s.remaining.erase u) (neighborScan g u)
          s.degrees queue with
      | mk degrees queue' =>
          have hs' : s' =
              (s.remaining.erase u, degrees, queue', s.output ++ [u]) := by
            simpa [step, hq, hupd] using h.symm
          subst s'
          rw [List.length_erase_of_mem hurem]
          have hpos := List.length_pos_of_mem hurem
          omega

private theorem loop_spec {α : Type u} [DecidableEq α]
    (g : DirectedAdjacency α) (fuel : Nat) (s : State α) (hinv : StateInvariant g s)
    (hfuel : fuel = s.remaining.length) : TerminalSpec g (loop g fuel s) := by
  induction fuel generalizing s with
  | zero =>
      have hlen : s.remaining.length = 0 := by omega
      have hempty : s.remaining = [] := List.length_eq_zero_iff.mp hlen
      simpa [loop, hempty] using TerminalSpec.success s hinv hempty
  | succ fuel ih =>
      by_cases hempty : s.remaining = []
      · simpa [loop, hempty] using TerminalSpec.success s hinv hempty
      · have hisempty : s.remaining.isEmpty = false := by
          simpa [List.isEmpty_iff] using hempty
        cases hstep : step g s with
        | none =>
            simpa [loop, hisempty, hstep] using TerminalSpec.failure s hinv hempty
              (step_none_queue_contents_nil g s hstep)
        | some s' =>
            rw [loop, hisempty, hstep]
            apply ih s' (step_invariant g s s' hinv hstep)
            have hlen := step_remaining_length g s s' hinv hstep
            omega

private def dedupNeighborsImplAux {α : Type u} [DecidableEq α] [Hashable α]
    (seen : Std.HashSet α) : List α → List α
  | [] => []
  | target :: neighbors =>
      if seen.contains target then dedupNeighborsImplAux seen neighbors
      else target :: dedupNeighborsImplAux (seen.insert target) neighbors

private abbrev dedupNeighborsImpl {α : Type u} [DecidableEq α] [Hashable α]
    (neighbors : List α) : List α :=
  dedupNeighborsImplAux ∅ neighbors

private def addEdgesImpl {α : Type u} [DecidableEq α] [Hashable α]
    (degrees : Std.HashMap α Nat) (neighbors : List α) : Std.HashMap α Nat :=
  neighbors.foldl (fun result target =>
    result.insert target (result.getD target 0 + 1)) degrees

private def initialDegreesImpl {α : Type u} [DecidableEq α] [Hashable α]
    (g : DirectedAdjacency α) : Std.HashMap α Nat :=
  g.vertices.foldl (fun degrees source =>
    addEdgesImpl degrees (dedupNeighborsImpl (g.adjacency source))) ∅

private def updateNeighborsImpl {α : Type u} [DecidableEq α] [Hashable α]
    (active : Std.HashSet α) (neighbors : List α)
    (degrees : Std.HashMap α Nat) (queue : Std.Queue α) :
    Std.HashMap α Nat × Std.Queue α :=
  neighbors.foldl (fun result target =>
    if active.contains target then
      let old := result.1.getD target 0
      (result.1.insert target (old - 1),
        if old == 1 then result.2.enqueue target else result.2)
    else
      result) (degrees, queue)

private abbrev ImplState (α : Type u) [BEq α] [Hashable α] :=
  Std.HashSet α × Std.HashMap α Nat × Std.Queue α × List α × Nat

private abbrev ImplState.active {α : Type u} [BEq α] [Hashable α]
    (s : ImplState α) : Std.HashSet α := s.1

private abbrev ImplState.degrees {α : Type u} [BEq α] [Hashable α]
    (s : ImplState α) : Std.HashMap α Nat := s.2.1

private abbrev ImplState.queue {α : Type u} [BEq α] [Hashable α]
    (s : ImplState α) : Std.Queue α := s.2.2.1

private abbrev ImplState.outputRev {α : Type u} [BEq α] [Hashable α]
    (s : ImplState α) : List α := s.2.2.2.1

private abbrev ImplState.count {α : Type u} [BEq α] [Hashable α]
    (s : ImplState α) : Nat := s.2.2.2.2

private def initialImplState {α : Type u} [DecidableEq α] [Hashable α]
    (g : DirectedAdjacency α) : ImplState α :=
  let degrees := initialDegreesImpl g
  (Std.HashSet.ofList g.vertices, degrees,
    Std.Queue.mk [] (g.vertices.filter fun v => degrees.getD v 0 == 0),
    [], g.vertices.length)

private def goImpl {α : Type u} [DecidableEq α] [Hashable α]
    (g : DirectedAdjacency α) : Nat → ImplState α → Result α
  | 0, state =>
      if state.2.2.2.2 == 0 then .success state.2.2.2.1.reverse
      else .failure state.2.2.2.1.reverse
        (g.vertices.filter fun v => state.1.contains v)
  | fuel + 1, state =>
      if state.2.2.2.2 == 0 then .success state.2.2.2.1.reverse
      else
        match state.2.2.1.dequeue? with
        | none => .failure state.2.2.2.1.reverse
            (g.vertices.filter fun v => state.1.contains v)
        | some (source, queue) =>
            let active := state.1.erase source
            let (degrees, queue) := updateNeighborsImpl active
              (dedupNeighborsImpl (g.adjacency source)) state.2.1 queue
            goImpl g fuel
              (active, degrees, queue, source :: state.2.2.2.1,
                state.2.2.2.2 - 1)

private def sortImpl {α : Type u} [DecidableEq α] [Hashable α]
    (g : DirectedAdjacency α) : Result α :=
  goImpl g g.vertices.length (initialImplState g)

private theorem dedupNeighborsImplAux_eq {α : Type u} [DecidableEq α] [Hashable α]
    (seen : Std.HashSet α) (seenModel : α → Bool)
    (hseen : ∀ x, seen.contains x = seenModel x) (neighbors : List α) :
    dedupNeighborsImplAux seen neighbors = dedupNeighbors seenModel neighbors := by
  induction neighbors generalizing seen seenModel with
  | nil => rfl
  | cons target neighbors induction =>
      by_cases hcontains : seen.contains target = true
      · have hmodel : seenModel target = true := (hseen target) ▸ hcontains
        simp [dedupNeighborsImplAux, dedupNeighbors, hcontains, hmodel,
          induction seen seenModel hseen]
      · have hcontainsFalse : seen.contains target = false :=
          Bool.eq_false_of_not_eq_true hcontains
        have hmodelFalse : seenModel target = false := (hseen target) ▸ hcontainsFalse
        rw [dedupNeighborsImplAux, dedupNeighbors]
        simp only [hcontainsFalse, hmodelFalse, Bool.false_eq_true, ↓reduceIte]
        congr 1
        apply induction
        intro x
        rw [Std.HashSet.contains_insert, hseen]
        by_cases hxt : x = target
        · subst x
          simp [Function.update]
        · simp [Function.update, hxt, Ne.symm hxt]

private theorem dedupNeighborsImpl_eq {α : Type u} [DecidableEq α] [Hashable α]
    (neighbors : List α) :
    dedupNeighborsImpl neighbors = dedupNeighbors (fun _ => false) neighbors := by
  apply dedupNeighborsImplAux_eq
  intro x
  simp

private def MapRel {α : Type u} [BEq α] [Hashable α]
    (actual : Std.HashMap α Nat) (model : α → Nat) : Prop :=
  ∀ x, actual.getD x 0 = model x

private theorem MapRel.insert {α : Type u} [DecidableEq α] [Hashable α]
    {actual : Std.HashMap α Nat} {model : α → Nat} (hrel : MapRel actual model)
    (key : α) (value : Nat) :
    MapRel (actual.insert key value) (Function.update model key value) := by
  intro x
  rw [Std.HashMap.getD_insert]
  by_cases hkx : key = x
  · subst x
    simp [Function.update]
  · simpa [hkx, Function.update, Ne.symm hkx] using hrel x

private theorem addEdgesImpl_getD {α : Type u} [DecidableEq α] [Hashable α]
    (degrees : Std.HashMap α Nat) (neighbors : List α) (x : α)
    (hnodup : neighbors.Nodup) :
    (addEdgesImpl degrees neighbors).getD x 0 =
      degrees.getD x 0 + if x ∈ neighbors then 1 else 0 := by
  induction neighbors generalizing degrees with
  | nil => simp [addEdgesImpl]
  | cons target neighbors induction =>
      have htarget : target ∉ neighbors := (List.nodup_cons.mp hnodup).1
      have htail : neighbors.Nodup := (List.nodup_cons.mp hnodup).2
      change (addEdgesImpl
        (degrees.insert target (degrees.getD target 0 + 1)) neighbors).getD x 0 = _
      rw [induction _ htail]
      by_cases hxt : x = target
      · subst x
        simp [Std.HashMap.getD_insert_self, htarget]
      · rw [Std.HashMap.getD_insert]
        simp [hxt, Ne.symm hxt]

private theorem initialDegreesFold_getD {α : Type u} [DecidableEq α] [Hashable α]
    (g : DirectedAdjacency α) (sources : List α) (degrees : Std.HashMap α Nat)
    (x : α) :
    (sources.foldl (fun result source =>
      addEdgesImpl result (dedupNeighborsImpl (g.adjacency source))) degrees).getD x 0 =
        degrees.getD x 0 + indegreeWithin g sources x := by
  induction sources generalizing degrees with
  | nil => simp [indegreeWithin]
  | cons source sources induction =>
      rw [List.foldl_cons, induction]
      rw [dedupNeighborsImpl_eq]
      rw [addEdgesImpl_getD _ _ _ (dedupNeighbors_nodup _ _)]
      by_cases hedge : g.hasEdge source x = true
      · have hmem : x ∈ dedupNeighbors (fun _ => false) (g.adjacency source) :=
          (mem_neighborScan g source x).2 hedge
        simp [indegreeWithin, hedge, hmem]
        omega
      · have hedgeFalse : g.hasEdge source x = false := Bool.eq_false_of_not_eq_true hedge
        have hnotmem : x ∉ dedupNeighbors (fun _ => false) (g.adjacency source) := by
          intro hmem
          exact hedge ((mem_neighborScan g source x).1 hmem)
        simp [indegreeWithin, hedgeFalse, hnotmem]

private theorem initialDegreesImpl_rel {α : Type u} [DecidableEq α] [Hashable α]
    (g : DirectedAdjacency α) :
    MapRel (initialDegreesImpl g) (indegreeWithin g g.vertices) := by
  intro x
  simpa [initialDegreesImpl] using
    initialDegreesFold_getD g g.vertices (∅ : Std.HashMap α Nat) x

private abbrev foldUpdate {α : Type u} [DecidableEq α]
    (g : DirectedAdjacency α) (removed : α) (remaining scan : List α)
    (degrees : α → Nat) (queue : Std.Queue α) : (α → Nat) × Std.Queue α :=
  scan.foldl (fun result v =>
    if v ∈ remaining && g.hasEdge removed v then
      let old := result.1 v
      (Function.update result.1 v (old - 1),
        if old == 1 then result.2.enqueue v else result.2)
    else
      result) (degrees, queue)

private theorem foldUpdate_eq {α : Type u} [DecidableEq α]
    (g : DirectedAdjacency α) (removed : α) (remaining scan : List α)
    (degrees : α → Nat) (queue : Std.Queue α) :
    foldUpdate g removed remaining scan degrees queue =
      updateNeighbors g removed remaining scan degrees queue := by
  induction scan generalizing degrees queue with
  | nil => simp [foldUpdate, updateNeighbors]
  | cons v scan ih =>
      by_cases hcond : (v ∈ remaining && g.hasEdge removed v) = true
      · rw [foldUpdate, updateNeighbors]
        have hcondProp : v ∈ remaining ∧ g.hasEdge removed v = true := by
          simpa only [Bool.and_eq_true, decide_eq_true_eq] using hcond
        simp [hcondProp]
        simpa [foldUpdate] using
          ih (Function.update degrees v (degrees v - 1))
            (if degrees v == 1 then queue.enqueue v else queue)
      · rw [foldUpdate, updateNeighbors]
        have hcondProp : ¬(v ∈ remaining ∧ g.hasEdge removed v = true) := by
          intro hp
          apply hcond
          simp [hp]
        simp [hcondProp]
        simpa [foldUpdate] using ih degrees queue

private def SetRel {α : Type u} [DecidableEq α] [Hashable α]
    (actual : Std.HashSet α) (model : List α) : Prop :=
  ∀ x, actual.contains x = decide (x ∈ model)

private theorem updateNeighborsImpl_rel {α : Type u} [DecidableEq α] [Hashable α]
    (g : DirectedAdjacency α) (removed : α) (remaining neighbors : List α)
    (active : Std.HashSet α) (actualDegrees : Std.HashMap α Nat)
    (modelDegrees : α → Nat) (actualQueue modelQueue : Std.Queue α)
    (hactive : SetRel active remaining)
    (hdegrees : MapRel actualDegrees modelDegrees)
    (hqueue : actualQueue = modelQueue)
    (hedges : ∀ x ∈ neighbors, g.hasEdge removed x = true) :
    let actual := updateNeighborsImpl active neighbors actualDegrees actualQueue
    let model := foldUpdate g removed remaining neighbors modelDegrees modelQueue
    actual.2 = model.2 ∧ MapRel actual.1 model.1 := by
  induction neighbors generalizing actualDegrees modelDegrees actualQueue modelQueue with
  | nil => simpa [updateNeighborsImpl, foldUpdate, hqueue] using hdegrees
  | cons target neighbors induction =>
      have hedge : g.hasEdge removed target = true := hedges target (by simp)
      have hedgesTail : ∀ x ∈ neighbors, g.hasEdge removed x = true := by
        intro x hx
        exact hedges x (by simp [hx])
      by_cases hmem : target ∈ remaining
      · have hcontains : active.contains target = true := by
          rw [hactive]
          simp [hmem]
        have hcontainsMem : target ∈ active := by
          simpa using hcontains
        have hmap :
            MapRel (actualDegrees.insert target (actualDegrees.getD target 0 - 1))
              (Function.update modelDegrees target (modelDegrees target - 1)) := by
          simpa [hdegrees target] using
            MapRel.insert hdegrees target (modelDegrees target - 1)
        have hqueue' :
            (if actualDegrees.getD target 0 == 1 then actualQueue.enqueue target else actualQueue) =
            (if modelDegrees target == 1 then modelQueue.enqueue target else modelQueue) := by
          rw [hdegrees target, hqueue]
        simpa [updateNeighborsImpl, foldUpdate, hcontainsMem, hmem, hedge] using
          induction (actualDegrees.insert target (actualDegrees.getD target 0 - 1))
            (Function.update modelDegrees target (modelDegrees target - 1))
            (if actualDegrees.getD target 0 == 1 then actualQueue.enqueue target else actualQueue)
            (if modelDegrees target == 1 then modelQueue.enqueue target else modelQueue)
            hmap hqueue' hedgesTail
      · have hcontains : active.contains target = false := by
          rw [hactive]
          simp [hmem]
        have hnotcontainsMem : target ∉ active := by
          simpa using hcontains
        simpa [updateNeighborsImpl, foldUpdate, hnotcontainsMem, hmem] using
          induction actualDegrees modelDegrees actualQueue modelQueue
            hdegrees hqueue hedgesTail

private theorem erase_eq_filter_ne {α : Type u} [DecidableEq α]
    (xs : List α) (target : α) (hnodup : xs.Nodup) (hmem : target ∈ xs) :
    xs.erase target = xs.filter fun x => decide (x ≠ target) := by
  induction xs with
  | nil => simp at hmem
  | cons x xs induction =>
      have htail : xs.Nodup := (List.nodup_cons.mp hnodup).2
      by_cases hxt : x = target
      · subst x
        have hnot : target ∉ xs := (List.nodup_cons.mp hnodup).1
        simp only [List.erase_cons_head, ne_eq, decide_not, decide_true, Bool.not_true,
          Bool.false_eq_true, not_false_eq_true, List.filter_cons_of_neg]
        symm
        apply List.filter_eq_self.mpr
        intro y hy
        have hyt : y ≠ target := by
          intro h
          subst y
          exact hnot hy
        simp [hyt]
      · have hmemTail : target ∈ xs := (List.mem_cons.mp hmem).resolve_left (Ne.symm hxt)
        simp [hxt, induction htail hmemTail]

private theorem filter_erase_active {α : Type u} [DecidableEq α] [Hashable α]
    (vertices : List α) (active : Std.HashSet α) (remaining : List α) (target : α)
    (hvertices : vertices.Nodup)
    (horder : vertices.filter (fun x => active.contains x) = remaining)
    (htarget : target ∈ remaining) :
    vertices.filter (fun x => (active.erase target).contains x) = remaining.erase target := by
  calc
    vertices.filter (fun x => (active.erase target).contains x) =
        vertices.filter (fun x => !(target == x) && active.contains x) := by
      apply List.filter_congr
      intro x hx
      exact Std.HashSet.contains_erase
    _ = (vertices.filter fun x => active.contains x).filter
          (fun x => !(target == x)) := by
      rw [List.filter_filter]
    _ = remaining.filter (fun x => !(target == x)) := by rw [horder]
    _ = remaining.filter (fun x => decide (x ≠ target)) := by
      apply List.filter_congr
      intro x hx
      by_cases hxt : x = target
      · subst x
        simp
      · simp [hxt, Ne.symm hxt]
    _ = remaining.erase target := by
      have hremainingNodup : remaining.Nodup := by
        rw [← horder]
        exact hvertices.filter _
      exact (erase_eq_filter_ne remaining target hremainingNodup htarget).symm

private theorem setRel_of_order {α : Type u} [DecidableEq α] [Hashable α]
    (g : DirectedAdjacency α) (active : Std.HashSet α) (remaining : List α)
    (horder : g.vertices.filter (fun x => active.contains x) = remaining) :
    SetRel active remaining := by
  intro x
  by_cases hcontains : active.contains x = true
  · have hmemFilter : x ∈ g.vertices.filter (fun y => active.contains y) := by
      simp [g.vertices_complete x, hcontains]
    have hmem : x ∈ remaining := horder ▸ hmemFilter
    simp [hcontains, hmem]
  · have hcontainsFalse : active.contains x = false :=
      Bool.eq_false_of_not_eq_true hcontains
    have hnotmem : x ∉ remaining := by
      intro hmem
      have hmemFilter : x ∈ g.vertices.filter (fun y => active.contains y) := horder.symm ▸ hmem
      simp [hcontainsFalse] at hmemFilter
    simp [hcontainsFalse, hnotmem]

private structure ImplRel {α : Type u} [DecidableEq α] [Hashable α]
    (g : DirectedAdjacency α) (actual : ImplState α) (model : State α) : Prop where
  remaining : g.vertices.filter (fun x => actual.active.contains x) = model.remaining
  degrees : MapRel actual.degrees model.degrees
  queue : actual.queue = model.queue
  output : actual.outputRev.reverse = model.output
  count : actual.count = model.remaining.length

private theorem initialImplState_rel {α : Type u} [DecidableEq α] [Hashable α]
    (g : DirectedAdjacency α) : ImplRel g (initialImplState g) (initialState g) := by
  have hdegrees := initialDegreesImpl_rel g
  constructor
  · change g.vertices.filter
      (fun x => (Std.HashSet.ofList g.vertices).contains x) = g.vertices
    apply List.filter_eq_self.mpr
    intro x hx
    rw [Std.HashSet.contains_ofList]
    simpa using hx
  · exact hdegrees
  · change Std.Queue.mk []
      (g.vertices.filter fun v => (initialDegreesImpl g).getD v 0 == 0) =
        Std.Queue.mk []
          (g.vertices.filter fun v => indegreeWithin g g.vertices v == 0)
    congr 1
    apply List.filter_congr
    intro x hx
    rw [hdegrees x]
  · rfl
  · rfl

private theorem implRel_after_dequeue {α : Type u} [DecidableEq α] [Hashable α]
    (g : DirectedAdjacency α) (actual : ImplState α) (model : State α)
    (source : α) (queue : Std.Queue α)
    (hrel : ImplRel g actual model) (hinv : StateInvariant g model)
    (hdequeue : model.queue.dequeue? = some (source, queue)) :
    let active := actual.active.erase source
    let actualUpdate := updateNeighborsImpl active
      (dedupNeighborsImpl (g.adjacency source)) actual.degrees queue
    let modelRemaining := model.remaining.erase source
    let modelUpdate := updateNeighbors g source modelRemaining
      (neighborScan g source) model.degrees queue
    ImplRel g
      (active, actualUpdate.1, actualUpdate.2, source :: actual.outputRev,
        actual.count - 1)
      (modelRemaining, modelUpdate.1, modelUpdate.2, model.output ++ [source]) := by
  have hcontents := Queue.contents_eq_cons_of_dequeue?_eq_some hdequeue
  have hsource : source ∈ model.remaining := hinv.queue_remaining source (by
    rw [hcontents]
    simp)
  have horder := filter_erase_active g.vertices actual.active model.remaining source
    g.vertices_nodup hrel.remaining hsource
  have hactive : SetRel (actual.active.erase source) (model.remaining.erase source) :=
    setRel_of_order g _ _ horder
  have hscan : dedupNeighborsImpl (g.adjacency source) = neighborScan g source := by
    exact dedupNeighborsImpl_eq _
  have hedges : ∀ x ∈ neighborScan g source, g.hasEdge source x = true := by
    intro x hx
    exact (mem_neighborScan g source x).1 hx
  have hupdate := updateNeighborsImpl_rel g source (model.remaining.erase source)
    (neighborScan g source) (actual.active.erase source) actual.degrees model.degrees
    queue queue hactive hrel.degrees rfl hedges
  rw [foldUpdate_eq] at hupdate
  rw [hscan]
  constructor
  · exact horder
  · exact hupdate.2
  · exact hupdate.1
  · change (source :: actual.outputRev).reverse = model.output ++ [source]
    simp [hrel.output]
  · rw [hrel.count, List.length_erase_of_mem hsource]

/-- **Kahn's topological sort.** Run Kahn's algorithm with a first-in first-out queue on a finite
directed graph $G$ whose vertices are enumerated as $v_1, \dots, v_n$. Initially every vertex is
remaining, the counter of each vertex is its number of in-neighbours, and the queue holds the
vertices with no in-neighbours in enumeration order. At each of $n$ steps, if the queue is nonempty,
its front vertex $x$ is removed from the queue and from the remaining vertices and appended to the
output; then each distinct out-neighbour $y$ of $x$ that is still remaining, taken in order of first
occurrence in the adjacency list of $x$, has its counter decreased by one and joins the back of the
queue if that counter was $1$. If no vertices remain after the $n$ steps, the result is a success
with the output list; otherwise it is a failure with the output list as the processed vertices and
the remaining vertices in enumeration order. -/
public def sort {α : Type u} [DecidableEq α] [Hashable α]
    (g : DirectedAdjacency α) : Result α :=
  let advance := fun (s : List α × (α → Nat) × Std.Queue α × List α) =>
    match s.2.2.1.dequeue? with
    | none => s
    | some (vertex, queue) =>
        let remaining := s.1.erase vertex
        let rec dedup (seen : α → Bool) : List α → List α
          | [] => []
          | target :: neighbors =>
              if seen target then dedup seen neighbors
              else target :: dedup (Function.update seen target true) neighbors
        let scan := dedup (fun _ => false) (g.adjacency vertex)
        let (degrees, queue) := scan.foldl (fun result v =>
              if v ∈ remaining && g.hasEdge vertex v then
                let old := result.1 v
                (Function.update result.1 v (old - 1),
                  if old == 1 then result.2.enqueue v else result.2)
              else
                result) (s.2.1, queue)
        (remaining, degrees, queue, s.2.2.2 ++ [vertex])
  let final := advance^[g.vertices.length]
    (g.vertices,
      indegreeWithin g g.vertices,
      Std.Queue.mk [] (g.vertices.filter fun v => indegreeWithin g g.vertices v == 0),
      [])
  if final.1.isEmpty then .success final.2.2.2 else .failure final.2.2.2 final.1

private theorem sort_dedup_eq_dedupNeighbors {α : Type u} [DecidableEq α]
    (seen : α → Bool) (neighbors : List α) :
    sort.dedup seen neighbors = dedupNeighbors seen neighbors := by
  induction neighbors generalizing seen with
  | nil => rfl
  | cons target neighbors induction =>
      by_cases hseen : seen target = true
      · simp [sort.dedup, dedupNeighbors, hseen, induction]
      · have hseenfalse : seen target = false := Bool.eq_false_of_not_eq_true hseen
        simp [sort.dedup, dedupNeighbors, hseenfalse, induction]

private abbrev sortAdvance {α : Type u} [DecidableEq α]
    (g : DirectedAdjacency α) (s : State α) : State α :=
  match s.queue.dequeue? with
  | none => s
  | some (vertex, queue) =>
      let remaining := s.remaining.erase vertex
      let scan := sort.dedup (fun _ => false) (g.adjacency vertex)
      let (degrees, queue) := scan.foldl (fun result v =>
            if v ∈ remaining && g.hasEdge vertex v then
              let old := result.1 v
              (Function.update result.1 v (old - 1),
                if old == 1 then result.2.enqueue v else result.2)
            else
              result) (s.degrees, queue)
      (remaining, degrees, queue, s.output ++ [vertex])

private abbrev advance {α : Type u} [DecidableEq α]
    (g : DirectedAdjacency α) (s : State α) : State α :=
  match s.queue.dequeue? with
  | none => s
  | some (vertex, queue) =>
      let remaining := s.remaining.erase vertex
      let (degrees, queue) :=
        foldUpdate g vertex remaining (neighborScan g vertex) s.degrees queue
      (remaining, degrees, queue, s.output ++ [vertex])

private theorem advance_eq_step {α : Type u} [DecidableEq α]
    (g : DirectedAdjacency α) (s : State α) :
    advance g s = match step g s with | none => s | some s' => s' := by
  cases hq : s.queue.dequeue? with
  | none => simp [advance, step, hq]
  | some pair =>
      rcases pair with ⟨vertex, queue⟩
      simp only [advance, step, hq]
      have hupd := foldUpdate_eq g vertex (s.remaining.erase vertex)
        (neighborScan g vertex) s.degrees queue
      simp only [foldUpdate] at hupd
      rw [hupd]

private abbrev finish {α : Type u} (s : State α) : Result α :=
  if s.remaining.isEmpty then .success s.output else .failure s.output s.remaining

private abbrev iterSort {α : Type u} [DecidableEq α]
    (g : DirectedAdjacency α) (fuel : Nat) (s : State α) : Result α :=
  finish ((advance g)^[fuel] s)

private theorem iterate_fixed {α : Type u} (f : α → α) (x : α)
    (h : f x = x) : ∀ n, f^[n] x = x := by
  intro n
  induction n with
  | zero => rfl
  | succ n => simpa [Function.iterate_succ_apply, h] using ‹f^[n] x = x›

private theorem iterSort_eq_loop {α : Type u} [DecidableEq α]
    (g : DirectedAdjacency α) (fuel : Nat) (s : State α) (hinv : StateInvariant g s)
    (hfuel : fuel = s.remaining.length) : iterSort g fuel s = loop g fuel s := by
  induction fuel generalizing s with
  | zero =>
      have hlen : s.remaining.length = 0 := by omega
      have hempty : s.remaining = [] := List.length_eq_zero_iff.mp hlen
      simp [iterSort, finish, loop, hempty]
  | succ fuel ih =>
      have hlen : s.remaining.length = fuel + 1 := by omega
      have hne : s.remaining ≠ [] := by
        intro hempty
        simp [hempty] at hlen
      have hisempty : s.remaining.isEmpty = false := by
        simpa [List.isEmpty_iff] using hne
      cases hstep : step g s with
      | none =>
          have hadvance : advance g s = s := by
            rw [advance_eq_step, hstep]
          have hiterate := iterate_fixed (advance g) s hadvance (fuel + 1)
          simp [iterSort, finish, loop, hiterate, hisempty, hstep]
      | some s' =>
          have hadvance : advance g s = s' := by
            rw [advance_eq_step, hstep]
          rw [iterSort, Function.iterate_succ_apply, hadvance]
          rw [loop, hisempty, hstep]
          change iterSort g fuel s' = loop g fuel s'
          apply ih s' (step_invariant g s s' hinv hstep)
          have hremaining := step_remaining_length g s s' hinv hstep
          omega

private theorem sort_eq_iterSort {α : Type u} [DecidableEq α] [Hashable α]
    (g : DirectedAdjacency α) :
    sort g = iterSort g g.vertices.length (initialState g) := by
  change finish ((sortAdvance g)^[g.vertices.length] (initialState g)) =
    finish ((advance g)^[g.vertices.length] (initialState g))
  have hadvance : sortAdvance g = advance g := by
    funext s
    cases hqueue : s.queue.dequeue? with
    | none => simp [sortAdvance, advance, hqueue]
    | some pair =>
        rcases pair with ⟨vertex, queue⟩
        simp [sortAdvance, advance, hqueue, sort_dedup_eq_dedupNeighbors,
          neighborScan]
  rw [hadvance]

private theorem sort_eq_loop {α : Type u} [DecidableEq α] [Hashable α]
    (g : DirectedAdjacency α) :
    sort g = loop g g.vertices.length (initialState g) := by
  rw [sort_eq_iterSort]
  exact iterSort_eq_loop g g.vertices.length (initialState g)
    (initialState_invariant g) rfl

private theorem goImpl_eq_loop {α : Type u} [DecidableEq α] [Hashable α]
    (g : DirectedAdjacency α) (fuel : Nat) (actual : ImplState α) (model : State α)
    (hrel : ImplRel g actual model) (hinv : StateInvariant g model)
    (hfuel : fuel = model.remaining.length) :
    goImpl g fuel actual = loop g fuel model := by
  induction fuel generalizing actual model with
  | zero =>
      have hlength : model.remaining.length = 0 := by omega
      have hempty : model.remaining = [] := List.length_eq_zero_iff.mp hlength
      have hcount : actual.count = 0 := by simpa [hempty] using hrel.count
      simp [goImpl, loop, hcount, hempty, hrel.output]
  | succ fuel induction =>
      have hlength : model.remaining.length = fuel + 1 := by omega
      have hne : model.remaining ≠ [] := by
        intro hempty
        simp [hempty] at hlength
      have hisEmpty : model.remaining.isEmpty = false := by
        simpa [List.isEmpty_iff] using hne
      have hcountNe : actual.count ≠ 0 := by
        rw [hrel.count]
        omega
      have hcountZero : (actual.count == 0) = false := by simpa using hcountNe
      cases hdequeue : model.queue.dequeue? with
      | none =>
          have hactualDequeue : actual.queue.dequeue? = none := by
            rw [hrel.queue, hdequeue]
          have hstep : step g model = none := by simp [step, hdequeue]
          simp [goImpl, loop, hcountZero, hisEmpty, hactualDequeue, hstep,
            hrel.output, hrel.remaining]
      | some pair =>
          rcases pair with ⟨source, queue⟩
          have hactualDequeue : actual.queue.dequeue? = some (source, queue) := by
            rw [hrel.queue, hdequeue]
          let active := actual.active.erase source
          let actualUpdate := updateNeighborsImpl active
            (dedupNeighborsImpl (g.adjacency source)) actual.degrees queue
          let actual' : ImplState α :=
            (active, actualUpdate.1, actualUpdate.2, source :: actual.outputRev,
              actual.count - 1)
          let modelRemaining := model.remaining.erase source
          let modelUpdate := updateNeighbors g source modelRemaining
            (neighborScan g source) model.degrees queue
          let model' : State α :=
            (modelRemaining, modelUpdate.1, modelUpdate.2, model.output ++ [source])
          have hstep : step g model = some model' := by
            simp [step, hdequeue, model', modelRemaining, modelUpdate]
          have hrel' : ImplRel g actual' model' := by
            exact implRel_after_dequeue g actual model source queue hrel hinv hdequeue
          have hinv' : StateInvariant g model' := step_invariant g model model' hinv hstep
          have hlength' : fuel = model'.remaining.length := by
            have := step_remaining_length g model model' hinv hstep
            omega
          rw [goImpl, loop, hcountZero, hisEmpty, hactualDequeue, hstep]
          exact induction actual' model' hrel' hinv' hlength'

private theorem sortImpl_eq_sort {α : Type u} [DecidableEq α] [Hashable α]
    (g : DirectedAdjacency α) : sortImpl g = sort g := by
  rw [sortImpl, sort_eq_loop]
  exact goImpl_eq_loop g g.vertices.length (initialImplState g) (initialState g)
    (initialImplState_rel g) (initialState_invariant g) rfl

/-- **Directed cycle within a vertex list.** Let $G$ be a finite directed graph and $R$ a list of
vertices. A list $c = [c_1, \dots, c_k]$ of vertices is a directed cycle of $G$ in $R$ when
$k \ge 1$, the vertices $c_1, \dots, c_k$ are pairwise distinct, $G$ has an edge from $c_i$ to
$c_{i+1}$ for each $1 \le i < k$ and an edge from $c_k$ to $c_1$, and every $c_i$ lies in $R$. -/
public def DirectedCycleIn {α : Type u}
    (g : DirectedAdjacency α) (remaining cycle : List α) : Prop :=
  cycle ≠ [] ∧
  cycle.Nodup ∧
  cycle.IsChain g.Edge ∧
  (match cycle with
    | [] => false
    | first :: rest => g.Edge (List.getLast (first :: rest) (by simp)) first) ∧
  ∀ v ∈ cycle, v ∈ remaining

/-- **Characterization of directed cycles within a vertex list.** Let $G$ be a finite directed
graph and let $R$ and $c = [c_1, \dots, c_k]$ be lists of vertices. Then $c$ is a directed cycle
of $G$ in $R$ if and only if $k \ge 1$, the vertices $c_1, \dots, c_k$ are pairwise distinct,
$G$ has an edge from $c_i$ to $c_{i+1}$ for every $1 \le i < k$, $G$ has an edge from $c_k$ to
$c_1$, and every $c_i$ lies in $R$. -/
public theorem directedCycleIn_iff {α : Type u}
    (g : DirectedAdjacency α) (remaining cycle : List α) :
    DirectedCycleIn g remaining cycle ↔
      ∃ hne : cycle ≠ [],
        cycle.Nodup ∧
        cycle.IsChain g.Edge ∧
        g.Edge (cycle.getLast hne) (cycle.head hne) ∧
        ∀ v ∈ cycle, v ∈ remaining := by
  constructor
  · rintro ⟨hne, hnodup, hchain, hclose, hmem⟩
    refine ⟨hne, hnodup, hchain, ?_, hmem⟩
    cases cycle with
    | nil => contradiction
    | cons first rest => simpa using hclose
  · rintro ⟨hne, hnodup, hchain, hclose, hmem⟩
    refine ⟨hne, hnodup, hchain, ?_, hmem⟩
    cases cycle with
    | nil => contradiction
    | cons first rest => simpa using hclose

private abbrev EdgeRel {α : Type u} (edge : α → α → Bool) : α → α → Prop :=
  fun u v => edge u v = true

private theorem existsCycleAux {α : Type u}
    (edge : α → α → Bool) (rem : List α)
    (hpred : ∀ v ∈ rem, ∃ u ∈ rem, edge u v = true)
    (v : α) (tail : List α)
    (hnodup : (v :: tail).Nodup)
    (hsub : ∀ x ∈ v :: tail, x ∈ rem)
    (hchain : (v :: tail).IsChain (EdgeRel edge)) :
    ∃ (cycle : List α) (first last : α),
      cycle.head? = some first ∧
      cycle.getLast? = some last ∧
      cycle.Nodup ∧
      cycle.IsChain (EdgeRel edge) ∧
      edge last first = true ∧
      ∀ x ∈ cycle, x ∈ rem := by
  classical
  obtain ⟨u, huRem, huv⟩ := hpred v (hsub v (by simp))
  by_cases huSeen : u ∈ v :: tail
  · obtain ⟨a, b, hab⟩ := List.append_of_mem huSeen
    have htake := hchain.take (a.length + 1)
    rw [hab] at htake
    have htakeEq : List.take (a.length + 1) (a ++ u :: b) = a ++ [u] := by
      rw [List.take_length_add_append]
      rfl
    have hcycleChain : (a ++ [u]).IsChain (EdgeRel edge) := by
      rw [htakeEq] at htake
      exact htake
    have hpathNodup : (a ++ u :: b).Nodup := by
      simpa [hab] using hnodup
    have hcycleNodup : (a ++ [u]).Nodup := by
      have htaken := hpathNodup.sublist (List.take_sublist (a.length + 1) (a ++ u :: b))
      rw [htakeEq] at htaken
      exact htaken
    have hhead : (a ++ [u]).head? = some v := by
      cases a with
      | nil =>
          simp at hab
          simp [hab]
      | cons x xs =>
          simp only [List.cons_append, List.cons.injEq] at hab
          simp [hab.1]
    refine ⟨a ++ [u], v, u, hhead, ?_, hcycleNodup, hcycleChain, huv, ?_⟩
    · simp
    · intro x hx
      apply hsub x
      rw [hab]
      simp only [List.mem_append, List.mem_cons]
      rcases List.mem_append.mp hx with hxa | hxu
      · exact Or.inl hxa
      · simp only [List.mem_singleton] at hxu
        exact Or.inr (Or.inl hxu)
  · have hnewNodup : (u :: v :: tail).Nodup := by simp [huSeen, hnodup]
    have hnewSub : ∀ x ∈ u :: v :: tail, x ∈ rem := by
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with hx | hx
      · simpa [hx] using huRem
      · exact hsub x (by simpa using hx)
    have hnewChain : (u :: v :: tail).IsChain (EdgeRel edge) := by
      simpa [EdgeRel] using And.intro huv hchain
    exact existsCycleAux edge rem hpred u (v :: tail) hnewNodup hnewSub hnewChain
termination_by rem.length - (v :: tail).length
decreasing_by
  have hlen : (u :: v :: tail).length ≤ rem.length :=
    hnewNodup.length_le_of_subset hnewSub
  apply Nat.sub_succ_lt_self
  exact Nat.lt_of_succ_le (by simpa [Nat.add_assoc] using hlen)

private theorem exists_nodup_cycle_of_internal_predecessor {α : Type u}
    (edge : α → α → Bool) (rem : List α)
    (hne : rem ≠ [])
    (hpred : ∀ v ∈ rem, ∃ u ∈ rem, edge u v = true) :
    ∃ (cycle : List α) (hcycle : cycle ≠ []),
      cycle.Nodup ∧
      cycle.IsChain (fun u v => edge u v = true) ∧
      edge (cycle.getLast hcycle) (cycle.head hcycle) = true ∧
      ∀ x ∈ cycle, x ∈ rem := by
  classical
  have hraw : ∃ (cycle : List α) (first last : α),
      cycle.head? = some first ∧
      cycle.getLast? = some last ∧
      cycle.Nodup ∧
      cycle.IsChain (EdgeRel edge) ∧
      edge last first = true ∧
      ∀ x ∈ cycle, x ∈ rem := by
    cases rem with
    | nil => contradiction
    | cons v tail =>
        exact existsCycleAux edge (v :: tail) hpred v [] (by simp) (by simp) (by simp)
  obtain ⟨cycle, first, last, hhead, hlast, hnodup, hchain, hclose, hsub⟩ := hraw
  have hcycle : cycle ≠ [] := by
    intro hnil
    simp [hnil] at hhead
  have hfirst : cycle.head hcycle = first :=
    (List.head_eq_iff_head?_eq_some hcycle).2 hhead
  have hlast' : cycle.getLast hcycle = last :=
    (List.getLast_eq_iff_getLast?_eq_some hcycle).2 hlast
  refine ⟨cycle, hcycle, hnodup, hchain, ?_, hsub⟩
  simpa [hfirst, hlast'] using hclose

/-- **Acyclic directed graph.** A finite directed graph $G$ is acyclic when it has no directed
cycle, that is, no nonempty list $[c_1, \dots, c_k]$ of pairwise distinct vertices such that $G$
has an edge from $c_i$ to $c_{i+1}$ for each $1 \le i < k$ and an edge from $c_k$ to $c_1$. -/
public def IsAcyclic {α : Type u} (g : DirectedAdjacency α) : Prop :=
  ¬ ∃ cycle, DirectedCycleIn g g.vertices cycle

/-- **Acyclicity means having no directed cycle.** A finite directed graph $G$ is acyclic if and
only if there is no directed cycle of $G$ in its vertex list, that is, no nonempty list of
pairwise distinct vertices in which each vertex has an edge to the next and the last vertex has
an edge to the first. -/
public theorem isAcyclic_iff_no_directedCycle {α : Type u}
    (g : DirectedAdjacency α) :
    IsAcyclic g ↔ ¬ ∃ cycle, DirectedCycleIn g g.vertices cycle := Iff.rfl

/-- **Topological order.** A list $L$ of vertices of a finite directed graph $G$ is a topological
order of $G$ when $L$ has no duplicates, a vertex lies in $L$ exactly when it lies in the vertex
enumeration of $G$, and for every edge $u \to v$ of $G$ the first position of $u$ in $L$ is strictly
smaller than the first position of $v$ in $L$. -/
public def IsTopologicalOrder {α : Type u} [DecidableEq α]
    (g : DirectedAdjacency α) (order : List α) : Prop :=
  order.Nodup ∧
  (∀ v, v ∈ order ↔ v ∈ g.vertices) ∧
  ∀ u v, g.Edge u v → order.idxOf u < order.idxOf v

private theorem sort_terminal {α : Type u} [DecidableEq α] [Hashable α]
    (g : DirectedAdjacency α) :
    TerminalSpec g (sort g) := by
  rw [sort_eq_loop]
  exact loop_spec g g.vertices.length (initialState g) (initialState_invariant g) rfl

private theorem edge_idxOf_lt_of_state {α : Type u} [DecidableEq α]
    (g : DirectedAdjacency α) (s : State α) (hinv : StateInvariant g s)
    (u v : α) (hu : u ∈ s.output) (hv : v ∈ s.output)
    (hedge : g.hasEdge u v = true) : s.output.idxOf u < s.output.idxOf v := by
  by_cases huv : u = v
  · subst v
    have := hinv.output_no_self u hu
    simp_all
  · have hui := List.idxOf_lt_length_of_mem hu
    have hvi := List.idxOf_lt_length_of_mem hv
    by_contra hnot
    have hle : s.output.idxOf v ≤ s.output.idxOf u := Nat.le_of_not_gt hnot
    have hne : s.output.idxOf v ≠ s.output.idxOf u := by
      intro heq
      apply huv
      exact (List.idxOf_inj hu).mp heq.symm
    have hlt : s.output.idxOf v < s.output.idxOf u := Nat.lt_of_le_of_ne hle hne
    have hback := hinv.output_ordered.rel_getElem_of_lt hvi hui hlt
    rw [List.getElem_idxOf hvi, List.getElem_idxOf hui] at hback
    simp_all

/-- **A successful topological sort has no repeated vertex.** If Kahn's topological sort on a
finite directed graph $G$ returns a success with list $L$, then $L$ has no duplicates. -/
public theorem success_nodup {α : Type u} [DecidableEq α] [Hashable α]
    (g : DirectedAdjacency α) (order : List α)
    (h : sort g = .success order) : order.Nodup := by
  have ht := sort_terminal g
  rw [h] at ht
  cases ht with
  | success s hinv hempty => exact hinv.output_nodup

/-- **A successful topological sort lists every vertex.** If Kahn's topological sort on a finite
directed graph $G$ returns a success with list $L$, then a vertex lies in $L$ if and only if it
lies in the vertex enumeration of $G$. -/
public theorem success_coverage {α : Type u} [DecidableEq α] [Hashable α]
    (g : DirectedAdjacency α) (order : List α)
    (h : sort g = .success order) : ∀ v, v ∈ order ↔ v ∈ g.vertices := by
  have ht := sort_terminal g
  rw [h] at ht
  cases ht with
  | success s hinv hempty =>
      intro v
      rw [hinv.coverage]
      simp [hempty]

/-- **A successful topological sort points every edge forward.** If Kahn's topological sort on a
finite directed graph $G$ returns a success with list $L$, then for every edge $u \to v$ of $G$ the
first position of $u$ in $L$ is strictly smaller than the first position of $v$ in $L$. -/
public theorem success_edge_forward {α : Type u} [DecidableEq α] [Hashable α]
    (g : DirectedAdjacency α) (order : List α) (h : sort g = .success order) :
    ∀ u v, g.Edge u v → order.idxOf u < order.idxOf v := by
  have ht := sort_terminal g
  rw [h] at ht
  cases ht with
  | success s hinv hempty =>
      intro u v hedge
      apply edge_idxOf_lt_of_state g s hinv u v
      · exact (hinv.coverage u).mp (g.vertices_complete u) |>.resolve_right (by simp [hempty])
      · exact (hinv.coverage v).mp (g.vertices_complete v) |>.resolve_right (by simp [hempty])
      · exact (g.hasEdge_eq_true u v).2 hedge

/-- **A successful topological sort is a topological order.** If Kahn's topological sort on a
finite directed graph $G$ returns a success with list $L$, then $L$ is a topological
order of $G$. -/
public theorem success_isTopologicalOrder {α : Type u} [DecidableEq α] [Hashable α]
    (g : DirectedAdjacency α) (order : List α) (h : sort g = .success order) :
    IsTopologicalOrder g order := by
  refine ⟨success_nodup g order h, ?_, success_edge_forward g order h⟩
  intro v
  exact success_coverage g order h v

/-- **A failed Kahn run splits the vertices into processed and unprocessed ones.** Let $G$ be a
finite directed graph. If deterministic FIFO Kahn topological sorting of $G$ fails after
processing the vertex list $P$ and leaving the vertex list $R$ unprocessed, then $R$ is nonempty,
neither $P$ nor $R$ has repeated entries, a vertex lies in the vertex list of $G$ if and only if
it lies in $P$ or in $R$, and no vertex lies in both $P$ and $R$. -/
public theorem failure_remainder {α : Type u} [DecidableEq α] [Hashable α]
    (g : DirectedAdjacency α) (processed remaining : List α)
    (h : sort g = .failure processed remaining) :
    remaining ≠ [] ∧ processed.Nodup ∧ remaining.Nodup ∧
      (∀ v, v ∈ g.vertices ↔ v ∈ processed ∨ v ∈ remaining) ∧
      (∀ v ∈ processed, v ∉ remaining) := by
  have ht := sort_terminal g
  rw [h] at ht
  cases ht with
  | failure s hinv hne hq =>
      exact ⟨hne, hinv.output_nodup, hinv.remaining_nodup,
        hinv.coverage, hinv.disjoint⟩

/-- **Unprocessed vertices of a failed Kahn run have positive indegree among the unprocessed.**
Let $G$ be a finite directed graph. If deterministic FIFO Kahn topological sorting of $G$ fails
after processing the vertex list $P$ and leaving the vertex list $R$ unprocessed, then for every
vertex $v$ in $R$ the indegree of $v$ within $R$, the number of entries $u$ of $R$ such that $G$
has an edge from $u$ to $v$, is positive. -/
public theorem failure_positive_indegree {α : Type u} [DecidableEq α] [Hashable α]
    (g : DirectedAdjacency α) (processed remaining : List α)
    (h : sort g = .failure processed remaining) :
    ∀ v ∈ remaining, 0 < indegreeWithin g remaining v := by
  have ht := sort_terminal g
  rw [h] at ht
  cases ht with
  | failure s hinv hne hq =>
      intro v hv
      rw [← hinv.degrees v hv]
      apply Nat.pos_of_ne_zero
      intro hz
      have hvq := hinv.zero_queued v hv hz
      rw [hq] at hvq
      exact List.not_mem_nil hvq

/-- **A failed Kahn run leaves a directed cycle.** Let $G$ be a finite directed graph. If
deterministic FIFO Kahn topological sorting of $G$ fails after processing the vertex list $P$
and leaving the vertex list $R$ unprocessed, then $G$ has a directed cycle in $R$: a nonempty
list of pairwise distinct vertices of $R$ in which each vertex has an edge to the next and the
last vertex has an edge to the first. -/
public theorem failure_cycle {α : Type u} [DecidableEq α] [Hashable α]
    (g : DirectedAdjacency α) (processed remaining : List α)
    (h : sort g = .failure processed remaining) :
    ∃ cycle, DirectedCycleIn g remaining cycle := by
  have hne := (failure_remainder g processed remaining h).1
  have hpred : ∀ v ∈ remaining, ∃ u ∈ remaining, g.hasEdge u v = true := by
    intro v hv
    have hpos := failure_positive_indegree g processed remaining h v hv
    rw [indegreeWithin, List.countP_eq_length_filter, List.length_pos_iff] at hpos
    obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil _ hpos
    simp only [List.mem_filter] at hu
    exact ⟨u, hu.1, hu.2⟩
  obtain ⟨cycle, hcycle, hnodup, hchain, hclose, hmem⟩ :=
    exists_nodup_cycle_of_internal_predecessor g.hasEdge remaining hne hpred
  exact ⟨cycle, (directedCycleIn_iff g remaining cycle).2
    ⟨hcycle, hnodup,
      hchain.imp (fun _ _ hedge => (g.hasEdge_eq_true _ _).1 hedge),
      (g.hasEdge_eq_true _ _).1 hclose, hmem⟩⟩

/-- **Success of Kahn's algorithm implies acyclicity.** If Kahn's topological sort on a finite
directed graph $G$ returns a success, then $G$ is acyclic. -/
public theorem success_implies_acyclic {α : Type u} [DecidableEq α] [Hashable α]
    (g : DirectedAdjacency α) (order : List α) (h : sort g = .success order) : IsAcyclic g := by
  intro hcycle
  obtain ⟨cycle, hc⟩ := hcycle
  obtain ⟨hne, hnodup, hchain, hclose, hmem⟩ :=
    (directedCycleIn_iff g g.vertices cycle).1 hc
  have hforward := success_edge_forward g order h
  have hidxchain : cycle.IsChain (fun u v => order.idxOf u < order.idxOf v) :=
    hchain.imp (fun _ _ hedge => hforward _ _ hedge)
  have hidxclose :
      order.idxOf (cycle.getLast hne) < order.idxOf (cycle.head hne) :=
    hforward _ _ hclose
  cases cycle with
  | nil => contradiction
  | cons x xs =>
      cases xs with
      | nil => simp at hidxclose
      | cons y ys =>
          have hfirstlast :
              order.idxOf x < order.idxOf ((x :: y :: ys).getLast (by simp)) := by
            apply hidxchain.rel_cons
            simp
          simp only [List.head_cons] at hidxclose
          omega

/-- **Kahn's algorithm succeeds on acyclic graphs.** If a finite directed graph $G$, given by a
vertex enumeration and adjacency lists, is acyclic, then deterministic FIFO Kahn topological
sorting of $G$ returns success with some vertex order. -/
public theorem acyclic_implies_success {α : Type u} [DecidableEq α] [Hashable α]
    (g : DirectedAdjacency α) (hacyclic : IsAcyclic g) :
    ∃ order, sort g = .success order := by
  cases hsort : sort g with
  | success order => exact ⟨order, rfl⟩
  | failure processed remaining =>
      exfalso
      obtain ⟨cycle, hcycle⟩ := failure_cycle g processed remaining hsort
      apply hacyclic
      refine ⟨cycle, ?_⟩
      obtain ⟨hne, hnodup, hchain, hclose, hmem⟩ :=
        (directedCycleIn_iff g remaining cycle).1 hcycle
      apply (directedCycleIn_iff g g.vertices cycle).2
      refine ⟨hne, hnodup, hchain, hclose, ?_⟩
      intro v hv
      exact (failure_remainder g processed remaining hsort).2.2.2.1 v |>.mpr
        (Or.inr (hmem v hv))

/-- **Kahn's algorithm succeeds exactly on acyclic graphs.** For every finite directed graph $G$,
Kahn's topological sort on $G$ returns a success if and only if $G$ is acyclic. -/
public theorem succeeds_iff_acyclic {α : Type u} [DecidableEq α] [Hashable α]
    (g : DirectedAdjacency α) :
    (∃ order, sort g = .success order) ↔ IsAcyclic g := by
  constructor
  · rintro ⟨order, h⟩
    exact success_implies_acyclic g order h
  · exact acyclic_implies_success g

end TopologicalSort

end Cslib.Algorithms.Lean
