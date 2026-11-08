/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.BreadthFirstSearch
public import Cslib.Algorithms.Lean.TimeM

import Std.Data.HashMap.Lemmas

/-!
# Breadth-first predecessor-tree execution

This module augments the existing ordered FIFO search with first-discovery parents.
A parent is recorded in the same branch that inserts its distance and enqueues the vertex.
Previously discovered neighbors never overwrite their parents, including tied alternatives.

The selected-event model charges dequeue attempts, adjacency membership checks, enqueues
and parent writes. The existing fixed vertex-count schedule includes empty dequeue attempts.
These annotations do not include hashing internals or establish a full RAM cost bound.

The source is CLRS, fourth edition, section 20.2, pages 555-562. Its Lemma 20.6 proof's
edge/reachability iff omits the first-discovery guard; the implementation preserves that guard.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.BreadthFirstSearch

universe u

/-- The existing BFS output together with the actual first-discovery predecessor table. -/
public structure BFSForest (V : Type u) extends BFSResult V where
  /-- The source and unreachable vertices have no predecessor. -/
  predecessor : V → Option V

private structure ParentState (V : Type u) [BEq V] [Hashable V] where
  core : List (V × Nat) × (Std.Queue (V × Nat) × Std.HashMap V Nat)
  parents : Std.HashMap V V

@[no_expose] private def scanParents {V : Type u} [BEq V] [Hashable V]
    (parent : V) (distance : Nat) : List V → ParentState V → TimeM Nat (ParentState V)
  | [], state => pure state
  | vertex :: neighbors, state => do
      ✓ let seen := state.core.2.2.contains vertex
      if seen then
        scanParents parent distance neighbors state
      else
        let distances := state.core.2.2.insert vertex (distance + 1)
        ✓ let parents := state.parents.insert vertex parent
        ✓ let queue := state.core.2.1.enqueue (vertex, distance + 1)
        scanParents parent distance neighbors
          ⟨(state.core.1, (queue, distances)), parents⟩

@[no_expose] private def parentStep {V : Type u} [BEq V] [Hashable V]
    (graph : DirectedAdjacency V) (state : ParentState V) : TimeM Nat (ParentState V) := do
  ✓ let next := state.core.2.1.dequeue?
  match next with
  | none => pure state
  | some (entry, queue) =>
      scanParents entry.1 entry.2 (graph.adjacency entry.1)
        ⟨(entry :: state.core.1, (queue, state.core.2.2)), state.parents⟩

@[no_expose] private def parentRun {V : Type u} [BEq V] [Hashable V]
    (graph : DirectedAdjacency V) (fuel : Nat) (state : ParentState V) :
    TimeM Nat (ParentState V) :=
  Nat.fold fuel (fun _ _ computation => do
    let current ← computation
    parentStep graph current) (pure state)

@[no_expose] private def parentInitial {V : Type u} [BEq V] [Hashable V]
    (source : V) : TimeM Nat (ParentState V) := do
  ✓ let queue := (Std.Queue.empty : Std.Queue (V × Nat)).enqueue (source, 0)
  return ⟨([], (queue, (Std.HashMap.emptyWithCapacity 1).insert source 0)),
    Std.HashMap.emptyWithCapacity 1⟩

/-- Run the existing FIFO BFS schedule with first-discovery parents and selected event costs. -/
public def bfsWithParents {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (graph : DirectedAdjacency V) (source : V) : TimeM Nat (BFSForest V) := do
  let initial ← parentInitial source
  let final ← parentRun graph graph.vertices.length initial
  return {
    toBFSResult := {
      distance := fun vertex => final.core.2.2[vertex]?
      order := final.core.1.reverse.map Prod.fst }
    predecessor := fun vertex => final.parents[vertex]? }

@[no_expose] private def followParents {V : Type u} [BEq V]
    (predecessor : V → Option V) (source : V) :
    Nat → V → List V → TimeM Nat (Option (List V))
  | fuel, current, suffix => do
      ✓ let atSource := current == source
      if atSource then
        ✓ return some (current :: suffix)
      else
        match fuel with
        | 0 => return none
        | fuel + 1 =>
            ✓ let previous := predecessor current
            match previous with
            | none => return none
            | some parent =>
                ✓ let suffix := current :: suffix
                followParents predecessor source fuel parent suffix

/-- Follow saved parents, returning the endpoint-inclusive source-to-target list.
Malformed tables are totalized by the visited-vertex count. Costs count source comparisons,
parent reads and actual vertex cons operations, not IO printing latency. -/
public def BFSForest.pathTo? {V : Type u} [BEq V]
    (forest : BFSForest V) (source target : V) : TimeM Nat (Option (List V)) :=
  followParents forest.predecessor source forest.order.length target []

@[no_expose] private def parentEntries {V : Type u} [BEq V] [Hashable V]
    (state : ParentState V) : List (V × Nat) :=
  state.core.1.reverse ++ Queue.contents state.core.2.1

private structure ParentInvariant {V : Type u} [BEq V] [Hashable V]
    (graph : DirectedAdjacency V) (source : V) (state : ParentState V) : Prop where
  map_matches : ∀ (vertex : V) (distance : Nat),
    state.core.2.2[vertex]? = some distance ↔ (vertex, distance) ∈ parentEntries state
  nodup : (parentEntries state |>.map Prod.fst).Nodup
  source_zero : state.core.2.2[source]? = some 0
  parent_none : ∀ (vertex : V),
    state.parents[vertex]? = none ↔ vertex = source ∨ state.core.2.2[vertex]? = none
  parent_edge : ∀ (vertex parent : V),
    state.parents[vertex]? = some parent → graph.Edge parent vertex
  parent_distance : ∀ (vertex parent : V),
    state.parents[vertex]? = some parent →
      ∃ distance : Nat, state.core.2.2[parent]? = some distance ∧
        state.core.2.2[vertex]? = some (distance + 1)

@[no_expose] private def coreStep {V : Type u} [BEq V] [Hashable V]
    (graph : DirectedAdjacency V)
    (core : List (V × Nat) × (Std.Queue (V × Nat) × Std.HashMap V Nat)) :
    List (V × Nat) × (Std.Queue (V × Nat) × Std.HashMap V Nat) :=
  match core.2.1.dequeue? with
  | none => core
  | some (entry, queue) =>
      (graph.adjacency entry.1).foldl (fun current vertex =>
        if current.2.2.contains vertex then current
        else (current.1, (current.2.1.enqueue (vertex, entry.2 + 1),
          current.2.2.insert vertex (entry.2 + 1))))
        (entry :: core.1, (queue, core.2.2))

@[expose] public section

private lemma parentInvariant_insert {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (graph : DirectedAdjacency V) (source : V) (state : ParentState V)
    (parent vertex : V) (distance : Nat)
    (invariant : ParentInvariant graph source state)
    (parent_distance : state.core.2.2[parent]? = some distance)
    (edge : graph.Edge parent vertex)
    (fresh : state.core.2.2.contains vertex = false) :
    ParentInvariant graph source
      ⟨(state.core.1, (state.core.2.1.enqueue (vertex, distance + 1),
          state.core.2.2.insert vertex (distance + 1))), state.parents.insert vertex parent⟩ := by
  have fresh_none : state.core.2.2[vertex]? = none :=
    Std.HashMap.getElem?_eq_none_of_contains_eq_false fresh
  have vertex_ne_source : vertex ≠ source := by
    intro h
    subst vertex
    rw [invariant.source_zero] at fresh_none
    contradiction
  have vertex_ne_parent : vertex ≠ parent := by
    intro h
    subst vertex
    rw [parent_distance] at fresh_none
    contradiction
  have vertex_not_mem : vertex ∉ (parentEntries state).map Prod.fst := by
    intro h
    obtain ⟨⟨other, otherDistance⟩, hentry, heq⟩ := List.mem_map.mp h
    dsimp at heq
    subst other
    have hlookup := (invariant.map_matches vertex otherDistance).2 hentry
    rw [fresh_none] at hlookup
    contradiction
  have inserted_map_matches : ∀ (other : V) (otherDistance : Nat),
      (state.core.2.2.insert vertex (distance + 1))[other]? = some otherDistance ↔
        (other, otherDistance) ∈ parentEntries state ++ [(vertex, distance + 1)] := by
    intro other otherDistance
    by_cases h : other = vertex
    · subst other
      rw [Std.HashMap.getElem?_insert_self]
      simp only [List.mem_append, List.mem_singleton]
      rw [← invariant.map_matches]
      simp [fresh_none, eq_comm]
    · rw [Std.HashMap.getElem?_insert]
      have hbeq : (vertex == other) = false := by
        simp [Ne.symm h]
      rw [hbeq]
      simp only [Bool.false_eq_true, ite_false]
      rw [invariant.map_matches]
      simp [h]
  refine {
    map_matches := ?_
    nodup := ?_
    source_zero := ?_
    parent_none := ?_
    parent_edge := ?_
    parent_distance := ?_
  }
  · intro other otherDistance
    simpa [parentEntries, Queue.contents_enqueue, List.append_assoc] using
      inserted_map_matches other otherDistance
  · have hnodup : ((parentEntries state).map Prod.fst ++ [vertex]).Nodup := by
      rw [List.nodup_append]
      refine ⟨invariant.nodup, by simp, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst b
      intro h
      subst a
      exact vertex_not_mem ha
    simpa [parentEntries, Queue.contents_enqueue, List.append_assoc] using hnodup
  · simpa [Std.HashMap.getElem?_insert, vertex_ne_source] using invariant.source_zero
  · intro other
    by_cases h : other = vertex
    · subst other
      simp [vertex_ne_source]
    · rw [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_insert]
      have hbeq : (vertex == other) = false := by
        simp [Ne.symm h]
      rw [hbeq]
      simp only [Bool.false_eq_true, ite_false]
      exact invariant.parent_none other
  · intro other otherParent hparent
    by_cases h : other = vertex
    · subst other
      rw [Std.HashMap.getElem?_insert_self] at hparent
      cases hparent
      exact edge
    · rw [Std.HashMap.getElem?_insert] at hparent
      have hbeq : (vertex == other) = false := by
        simp [Ne.symm h]
      rw [hbeq] at hparent
      simp only [Bool.false_eq_true, ite_false] at hparent
      have oldParent : state.parents[other]? = some otherParent := hparent
      exact invariant.parent_edge other otherParent oldParent
  · intro other otherParent hparent
    by_cases h : other = vertex
    · subst other
      rw [Std.HashMap.getElem?_insert_self] at hparent
      cases hparent
      refine ⟨distance, ?_, Std.HashMap.getElem?_insert_self⟩
      rw [Std.HashMap.getElem?_insert]
      have hbeq : (vertex == parent) = false := by
        simp [vertex_ne_parent]
      rw [hbeq]
      simp only [Bool.false_eq_true, ite_false]
      exact parent_distance
    · rw [Std.HashMap.getElem?_insert] at hparent
      have hbeq : (vertex == other) = false := by
        simp [Ne.symm h]
      rw [hbeq] at hparent
      simp only [Bool.false_eq_true, ite_false] at hparent
      have oldParent : state.parents[other]? = some otherParent := hparent
      obtain ⟨oldDistance, hparentDistance, hotherDistance⟩ :=
        invariant.parent_distance other otherParent oldParent
      have otherParent_ne_vertex : otherParent ≠ vertex := by
        intro heq
        subst otherParent
        rw [fresh_none] at hparentDistance
        contradiction
      refine ⟨oldDistance, ?_, ?_⟩
      · rw [Std.HashMap.getElem?_insert]
        have hparentBeq : (vertex == otherParent) = false := by
          simp [Ne.symm otherParent_ne_vertex]
        rw [hparentBeq]
        simp only [Bool.false_eq_true, ite_false]
        exact hparentDistance
      · rw [Std.HashMap.getElem?_insert]
        rw [hbeq]
        simp only [Bool.false_eq_true, ite_false]
        exact hotherDistance

private lemma parentInitial_invariant {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (graph : DirectedAdjacency V) (source : V) :
    ParentInvariant graph source (parentInitial source).ret := by
  constructor
  · intro vertex distance
    by_cases h : source = vertex
    · subst vertex
      simpa [parentInitial, parentEntries] using (eq_comm : 0 = distance ↔ distance = 0)
    · have h' : vertex ≠ source := Ne.symm h
      simp [parentInitial, parentEntries, h, h']
  · simp [parentInitial, parentEntries]
  · simp [parentInitial]
  · intro vertex
    by_cases h : source = vertex
    · subst vertex
      simp [parentInitial]
    · have h' : vertex ≠ source := Ne.symm h
      simp [parentInitial, h, h']
  · intro vertex parent h
    simp [parentInitial] at h
  · intro vertex parent h
    simp [parentInitial] at h



private lemma parentEntries_dequeue {V : Type u} [BEq V] [Hashable V]
    (state : ParentState V) (entry : V × Nat) (queue : Std.Queue (V × Nat))
    (h : state.core.2.1.dequeue? = some (entry, queue)) :
    parentEntries ⟨(entry :: state.core.1, (queue, state.core.2.2)), state.parents⟩ =
      parentEntries state := by
  simp [parentEntries, Queue.contents_eq_cons_of_dequeue?_eq_some h, List.append_assoc]

private lemma parentInvariant_dequeue {V : Type u} [BEq V] [Hashable V]
    (graph : DirectedAdjacency V) (source : V) (state : ParentState V)
    (entry : V × Nat) (queue : Std.Queue (V × Nat))
    (h : state.core.2.1.dequeue? = some (entry, queue))
    (invariant : ParentInvariant graph source state) :
    ParentInvariant graph source
      ⟨(entry :: state.core.1, (queue, state.core.2.2)), state.parents⟩ := by
  constructor
  · simpa only [parentEntries_dequeue state entry queue h] using invariant.map_matches
  · simpa only [parentEntries_dequeue state entry queue h] using invariant.nodup
  · exact invariant.source_zero
  · exact invariant.parent_none
  · exact invariant.parent_edge
  · exact invariant.parent_distance

private lemma scanParents_invariant {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (graph : DirectedAdjacency V) (source parent : V) (distance : Nat)
    (neighbors : List V) (state : ParentState V)
    (invariant : ParentInvariant graph source state)
    (parentFound : state.core.2.2[parent]? = some distance)
    (edges : ∀ vertex ∈ neighbors, graph.Edge parent vertex) :
    ParentInvariant graph source (scanParents parent distance neighbors state).ret := by
  induction neighbors generalizing state with
  | nil => exact invariant
  | cons vertex neighbors ih =>
      cases fresh : state.core.2.2.contains vertex with
      | false =>
          have different : vertex ≠ parent := by
            intro same
            subst vertex
            rw [Std.HashMap.contains_eq_isSome_getElem?, parentFound] at fresh
            contradiction
          simp only [scanParents, TimeM.ret_bind, fresh, Bool.false_eq_true, ↓reduceIte]
          apply ih
          · exact parentInvariant_insert graph source state parent vertex distance
              invariant parentFound (edges vertex (List.mem_cons_self)) fresh
          · simp [Std.HashMap.getElem?_insert, different, parentFound]
          · intro other member
            exact edges other (List.mem_cons_of_mem vertex member)
      | true =>
          simp only [scanParents, TimeM.ret_bind, fresh, ↓reduceIte]
          exact ih state invariant parentFound
            (fun other member => edges other (List.mem_cons_of_mem vertex member))

private lemma parentStep_invariant {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (graph : DirectedAdjacency V) (source : V) (state : ParentState V)
    (invariant : ParentInvariant graph source state) :
    ParentInvariant graph source (parentStep graph state).ret := by
  cases next : state.core.2.1.dequeue? with
  | none => simpa [parentStep, next] using invariant
  | some pair =>
      rcases pair with ⟨entry, queue⟩
      have entryFound : state.core.2.2[entry.1]? = some entry.2 := by
        apply (invariant.map_matches entry.1 entry.2).mpr
        simp [parentEntries, Queue.contents_eq_cons_of_dequeue?_eq_some next]
      simp only [parentStep, TimeM.ret_bind, next]
      exact scanParents_invariant graph source entry.1 entry.2
        (graph.adjacency entry.1)
        ⟨(entry :: state.core.1, (queue, state.core.2.2)), state.parents⟩
        (parentInvariant_dequeue graph source state entry queue next invariant) entryFound
        (fun _ member => member)

private lemma parentRun_invariant {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (graph : DirectedAdjacency V) (source : V) (fuel : Nat) (state : ParentState V)
    (invariant : ParentInvariant graph source state) :
    ParentInvariant graph source (parentRun graph fuel state).ret := by
  induction fuel with
  | zero => simpa [parentRun] using invariant
  | succ fuel ih =>
      simpa only [parentRun, Nat.fold_succ, TimeM.ret_bind] using
        parentStep_invariant graph source (parentRun graph fuel state).ret ih

private lemma parentFinal_invariant {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (graph : DirectedAdjacency V) (source : V) :
    ParentInvariant graph source
      (parentRun graph graph.vertices.length (parentInitial source).ret).ret :=
  parentRun_invariant graph source graph.vertices.length (parentInitial source).ret
    (parentInitial_invariant graph source)

private lemma parentEntries_insert {V : Type u} [BEq V] [Hashable V]
    (state : ParentState V) (parent vertex : V) (distance : Nat) :
    parentEntries
      ⟨(state.core.1, (state.core.2.1.enqueue (vertex, distance + 1),
          state.core.2.2.insert vertex (distance + 1))), state.parents.insert vertex parent⟩ =
      parentEntries state ++ [(vertex, distance + 1)] := by
  simp [parentEntries, List.append_assoc]

private lemma scanParents_time_potential {V : Type u} [BEq V] [Hashable V]
    (parent : V) (distance : Nat) (neighbors : List V) (state : ParentState V) :
    (scanParents parent distance neighbors state).time + 2 * (parentEntries state).length =
      neighbors.length +
        2 * (parentEntries (scanParents parent distance neighbors state).ret).length := by
  induction neighbors generalizing state with
  | nil => simp [scanParents]
  | cons vertex neighbors ih =>
      cases h : state.core.2.2.contains vertex with
      | false =>
          have tail := ih
            ⟨(state.core.1, (state.core.2.1.enqueue (vertex, distance + 1),
              state.core.2.2.insert vertex (distance + 1))), state.parents.insert vertex parent⟩
          simp only [parentEntries_insert, List.length_append, List.length_singleton] at tail
          simp only [scanParents, TimeM.ret_bind, TimeM.time_bind, TimeM.time_tick,
            h, Bool.false_eq_true, ↓reduceIte, List.length_cons]
          omega
      | true =>
          have tail := ih state
          simp only [scanParents, TimeM.ret_bind, TimeM.time_bind, TimeM.time_tick,
            h, ↓reduceIte, List.length_cons]
          omega


private lemma scanParents_ret_order {V : Type u} [BEq V] [Hashable V]
    (parent : V) (distance : Nat) (neighbors : List V) (state : ParentState V) :
    (scanParents parent distance neighbors state).ret.core.1 = state.core.1 := by
  induction neighbors generalizing state with
  | nil => rfl
  | cons vertex neighbors ih =>
      cases h : state.core.2.2.contains vertex <;>
        simp only [scanParents, TimeM.ret_bind, h, Bool.false_eq_true, ↓reduceIte, ih]

private lemma parentStep_time_potential {V : Type u} [BEq V] [Hashable V]
    (graph : DirectedAdjacency V) (state : ParentState V) :
    (parentStep graph state).time + 2 * (parentEntries state).length +
        (state.core.1.map fun entry => (graph.adjacency entry.1).length).sum =
      1 + 2 * (parentEntries (parentStep graph state).ret).length +
        ((parentStep graph state).ret.core.1.map
          fun entry => (graph.adjacency entry.1).length).sum := by
  cases h : state.core.2.1.dequeue? with
  | none => simp [parentStep, h]
  | some next =>
      rcases next with ⟨entry, queue⟩
      have potential := scanParents_time_potential entry.1 entry.2
        (graph.adjacency entry.1)
        ⟨(entry :: state.core.1, (queue, state.core.2.2)), state.parents⟩
      simp only [parentEntries_dequeue state entry queue h] at potential
      simp only [parentStep, TimeM.ret_bind, TimeM.time_bind, TimeM.time_tick, h,
        scanParents_ret_order, List.map_cons, List.sum_cons]
      omega


private lemma parentRun_time_potential {V : Type u} [BEq V] [Hashable V]
    (graph : DirectedAdjacency V) (fuel : Nat) (state : ParentState V) :
    (parentRun graph fuel state).time + 2 * (parentEntries state).length +
        (state.core.1.map fun entry => (graph.adjacency entry.1).length).sum =
      fuel + 2 * (parentEntries (parentRun graph fuel state).ret).length +
        ((parentRun graph fuel state).ret.core.1.map
          fun entry => (graph.adjacency entry.1).length).sum := by
  induction fuel with
  | zero => simp [parentRun, Nat.fold_zero]
  | succ fuel ih =>
      have step := parentStep_time_potential graph (parentRun graph fuel state).ret
      simp only [parentRun, Nat.fold_succ, TimeM.ret_bind, TimeM.time_bind] at *
      omega


private lemma parentRun_processed_length_of_queue_nonempty
    {V : Type u} [BEq V] [Hashable V]
    (graph : DirectedAdjacency V) (fuel : Nat) (state : ParentState V)
    (nonempty : (parentRun graph fuel state).ret.core.2.1.dequeue? ≠ none) :
    state.core.1.length + fuel ≤ (parentRun graph fuel state).ret.core.1.length := by
  induction fuel with
  | zero => simp [parentRun, Nat.fold_zero]
  | succ fuel ih =>
      let previous := (parentRun graph fuel state).ret
      have run_succ :
          (parentRun graph (fuel + 1) state).ret = (parentStep graph previous).ret := by
        simp only [parentRun, Nat.fold_succ, TimeM.ret_bind, previous]
      rw [run_succ] at nonempty ⊢
      cases h : previous.core.2.1.dequeue? with
      | none =>
          simp only [parentStep, TimeM.ret_bind, TimeM.ret_pure, h] at nonempty
          exact False.elim (nonempty rfl)
      | some next =>
          rcases next with ⟨entry, queue⟩
          have previous_nonempty : previous.core.2.1.dequeue? ≠ none := by simp [h]
          have bound := ih previous_nonempty
          simp only [parentStep, TimeM.ret_bind, h, scanParents_ret_order, List.length_cons]
          change state.core.1.length + (fuel + 1) ≤ previous.core.1.length + 1
          change state.core.1.length + fuel ≤ previous.core.1.length at bound
          omega


private lemma parentInvariant_steps {V : Type u} [BEq V] [Hashable V]
    (graph : DirectedAdjacency V) (source : V) (state : ParentState V)
    (invariant : ParentInvariant graph source state) (vertex : V) (distance : Nat)
    (found : state.core.2.2[vertex]? = some distance) :
    Relation.RelatesInSteps (fun parent vertex => state.parents[vertex]? = some parent)
      source vertex distance := by
  induction distance generalizing vertex with
  | zero =>
      cases h : state.parents[vertex]? with
      | none =>
          rcases (invariant.parent_none vertex).mp h with root | absent
          · subst vertex
            exact .refl source
          · rw [found] at absent
            contradiction
      | some parent =>
          obtain ⟨parentDistance, _, childDistance⟩ :=
            invariant.parent_distance vertex parent h
          have impossible := found.symm.trans childDistance
          simp only [Option.some.injEq] at impossible
          omega
  | succ distance ih =>
      cases h : state.parents[vertex]? with
      | none =>
          rcases (invariant.parent_none vertex).mp h with root | absent
          · subst vertex
            rw [invariant.source_zero] at found
            simp only [Option.some.injEq] at found
            omega
          · rw [found] at absent
            contradiction
      | some parent =>
          obtain ⟨parentDistance, parentFound, childDistance⟩ :=
            invariant.parent_distance vertex parent h
          have sameDistance := found.symm.trans childDistance
          simp only [Option.some.injEq] at sameDistance
          have eqDistance : parentDistance = distance := by omega
          subst parentDistance
          exact .tail source parent vertex distance (ih parent parentFound) h


private lemma parentRun_queue_empty {V : Type u} [BEq V] [Hashable V]
    (graph : DirectedAdjacency V) (source : V) (fuel : Nat) (state : ParentState V)
    (scheduled : graph.vertices.length ≤ state.core.1.length + fuel)
    (invariant : ParentInvariant graph source (parentRun graph fuel state).ret) :
    (parentRun graph fuel state).ret.core.2.1.dequeue? = none := by
  by_contra nonempty
  have processed := parentRun_processed_length_of_queue_nonempty graph fuel state nonempty
  have entries_bound :
      (parentEntries (parentRun graph fuel state).ret).length ≤ graph.vertices.length := by
    simpa only [List.length_map] using
      invariant.nodup.length_le_of_subset
        (fun vertex _ => graph.vertices_complete vertex)
  have queue_positive :
      0 < (Queue.contents (parentRun graph fuel state).ret.core.2.1).length := by
    apply List.length_pos_iff.mpr
    intro empty
    exact nonempty ((Queue.dequeue?_eq_none_iff _).mpr empty)
  simp only [parentEntries, List.length_append, List.length_reverse] at entries_bound
  omega


private lemma parentInvariant_steps_distance {V : Type u} [BEq V] [Hashable V]
    (graph : DirectedAdjacency V) (source : V) (state : ParentState V)
    (invariant : ParentInvariant graph source state) (start vertex : V)
    (length distance : Nat)
    (steps : Relation.RelatesInSteps
      (fun parent vertex => state.parents[vertex]? = some parent) start vertex length)
    (found : state.core.2.2[start]? = some distance) :
    state.core.2.2[vertex]? = some (distance + length) := by
  induction steps with
  | refl => simpa using found
  | tail parent vertex length _ edge ih =>
      obtain ⟨parentDistance, parentFound, childFound⟩ :=
        invariant.parent_distance vertex parent edge
      have sameDistance := parentFound.symm.trans ih
      simp only [Option.some.injEq] at sameDistance
      simpa only [sameDistance, Nat.add_assoc] using childFound


private lemma scanParents_ret_predecessor {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (parent : V) (distance : Nat) (neighbors : List V) (state : ParentState V)
    (target : V) :
    (scanParents parent distance neighbors state).ret.parents[target]? =
      if state.core.2.2.contains target then state.parents[target]?
      else if target ∈ neighbors then some parent else state.parents[target]? := by
  induction neighbors generalizing state with
  | nil => simp [scanParents]
  | cons vertex neighbors ih =>
      cases h : state.core.2.2.contains vertex with
      | false =>
          simp only [scanParents, TimeM.ret_bind, h, Bool.false_eq_true, ↓reduceIte]
          rw [ih]
          by_cases same : vertex = target
          · subst vertex
            simp [h]
          · have opposite : target ≠ vertex := Ne.symm same
            simp [Std.HashMap.contains_insert, Std.HashMap.getElem?_insert, same, opposite]
      | true =>
          simp only [scanParents, TimeM.ret_bind, h, ↓reduceIte]
          rw [ih]
          by_cases same : vertex = target
          · subst vertex
            simp [h]
          · have opposite : target ≠ vertex := Ne.symm same
            simp [opposite]


private lemma parentStep_predecessor_eq_find? {V : Type u} [BEq V] [Hashable V]
    [LawfulBEq V] (graph : DirectedAdjacency V) (source : V) (state : ParentState V)
    (invariant : ParentInvariant graph source state)
    (first : ∀ target : V, target ≠ source →
      state.parents[target]? =
        (state.core.1.reverse.map Prod.fst).find?
          (fun parent => (graph.adjacency parent).contains target))
    (target : V) (nonsource : target ≠ source) :
    (parentStep graph state).ret.parents[target]? =
      ((parentStep graph state).ret.core.1.reverse.map Prod.fst).find?
        (fun parent => (graph.adjacency parent).contains target) := by
  cases h : state.core.2.1.dequeue? with
  | none => simpa [parentStep, h] using first target nonsource
  | some next =>
      rcases next with ⟨entry, queue⟩
      simp only [parentStep, TimeM.ret_bind, h, scanParents_ret_order,
        List.reverse_cons, List.map_append, List.map_singleton, List.find?_append,
        scanParents_ret_predecessor]
      rw [← first target nonsource]
      cases contains : state.core.2.2.contains target with
      | false =>
          have absent : state.core.2.2[target]? = none :=
            Std.HashMap.getElem?_eq_none_of_contains_eq_false contains
          have parentNone := (invariant.parent_none target).mpr (Or.inr absent)
          simp [parentNone]
      | true =>
          cases parentFound : state.parents[target]? with
          | none =>
              have absent :=
                ((invariant.parent_none target).mp parentFound).resolve_left nonsource
              rw [Std.HashMap.contains_eq_isSome_getElem?, absent] at contains
              contradiction
          | some parent => simp


private lemma parentRun_predecessor_eq_find? {V : Type u} [BEq V] [Hashable V]
    [LawfulBEq V] (graph : DirectedAdjacency V) (source : V) (state : ParentState V)
    (fuel : Nat)
    (invariants : ∀ count : Nat, count ≤ fuel →
      ParentInvariant graph source (parentRun graph count state).ret)
    (first : ∀ target : V, target ≠ source →
      state.parents[target]? =
        (state.core.1.reverse.map Prod.fst).find?
          (fun parent => (graph.adjacency parent).contains target)) :
    ∀ target : V, target ≠ source →
      (parentRun graph fuel state).ret.parents[target]? =
        ((parentRun graph fuel state).ret.core.1.reverse.map Prod.fst).find?
          (fun parent => (graph.adjacency parent).contains target) := by
  induction fuel with
  | zero =>
      intro target nonsource
      simpa only [parentRun, Nat.fold_zero, TimeM.ret_pure] using first target nonsource
  | succ fuel ih =>
      intro target nonsource
      have prior : ∀ count : Nat, count ≤ fuel →
          ParentInvariant graph source (parentRun graph count state).ret := by
        intro count bound
        exact invariants count (by omega)
      simpa only [parentRun, Nat.fold_succ, TimeM.ret_bind] using
        parentStep_predecessor_eq_find? graph source (parentRun graph fuel state).ret
          (invariants fuel (by omega)) (ih prior) target nonsource

private lemma followParents_none {V : Type u} [BEq V] [LawfulBEq V]
    (predecessor : V → Option V) (source target : V) (fuel : Nat)
    (positive : 0 < fuel) (nonsource : target ≠ source)
    (missing : predecessor target = none) :
    followParents predecessor source fuel target [] = ⟨none, 2⟩ := by
  cases fuel with
  | zero => omega
  | succ fuel =>
      apply TimeM.ext <;> simp [followParents, nonsource, missing]

private lemma followParents_source {V : Type u} [BEq V] [ReflBEq V]
    (predecessor : V → Option V) (source : V) (fuel : Nat) (suffix : List V) :
    followParents predecessor source fuel source suffix = ⟨some (source :: suffix), 2⟩ := by
  cases fuel <;> apply TimeM.ext <;> simp [followParents]

private lemma parentInvariant_follow {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (graph : DirectedAdjacency V) (source : V) (state : ParentState V)
    (invariant : ParentInvariant graph source state) (vertex : V) (distance : Nat)
    (found : state.core.2.2[vertex]? = some distance) (fuel : Nat)
    (enough : distance ≤ fuel) (suffix : List V) :
    ∃ path : List V,
      path.IsChainFromTo (fun parent vertex => state.parents[vertex]? = some parent)
        source vertex ∧ path.length = distance + 1 ∧
      followParents (fun vertex => state.parents[vertex]?) source fuel vertex suffix =
        ⟨some (path ++ suffix), 3 * distance + 2⟩ := by
  induction distance generalizing vertex fuel suffix with
  | zero =>
      have root := (parentInvariant_steps graph source state invariant vertex 0 found).zero
      subst vertex
      refine ⟨[source], List.isChainFromTo_singleton, by simp, ?_⟩
      simpa using followParents_source (fun vertex => state.parents[vertex]?)
        source fuel suffix
  | succ distance ih =>
      have nonsource : vertex ≠ source := by
        intro root
        subst vertex
        rw [invariant.source_zero] at found
        simp only [Option.some.injEq] at found
        omega
      cases h : state.parents[vertex]? with
      | none =>
          rcases (invariant.parent_none vertex).mp h with root | absent
          · exact False.elim (nonsource root)
          · rw [found] at absent
            contradiction
      | some parent =>
          obtain ⟨parentDistance, parentFound, childFound⟩ :=
            invariant.parent_distance vertex parent h
          have sameDistance := found.symm.trans childFound
          simp only [Option.some.injEq] at sameDistance
          have eqDistance : parentDistance = distance := by omega
          subst parentDistance
          cases fuel with
          | zero => omega
          | succ fuel =>
              obtain ⟨initialPath, initialPathLinked, initialPathLength, recursive⟩ :=
                ih parent parentFound fuel (by omega) (vertex :: suffix)
              refine ⟨initialPath ++ [vertex], initialPathLinked.snoc h,
                by simp [initialPathLength], ?_⟩
              apply TimeM.ext
              · simp [followParents, nonsource, h, recursive, List.append_assoc]
              · simp [followParents, nonsource, h, recursive, Nat.mul_add, Nat.add_assoc]
                omega


private lemma scanParents_ret_core {V : Type u} [BEq V] [Hashable V]
    (parent : V) (distance : Nat) (neighbors : List V) (state : ParentState V) :
    (scanParents parent distance neighbors state).ret.core =
      neighbors.foldl (fun core vertex =>
        if core.2.2.contains vertex then core
        else (core.1, (core.2.1.enqueue (vertex, distance + 1),
          core.2.2.insert vertex (distance + 1)))) state.core := by
  induction neighbors generalizing state with
  | nil => rfl
  | cons vertex neighbors ih =>
      cases h : state.core.2.2.contains vertex <;>
        simp only [scanParents, TimeM.ret_bind,
          List.foldl_cons, h, Bool.false_eq_true, ↓reduceIte, ih]

private lemma parentStep_ret_core {V : Type u} [BEq V] [Hashable V]
    (graph : DirectedAdjacency V) (state : ParentState V) :
    (parentStep graph state).ret.core = coreStep graph state.core := by
  cases h : state.core.2.1.dequeue? with
  | none => simp only [parentStep, coreStep, TimeM.ret_bind, TimeM.ret_pure, h]
  | some next =>
      rcases next with ⟨entry, queue⟩
      simp only [parentStep, coreStep, TimeM.ret_bind, h, scanParents_ret_core]

private lemma parentRun_ret_core {V : Type u} [BEq V] [Hashable V]
    (graph : DirectedAdjacency V) (fuel : Nat) (state : ParentState V) :
    (parentRun graph fuel state).ret.core =
      Nat.fold fuel (fun _ _ => coreStep graph) state.core := by
  induction fuel with
  | zero => simp only [parentRun, Nat.fold_zero, TimeM.ret_pure]
  | succ fuel ih =>
      simpa only [parentRun, Nat.fold_succ, TimeM.ret_bind, parentStep_ret_core]
        using congrArg (coreStep graph) ih


end

end Cslib.Algorithms.Lean.BreadthFirstSearch
