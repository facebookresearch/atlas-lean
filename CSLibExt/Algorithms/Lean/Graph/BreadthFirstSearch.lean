/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.DirectedAdjacency
public import CSLibExt.Algorithms.Lean.DataStructures.Queue.Semantics

import Mathlib.Data.List.Sort
import Std.Data.HashMap.Lemmas

/-!
# Executable breadth-first search on ordered finite directed graphs

This file implements `CLASSIC-CS-BFS-CONTRACT-v1`.

Forward clause map: `DirectedAdjacency V` certifies a finite duplicate-free
vertex enumeration and supplies ordered adjacency lists. `DirectedAdjacency.Walk`
is CSLib's canonical exact-step relation over adjacency-list edge membership, and
`DirectedAdjacency.Reachable` is its reflexive-transitive closure.
`bfs` uses a `Std.Queue` worklist and a `Std.HashMap` for discovered vertices and
distances. Neighbors are examined left-to-right, marked immediately, and enqueued
once. Processed entries are consed to a reversed list and reversed once at the end.
Thus the executable traversal performs expected
`O(V + ∑ v, (g.adjacency v).length)` work under the standard hash-map cost
model: adjacency lists may contain repeated entries (the semantic `Edge`
relation collapses duplicates via list membership), and every list entry is
scanned, so the bound is measured against total adjacency-list length rather
than the number of distinct semantic edges. `BFSResult.distance` counts edges
and `BFSResult.order` is the resulting first-discovery order.

Reverse clause map: `distance_present_iff_reachable` and
`order_mem_iff_reachable` characterize the two observable outputs;
`order_nodup` proves immediate marking prevents repeated discovery;
`distance_eq_some_iff_shortest` states exact-walk existence and minimality;
`source_distance` fixes the zero-edge convention; and
`order_distances_nondecreasing` is the FIFO layer-order theorem.  The importing
tests check the empty representation, duplicate/self edges, cycles,
disconnection, left-to-right adjacency order, and a graph that distinguishes
FIFO BFS from depth-first search.

Thus adjacency is directed, neighbor order affects only first-discovery order,
and shortest distance is the minimum number of edges. Empty vertex types allow
a graph value but no BFS source.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

universe u

open DirectedAdjacency

namespace BreadthFirstSearch

variable {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]

private abbrev Entry (V : Type u) := V × Nat

private abbrev State (V : Type u) [BEq V] [Hashable V] :=
  List (Entry V) × (Std.Queue (Entry V) × Std.HashMap V Nat)

private abbrev State.orderRev (st : State V) : List (Entry V) :=
  st.1

private abbrev State.queue (st : State V) : Std.Queue (Entry V) :=
  st.2.1

private abbrev State.distances (st : State V) : Std.HashMap V Nat :=
  st.2.2

omit [LawfulBEq V] in
@[simp] private theorem State.orderRev_tuple (order : List (Entry V))
    (queue : Std.Queue (Entry V)) (distances : Std.HashMap V Nat) :
    State.orderRev (order, (queue, distances)) = order := rfl

omit [LawfulBEq V] in
@[simp] private theorem State.queue_tuple (order : List (Entry V))
    (queue : Std.Queue (Entry V)) (distances : Std.HashMap V Nat) :
    State.queue (order, (queue, distances)) = queue := rfl

omit [LawfulBEq V] in
@[simp] private theorem State.distances_tuple (order : List (Entry V))
    (queue : Std.Queue (Entry V)) (distances : Std.HashMap V Nat) :
    State.distances (order, (queue, distances)) = distances := rfl

private def State.entries (st : State V) : List (Entry V) :=
  st.orderRev.reverse ++ Queue.contents st.queue

private def State.vertices (st : State V) : List (V) :=
  st.entries.map Prod.fst

private def State.enqueue (st : State V) (v : V) (d : Nat) : State V :=
  (st.orderRev, (st.queue.enqueue (v, d), st.distances.insert v d))

omit [LawfulBEq V] in
@[simp] private theorem State.entries_enqueue (st : State V) (v : V) (d : Nat) :
    (st.enqueue v d).entries = st.entries ++ [(v, d)] := by
  simp [State.enqueue, State.entries, List.append_assoc]

omit [LawfulBEq V] in
@[simp] private theorem State.vertices_enqueue (st : State V) (v : V) (d : Nat) :
    (st.enqueue v d).vertices = st.vertices ++ [v] := by
  simp [State.vertices]

private def fresh (seen : List (V)) : List (V) → List (V)
  | [] => []
  | v :: rest =>
      if v ∈ seen then fresh seen rest else v :: fresh (seen ++ [v]) rest

omit [Hashable V] in
private theorem fresh_append_nodup {seen neighbors : List (V)}
    (h : seen.Nodup) : (seen ++ fresh seen neighbors).Nodup := by
  induction neighbors generalizing seen with
  | nil => simpa [fresh] using h
  | cons v rest ih =>
      by_cases hv : v ∈ seen
      · simpa [fresh, hv] using ih h
      · simp only [fresh, hv, ↓reduceIte]
        have hs : (seen ++ [v]).Nodup := by
          simpa only [List.concat_eq_append] using h.concat hv
        have hi := ih (seen := seen ++ [v]) hs
        simpa [List.append_assoc] using hi

omit [Hashable V] in
private theorem mem_seen_append_fresh {seen neighbors : List (V)}
    {v : V} (hv : v ∈ neighbors) : v ∈ seen ++ fresh seen neighbors := by
  induction neighbors generalizing seen with
  | nil => simp at hv
  | cons u rest ih =>
      simp only [List.mem_cons] at hv
      by_cases hu : u ∈ seen
      · simp only [fresh, hu, ↓reduceIte]
        rcases hv with rfl | hv
        · simp [hu]
        · exact ih hv
      · simp only [fresh, hu, ↓reduceIte]
        rcases hv with rfl | hv
        · simp
        · have hi := ih (seen := seen ++ [u]) hv
          simpa [List.append_assoc] using hi

omit [Hashable V] in
private theorem fresh_mem_neighbors {seen neighbors : List (V)}
    {v : V} (hv : v ∈ fresh seen neighbors) : v ∈ neighbors := by
  induction neighbors generalizing seen with
  | nil => simp [fresh] at hv
  | cons u rest ih =>
      by_cases hu : u ∈ seen
      · simp only [fresh, hu, ↓reduceIte] at hv
        exact List.mem_cons_of_mem _ (ih hv)
      · simp only [fresh, hu, ↓reduceIte, List.mem_cons] at hv
        rcases hv with rfl | hv
        · simp
        · exact List.mem_cons_of_mem _ (ih hv)

omit [Hashable V] in
private theorem fresh_not_mem_seen {seen neighbors : List (V)}
    {v : V} (hv : v ∈ fresh seen neighbors) : v ∉ seen := by
  induction neighbors generalizing seen with
  | nil => simp [fresh] at hv
  | cons u rest ih =>
      by_cases hu : u ∈ seen
      · simp only [fresh, hu, ↓reduceIte] at hv
        exact ih hv
      · simp only [fresh, hu, ↓reduceIte, List.mem_cons] at hv
        rcases hv with rfl | hv
        · exact hu
        · exact fun h => ih hv (by simp [h])

private def MapMatches (st : State V) : Prop :=
  ∀ v d, st.distances[v]? = some d ↔ (v, d) ∈ st.entries

private theorem contains_eq_true_iff_mem_vertices {st : State V}
    (hm : MapMatches st) (v : V) :
    st.distances.contains v = true ↔ v ∈ st.vertices := by
  rw [Std.HashMap.contains_eq_isSome_getElem?]
  constructor
  · intro h
    cases hget : st.distances[v]? with
    | none => simp [hget] at h
    | some d =>
        exact List.mem_map_of_mem ((hm v d).mp hget)
  · intro h
    rcases List.mem_map.mp h with ⟨⟨w, d⟩, hw, hv⟩
    simp only at hv
    subst w
    rw [(hm v d).mpr hw]
    rfl

private theorem mapMatches_enqueue {st : State V} (hm : MapMatches st)
    {v : V} {d : Nat} (hv : v ∉ st.vertices) :
    MapMatches (st.enqueue v d) := by
  intro w k
  rw [State.entries_enqueue]
  simp only [State.enqueue, State.distances_tuple]
  rw [Std.HashMap.getElem?_insert]
  by_cases h : v = w
  · subst w
    simp only [beq_self_eq_true, ↓reduceIte, List.mem_append, List.mem_singleton]
    constructor
    · intro hk
      cases hk
      exact Or.inr rfl
    · intro he
      rcases he with he | he
      · exact False.elim (hv (List.mem_map_of_mem he))
      · exact congrArg some (congrArg Prod.snd he).symm
  · have hb : (v == w) = false := by simpa using h
    simp only [hb, List.mem_append, List.mem_singleton]
    constructor
    · intro hk
      exact Or.inl ((hm w k).mp hk)
    · rintro (he | he)
      · exact (hm w k).mpr he
      · exact False.elim (h (congrArg Prod.fst he).symm)

private def scan (neighbors : List (V)) (d : Nat) (st : State V) : State V :=
  neighbors.foldl (fun state v =>
    if state.distances.contains v then state else state.enqueue v (d + 1)) st

omit [LawfulBEq V] in
private theorem scan_orderRev (neighbors : List (V)) (d : Nat) (st : State V) :
    (scan neighbors d st).orderRev = st.orderRev := by
  induction neighbors generalizing st with
  | nil => rfl
  | cons v rest ih =>
      simp only [scan, List.foldl_cons]
      by_cases hb : st.distances.contains v = true
      · simp only [hb, ↓reduceIte]
        simpa only [scan] using ih st
      · simp only [hb, Bool.false_eq_true, ↓reduceIte]
        simpa only [scan, State.enqueue, State.orderRev_tuple] using
          ih (st.enqueue v (d + 1))

private theorem scan_mapMatches (neighbors : List (V)) (d : Nat) (st : State V)
    (hm : MapMatches st) : MapMatches (scan neighbors d st) := by
  induction neighbors generalizing st with
  | nil => exact hm
  | cons v rest ih =>
      by_cases hb : st.distances.contains v = true
      · rw [scan, List.foldl_cons]
        simp only [hb, ↓reduceIte]
        rw [← scan]
        exact ih st hm
      · have hv : v ∉ st.vertices := by
          intro hv
          exact hb ((contains_eq_true_iff_mem_vertices hm v).mpr hv)
        rw [scan, List.foldl_cons]
        simp only [hb]
        rw [← scan]
        exact ih (st.enqueue v (d + 1)) (mapMatches_enqueue hm hv)

private theorem scan_queueContents (neighbors : List (V)) (d : Nat) (st : State V)
    (hm : MapMatches st) :
    Queue.contents (scan neighbors d st).queue =
      Queue.contents st.queue ++ (fresh st.vertices neighbors).map (fun v => (v, d + 1)) := by
  induction neighbors generalizing st with
  | nil => simp [scan, fresh]
  | cons v rest ih =>
      by_cases hb : st.distances.contains v = true
      · have hv : v ∈ st.vertices := (contains_eq_true_iff_mem_vertices hm v).mp hb
        rw [scan, List.foldl_cons]
        simp only [hb, ite_true]
        rw [← scan, ih st hm]
        simp [fresh, hv]
      · have hv : v ∉ st.vertices := by
          intro hv
          exact hb ((contains_eq_true_iff_mem_vertices hm v).mpr hv)
        rw [scan, List.foldl_cons]
        simp only [hb, Bool.false_eq_true, ↓reduceIte]
        rw [← scan,
          ih (st.enqueue v (d + 1)) (mapMatches_enqueue hm hv), State.vertices_enqueue]
        simp [fresh, hv, State.enqueue]

private theorem scan_entries (neighbors : List (V)) (d : Nat) (st : State V)
    (hm : MapMatches st) :
    (scan neighbors d st).entries =
      st.entries ++ (fresh st.vertices neighbors).map (fun v => (v, d + 1)) := by
  simp [State.entries, scan_orderRev, scan_queueContents neighbors d st hm,
    List.append_assoc]

private theorem scan_vertices (neighbors : List (V)) (d : Nat) (st : State V)
    (hm : MapMatches st) :
    (scan neighbors d st).vertices = st.vertices ++ fresh st.vertices neighbors := by
  simp [State.vertices, scan_entries neighbors d st hm, Function.comp_def]

private def advance (g : DirectedAdjacency V) (st : State V) : Option (State V) :=
  match st.queue.dequeue? with
  | none => none
  | some (e, q) =>
      let moved : State V := (e :: st.orderRev, (q, st.distances))
      some (scan (g.adjacency e.1) e.2 moved)

private def step (g : DirectedAdjacency V) (st : State V) : State V :=
  match st.queue.dequeue? with
  | none => st
  | some (e, q) =>
      scan (g.adjacency e.1) e.2 (e :: st.orderRev, (q, st.distances))

omit [LawfulBEq V] in
private theorem step_eq (g : DirectedAdjacency V) (st : State V) :
    step g st = (advance g st).getD st := by
  unfold step advance
  split <;> rfl

private def run (g : DirectedAdjacency V) (fuel : Nat) (st : State V) : State V :=
  Nat.fold fuel (fun _ _ state => step g state) st

private abbrev ModelState (V : Type u) := List (Entry V) × List (Entry V)

private abbrev ModelState.orderRev (st : ModelState V) : List (Entry V) :=
  st.1

private abbrev ModelState.queue (st : ModelState V) : List (Entry V) :=
  st.2

private def ModelState.entries (st : ModelState V) : List (Entry V) :=
  st.orderRev.reverse ++ st.queue

private def modelScan (neighbors : List V) (d : Nat) (st : ModelState V) : ModelState V :=
  neighbors.foldl (fun state vertex =>
    if (state.entries.map Prod.fst).contains vertex then state
    else (state.orderRev, state.queue ++ [(vertex, d + 1)])) st

omit [Hashable V] in
private theorem modelScan_orderRev (neighbors : List V) (d : Nat) (st : ModelState V) :
    (modelScan neighbors d st).orderRev = st.orderRev := by
  induction neighbors generalizing st with
  | nil => rfl
  | cons vertex rest ih =>
      rw [modelScan, List.foldl_cons]
      by_cases hv : vertex ∈ st.entries.map Prod.fst
      · have hb : (st.entries.map Prod.fst).contains vertex = true :=
          List.contains_iff_mem.mpr hv
        simp only [hb, ↓reduceIte]
        simpa only [modelScan] using ih st
      · have hb : (st.entries.map Prod.fst).contains vertex = false := by
          cases hcontains : (st.entries.map Prod.fst).contains vertex with
          | false => rfl
          | true => exact False.elim (hv (List.contains_iff_mem.mp hcontains))
        simp only [hb, Bool.false_eq_true, ↓reduceIte]
        simpa only [modelScan] using
          ih (st.orderRev, st.queue ++ [(vertex, d + 1)])

omit [Hashable V] in
private theorem modelScan_queue (neighbors : List V) (d : Nat) (st : ModelState V) :
    (modelScan neighbors d st).queue =
      st.queue ++ (fresh (st.entries.map Prod.fst) neighbors).map
        (fun vertex => (vertex, d + 1)) := by
  induction neighbors generalizing st with
  | nil => simp [modelScan, fresh]
  | cons vertex rest ih =>
      by_cases hv : vertex ∈ st.entries.map Prod.fst
      · have hb : (st.entries.map Prod.fst).contains vertex = true :=
          List.contains_iff_mem.mpr hv
        rw [modelScan, List.foldl_cons]
        simp only [hb, ↓reduceIte]
        rw [← modelScan, ih]
        simp [fresh, hv]
      · have hb : (st.entries.map Prod.fst).contains vertex = false := by
          cases hcontains : (st.entries.map Prod.fst).contains vertex with
          | false => rfl
          | true => exact False.elim (hv (List.contains_iff_mem.mp hcontains))
        rw [modelScan, List.foldl_cons]
        simp only [hb, Bool.false_eq_true, ↓reduceIte]
        let next : ModelState V := (st.orderRev, st.queue ++ [(vertex, d + 1)])
        rw [← modelScan, ih next]
        have hentries : next.entries = st.entries ++ [(vertex, d + 1)] := by
          simp [next, ModelState.entries, List.append_assoc]
        rw [hentries, List.map_append]
        simp only [fresh, hv, ↓reduceIte, List.map_cons, next, ModelState.queue]
        rw [List.append_assoc]
        rfl

private def modelStep (g : DirectedAdjacency V) (st : ModelState V) : ModelState V :=
  match st.queue with
  | [] => st
  | entry :: queue => modelScan (g.adjacency entry.1) entry.2 (entry :: st.orderRev, queue)

private def modelRun (g : DirectedAdjacency V) (fuel : Nat) (st : ModelState V) :
    ModelState V :=
  Nat.fold fuel (fun _ _ state => modelStep g state) st

private def modelInitial (s : V) : ModelState V :=
  ([], [(s, 0)])

omit [Hashable V] [LawfulBEq V] in
private theorem natFold_modelStep_eq_foldr (g : DirectedAdjacency V)
    (vertices : List V) (st : ModelState V) :
    Nat.fold vertices.length (fun _ _ state => modelStep g state) st =
      vertices.foldr (fun _ state => modelStep g state) st := by
  induction vertices with
  | nil => simp
  | cons vertex rest ih =>
      rw [List.length_cons, Nat.fold_succ]
      change modelStep g
        (Nat.fold rest.length (fun _ _ state => modelStep g state) st) = _
      rw [ih]
      simp

private def modelFinal (g : DirectedAdjacency V) (s : V) : ModelState V :=
  g.vertices.foldr (fun _ state => modelStep g state) (modelInitial s)

private def ModelMatches (st : State V) (model : ModelState V) : Prop :=
  st.orderRev = model.orderRev ∧ Queue.contents st.queue = model.queue

omit [LawfulBEq V] in
private theorem ModelMatches.entries {st : State V} {model : ModelState V}
    (matchState : ModelMatches st model) : st.entries = model.entries := by
  rcases matchState with ⟨order, queue⟩
  simp [State.entries, ModelState.entries, order, queue]

private theorem step_modelMatches (g : DirectedAdjacency V) {st : State V}
    {model : ModelState V} (mapMatches : MapMatches st)
    (matchState : ModelMatches st model) :
    ModelMatches (step g st) (modelStep g model) := by
  have entriesMatch := matchState.entries
  rcases matchState with ⟨orderMatch, queueMatch⟩
  cases hmodelQueue : model.queue with
  | nil =>
      have hcontents : Queue.contents st.queue = [] := queueMatch.trans hmodelQueue
      have hdequeue : st.queue.dequeue? = none :=
        (Queue.dequeue?_eq_none_iff st.queue).mpr hcontents
      constructor
      · simp [step, hdequeue, modelStep, hmodelQueue, orderMatch]
      · simp [step, hdequeue, modelStep, hmodelQueue, hcontents]
  | cons entry rest =>
      cases hdequeue : st.queue.dequeue? with
      | none =>
          have hcontents := (Queue.dequeue?_eq_none_iff st.queue).mp hdequeue
          rw [hcontents, hmodelQueue] at queueMatch
          contradiction
      | some result =>
          rcases result with ⟨actual, queue⟩
          have hcontents := Queue.contents_eq_cons_of_dequeue?_eq_some hdequeue
          have hcons : actual :: Queue.contents queue = entry :: rest :=
            hcontents.symm.trans (queueMatch.trans hmodelQueue)
          have hentry : actual = entry := List.cons.inj hcons |>.1
          have hrest : Queue.contents queue = rest := List.cons.inj hcons |>.2
          subst actual
          let moved : State V :=
            (entry :: st.orderRev, (queue, st.distances))
          let modelMoved : ModelState V :=
            (entry :: model.orderRev, rest)
          have movedEntries : moved.entries = st.entries := by
            simp [moved, State.entries, hcontents, List.append_assoc]
          have movedMapMatches : MapMatches moved := by
            intro vertex distance
            simpa [moved, movedEntries] using mapMatches vertex distance
          have movedEntriesMatch : moved.entries = modelMoved.entries := by
            rw [movedEntries, entriesMatch]
            simp only [modelMoved, ModelState.entries, ModelState.orderRev,
              ModelState.queue, List.reverse_cons]
            simp [hmodelQueue, List.append_assoc]
          have movedVerticesMatch : moved.vertices = modelMoved.entries.map Prod.fst := by
            simp [State.vertices, movedEntriesMatch]
          constructor
          · calc
              (step g st).orderRev =
                  (scan (g.adjacency entry.1) entry.2 moved).orderRev := by
                    simp [step, hdequeue, moved]
              _ = moved.orderRev := scan_orderRev _ _ _
              _ = modelMoved.orderRev := by simp [moved, modelMoved, orderMatch]
              _ = (modelScan (g.adjacency entry.1) entry.2 modelMoved).orderRev :=
                (modelScan_orderRev _ _ _).symm
              _ = (modelStep g model).orderRev := by
                simp [modelStep, hmodelQueue, modelMoved]
          · calc
              Queue.contents (step g st).queue =
                  Queue.contents (scan (g.adjacency entry.1) entry.2 moved).queue := by
                    simp [step, hdequeue, moved]
              _ = Queue.contents queue ++
                    (fresh moved.vertices (g.adjacency entry.1)).map
                      (fun vertex => (vertex, entry.2 + 1)) :=
                scan_queueContents _ _ _ movedMapMatches
              _ = rest ++
                    (fresh (modelMoved.entries.map Prod.fst) (g.adjacency entry.1)).map
                      (fun vertex => (vertex, entry.2 + 1)) := by
                rw [hrest, movedVerticesMatch]
              _ = (modelScan (g.adjacency entry.1) entry.2 modelMoved).queue :=
                by simpa only [modelMoved, ModelState.queue] using
                  (modelScan_queue (g.adjacency entry.1) entry.2 modelMoved).symm
              _ = (modelStep g model).queue := by
                simp [modelStep, hmodelQueue, modelMoved]

/-- **Result of breadth-first search.** A breadth-first search result on a vertex type $V$
consists of a distance function, assigning to each vertex either a natural number or none,
and a list of vertices. They are meant to record the shortest distance from the source (none
when the vertex is unreachable) and the vertices in first-discovery order. -/
structure BFSResult (V : Type u) where
  /-- The shortest distance from the source, or `none` when unreachable. -/
  distance : V → Option Nat
  /-- Vertices in first-discovery order. -/
  order : List (V)

/-- **List model of breadth-first search.** Given a finite directed graph $G$ with ordered
adjacency lists and a source vertex $s$, the list model keeps a list of processed pairs and a
queue of pairs $(v, d)$ of a vertex and a distance, starting with no processed pairs and the
queue $[(s, 0)]$. It performs one round per vertex of $G$: if the queue is empty, nothing
changes; otherwise the front pair $(u, d)$ is removed from the queue and recorded as processed,
and then each entry $w$ of the adjacency list of $u$, from left to right, is appended to the
queue as $(w, d + 1)$ unless $w$ already occurs in a processed or queued pair. The reported
distance of a vertex $v$ is the distance in the first pair for $v$ in the list of processed pairs
in processing order followed by the queue, or none if there is no such pair; the reported order
lists the processed vertices in processing order.

The model can be evaluated by kernel reduction, which is used to check concrete results. -/
def bfsModel (g : DirectedAdjacency V) (s : V) : BFSResult V :=
  let initial : List (V × Nat) × List (V × Nat) := ([], [(s, 0)])
  let final := g.vertices.foldr (fun _ state =>
    match state.2 with
    | [] => state
    | entry :: queue =>
        (g.adjacency entry.1).foldl (fun state vertex =>
          if ((state.1.reverse ++ state.2).map Prod.fst).contains vertex then state
          else (state.1, state.2 ++ [(vertex, entry.2 + 1)]))
          (entry :: state.1, queue)) initial
  let entries := final.1.reverse ++ final.2
  { distance := fun v => (entries.find? fun entry => entry.1 == v).map Prod.snd
    order := final.1.reverse.map Prod.fst }

private def QueueLayered (st : State V) : Prop :=
  match Queue.contents st.queue with
  | [] => True
  | first :: _ => ∀ e ∈ Queue.contents st.queue, e.2 ≤ first.2 + 1

private structure Invariant (g : DirectedAdjacency V) (s : V) (st : State V) : Prop where
  nodup : st.vertices.Nodup
  walks : ∀ e ∈ st.entries, Walk g e.2 s e.1
  sorted : (st.entries.map Prod.snd).Pairwise (· ≤ ·)
  layered : QueueLayered st
  closed : ∀ e ∈ st.orderRev, ∀ v ∈ g.adjacency e.1,
    ∃ d, (v, d) ∈ st.entries ∧ d ≤ e.2 + 1
  source : (s, 0) ∈ st.entries
  map_matches : MapMatches st

omit [LawfulBEq V] in
private theorem entries_eq_of_dequeue {st : State V} {e : Entry V}
    {q : Std.Queue (Entry V)} (h : st.queue.dequeue? = some (e, q)) :
    st.entries = st.orderRev.reverse ++ e :: Queue.contents q := by
  simp [State.entries, Queue.contents_eq_cons_of_dequeue?_eq_some h]

omit [LawfulBEq V] in
private theorem entry_distance_le_front_succ {g : DirectedAdjacency V} {s : V}
    {st : State V} (hi : Invariant g s st) {u : V} {d : Nat}
    {q : Std.Queue (Entry V)} (hq : st.queue.dequeue? = some ((u, d), q))
    {e : Entry V} (he : e ∈ st.entries) : e.2 ≤ d + 1 := by
  have hent : st.entries = st.orderRev.reverse ++ (u, d) :: Queue.contents q :=
    entries_eq_of_dequeue hq
  have hsort := hi.sorted
  rw [hent, List.map_append] at hsort
  rw [hent] at he
  simp only [List.map_cons] at hsort
  rcases List.pairwise_append.mp hsort with ⟨_, htail, hcross⟩
  rcases List.pairwise_cons.mp htail with ⟨hfront, _⟩
  rcases List.mem_append.mp he with he | he
  · exact Nat.le_trans (hcross e.2 (List.mem_map_of_mem he) d (by simp)) (Nat.le_succ d)
  · rcases List.mem_cons.mp he with rfl | he
    · exact Nat.le_succ d
    · have hlayer := hi.layered
      unfold QueueLayered at hlayer
      rw [Queue.contents_eq_cons_of_dequeue?_eq_some hq] at hlayer
      exact hlayer e (by simp [he])

omit [LawfulBEq V] in
private theorem front_le_queued {g : DirectedAdjacency V} {s : V}
    {st : State V} (hi : Invariant g s st) {u : V} {d : Nat}
    {q : Std.Queue (Entry V)} (hq : st.queue.dequeue? = some ((u, d), q))
    {e : Entry V} (he : e ∈ Queue.contents q) : d ≤ e.2 := by
  have hent : st.entries = st.orderRev.reverse ++ (u, d) :: Queue.contents q :=
    entries_eq_of_dequeue hq
  have hsort := hi.sorted
  rw [hent, List.map_append] at hsort
  simp only [List.map_cons] at hsort
  have htail := (List.pairwise_append.mp hsort).2.1
  exact (List.pairwise_cons.mp htail).1 e.2 (List.mem_map_of_mem he)

private theorem invariant_step {g : DirectedAdjacency V} {s : V}
    {st : State V} (hi : Invariant g s st) {u : V} {d : Nat}
    {q : Std.Queue (Entry V)} (hq : st.queue.dequeue? = some ((u, d), q)) :
    Invariant g s (scan (g.adjacency u) d
      ((u, d) :: st.orderRev, (q, st.distances))) := by
  let moved : State V := ((u, d) :: st.orderRev, (q, st.distances))
  let out := scan (g.adjacency u) d moved
  have hmovedEntries : moved.entries = st.entries := by
    calc
      moved.entries = st.orderRev.reverse ++ [(u, d)] ++ Queue.contents q := by
        simp [moved, State.entries, List.append_assoc]
      _ = st.orderRev.reverse ++ (u, d) :: Queue.contents q := by simp [List.append_assoc]
      _ = st.entries := (entries_eq_of_dequeue hq).symm
  have hmovedVertices : moved.vertices = st.vertices := by
    simp [State.vertices, hmovedEntries]
  have hmovedMatches : MapMatches moved := by
    intro v dv
    simpa [moved, hmovedEntries] using hi.map_matches v dv
  have houtEntries : out.entries =
      st.entries ++ (fresh st.vertices (g.adjacency u)).map (fun v => (v, d + 1)) := by
    simp [out, scan_entries _ _ _ hmovedMatches, hmovedEntries, hmovedVertices]
  have houtVertices : out.vertices = st.vertices ++ fresh st.vertices (g.adjacency u) := by
    simp [State.vertices, houtEntries, Function.comp_def]
  have hparent : Walk g d s u := by
    apply hi.walks (u, d)
    rw [entries_eq_of_dequeue hq]
    simp
  constructor
  · rw [houtVertices]
    exact fresh_append_nodup hi.nodup
  · intro e he
    rw [houtEntries] at he
    rcases List.mem_append.mp he with he | he
    · exact hi.walks e he
    · rcases List.mem_map.mp he with ⟨v, hv, rfl⟩
      exact Relation.RelatesInSteps.tail _ _ _ _ hparent (fresh_mem_neighbors hv)
  · rw [houtEntries, List.map_append]
    apply List.pairwise_append.mpr
    refine ⟨hi.sorted, ?_, ?_⟩
    · simp [Function.comp_def]
    · intro a ha b hb
      rcases List.mem_map.mp ha with ⟨e, he, rfl⟩
      have hb'' : fresh st.vertices (g.adjacency u) ≠ [] ∧ b = d + 1 := by
        simpa [Function.comp_def] using hb
      have hb' : b = d + 1 := hb''.2
      subst b
      exact entry_distance_le_front_succ hi hq he
  · unfold QueueLayered
    have hqueue : Queue.contents out.queue =
        Queue.contents q ++ (fresh st.vertices (g.adjacency u)).map (fun v => (v, d + 1)) := by
      simp [out, scan_queueContents _ _ _ hmovedMatches, moved, hmovedVertices]
    rw [hqueue]
    cases hwhole : Queue.contents q ++
        (fresh st.vertices (g.adjacency u)).map (fun v => (v, d + 1)) with
    | nil => trivial
    | cons first rest =>
        intro e he
        have heUpper : e.2 ≤ d + 1 := by
          have hem : e ∈ Queue.contents q ∨
              e ∈ (fresh st.vertices (g.adjacency u)).map (fun v => (v, d + 1)) := by
            exact List.mem_append.mp (hwhole ▸ he)
          rcases hem with hem | hem
          · exact entry_distance_le_front_succ hi hq (by
              rw [entries_eq_of_dequeue hq]
              simp [hem])
          · rcases List.mem_map.mp hem with ⟨v, hv, rfl⟩
            exact Nat.le_refl _
        have hfirstLower : d ≤ first.2 := by
          have hfm : first ∈ Queue.contents q ∨
              first ∈ (fresh st.vertices (g.adjacency u)).map (fun v => (v, d + 1)) := by
            apply List.mem_append.mp
            rw [hwhole]
            simp
          rcases hfm with hfm | hfm
          · exact front_le_queued hi hq hfm
          · rcases List.mem_map.mp hfm with ⟨v, hv, rfl⟩
            exact Nat.le_succ d
        omega
  · intro e he v hv
    have hdone : out.orderRev = (u, d) :: st.orderRev := by
      simp [out, scan_orderRev, moved]
    rw [hdone] at he
    rcases List.mem_cons.mp he with he | he
    · have heq : e = (u, d) := he
      subst e
      have hvout : v ∈ out.vertices := by
        rw [houtVertices]
        exact mem_seen_append_fresh hv
      rcases List.mem_map.mp hvout with ⟨e, heout, hev⟩
      have hev' : e.1 = v := by simpa using hev
      rcases e with ⟨w, dw⟩
      simp only at hev'
      subst w
      refine ⟨dw, heout, ?_⟩
      rw [houtEntries] at heout
      rcases List.mem_append.mp heout with heold | hnew
      · exact entry_distance_le_front_succ hi hq heold
      · rcases List.mem_map.mp hnew with ⟨w, hw, hew⟩
        have := congrArg Prod.snd hew
        omega
    · rcases hi.closed e he v hv with ⟨dv, hmem, hle⟩
      exact ⟨dv, houtEntries ▸ List.mem_append_left _ hmem, hle⟩
  · rw [houtEntries]
    exact List.mem_append_left _ hi.source
  · exact scan_mapMatches _ _ _ hmovedMatches

private theorem advance_preserves {g : DirectedAdjacency V} {s : V}
    {st st' : State V} (hi : Invariant g s st) (ha : advance g st = some st') :
    Invariant g s st' := by
  unfold advance at ha
  split at ha
  · contradiction
  · rename_i e q hq
    obtain ⟨u, d⟩ := e
    have hout : scan (g.adjacency u) d
        ((u, d) :: st.orderRev, (q, st.distances)) = st' := by
      simpa using ha
    rw [← hout]
    exact invariant_step hi hq

private theorem run_preserves {g : DirectedAdjacency V} {s : V}
    (fuel : Nat) {st : State V} (hi : Invariant g s st) :
    Invariant g s (run g fuel st) := by
  induction fuel generalizing st with
  | zero => simpa [run] using hi
  | succ fuel ih =>
      rw [run, Nat.fold_succ]
      change Invariant g s (step g (run g fuel st))
      rw [step_eq]
      have hmid : Invariant g s (run g fuel st) := ih hi
      cases ha : advance g (run g fuel st) with
      | none => simpa [ha] using hmid
      | some st' => simpa [ha] using advance_preserves hmid ha

omit [LawfulBEq V] in
private theorem advance_none_queueContents {g : DirectedAdjacency V} {st : State V}
    (ha : advance g st = none) : Queue.contents st.queue = [] := by
  unfold advance at ha
  split at ha
  · rename_i hq
    exact (Queue.dequeue?_eq_none_iff st.queue).mp hq
  · contradiction

omit [LawfulBEq V] in
private theorem advance_some_orderRev_length {g : DirectedAdjacency V} {st st' : State V}
    (ha : advance g st = some st') : st'.orderRev.length = st.orderRev.length + 1 := by
  unfold advance at ha
  split at ha
  · contradiction
  · rename_i e q hq
    obtain ⟨u, d⟩ := e
    have hout : scan (g.adjacency u) d
        ((u, d) :: st.orderRev, (q, st.distances)) = st' := by
      simpa using ha
    rw [← hout, scan_orderRev]
    simp

omit [LawfulBEq V] in
private theorem run_orderRev_length_of_queue_nonempty {g : DirectedAdjacency V}
    (fuel : Nat) (st : State V)
    (hne : Queue.contents (run g fuel st).queue ≠ []) :
    (run g fuel st).orderRev.length = st.orderRev.length + fuel := by
  induction fuel generalizing st with
  | zero => simp [run]
  | succ fuel ih =>
      rw [run, Nat.fold_succ] at hne ⊢
      change Queue.contents (step g (run g fuel st)).queue ≠ [] at hne
      change (step g (run g fuel st)).orderRev.length =
        st.orderRev.length + (fuel + 1)
      rw [step_eq] at hne ⊢
      cases ha : advance g (run g fuel st) with
      | none =>
          have hempty := advance_none_queueContents ha
          exact False.elim (hne (by simpa [ha] using hempty))
      | some st' =>
          have hmid : Queue.contents (run g fuel st).queue ≠ [] := by
            intro hempty
            have hdequeue : (run g fuel st).queue.dequeue? = none :=
              (Queue.dequeue?_eq_none_iff (run g fuel st).queue).mpr hempty
            have : advance g (run g fuel st) = none := by
              unfold advance
              rw [hdequeue]
            rw [ha] at this
            contradiction
          have hlen := ih st hmid
          have hstep := advance_some_orderRev_length ha
          simpa [ha] using (calc
            st'.orderRev.length = (run g fuel st).orderRev.length + 1 := hstep
            _ = st.orderRev.length + (fuel + 1) := by rw [hlen]; omega)

private def initialState (s : V) : State V :=
  ([], ((Std.Queue.empty : Std.Queue (Entry V)).enqueue (s, 0),
    (Std.HashMap.emptyWithCapacity 1).insert s 0))

private theorem initial_invariant (g : DirectedAdjacency V) (s : V) :
    Invariant g s (initialState s) := by
  constructor
  · simp [initialState, State.vertices, State.entries]
  · intro e he
    have he' : e = (s, 0) := by
      simpa [initialState, State.entries] using he
    cases he'
    exact Relation.RelatesInSteps.refl s
  · simp [initialState, State.entries]
  · simp [QueueLayered, initialState]
  · simp [initialState]
  · simp [initialState, State.entries]
  · intro v d
    suffices ((Std.HashMap.emptyWithCapacity 1).insert s 0)[v]? = some d ↔
        (v, d) ∈ [(s, 0)] by
      simpa [initialState, State.entries]
    rw [Std.HashMap.getElem?_insert]
    by_cases h : s = v
    · subst v
      simpa only [beq_self_eq_true, ↓reduceIte, Option.some.injEq,
        List.mem_singleton, Prod.mk.injEq, true_and] using
        (eq_comm : 0 = d ↔ d = 0)
    · have hb : (s == v) = false := by simpa using h
      constructor
      · intro hget
        exfalso
        simp [hb] at hget
      · intro hmem
        have hv : v = s := congrArg Prod.fst (List.mem_singleton.mp hmem)
        exact False.elim (h hv.symm)

private theorem run_modelMatches (g : DirectedAdjacency V) (s : V) (fuel : Nat) :
    ModelMatches (run g fuel (initialState s))
      (modelRun g fuel (modelInitial s)) := by
  induction fuel with
  | zero => simp [run, modelRun, initialState, modelInitial, ModelMatches]
  | succ fuel ih =>
      rw [run, modelRun, Nat.fold_succ, Nat.fold_succ]
      apply step_modelMatches g (run_preserves fuel (initial_invariant g s)).map_matches ih

private def finalState (g : DirectedAdjacency V) (s : V) : State V :=
  run g g.vertices.length (initialState s)

private theorem final_invariant (g : DirectedAdjacency V) (s : V) :
    Invariant g s (finalState g s) :=
  run_preserves g.vertices.length (initial_invariant g s)

private theorem final_modelMatches (g : DirectedAdjacency V) (s : V) :
    ModelMatches (finalState g s) (modelFinal g s) := by
  unfold finalState modelFinal
  rw [← natFold_modelStep_eq_foldr]
  exact run_modelMatches g s g.vertices.length

private theorem nodup_length_le_of_subset {α : Type u} {xs ys : List α}
    (hn : xs.Nodup) (hsub : ∀ x, x ∈ xs → x ∈ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons a rest ih =>
      have ha : a ∈ ys := hsub a (by simp)
      obtain ⟨left, right, rfl⟩ := List.append_of_mem ha
      have hn' := List.nodup_cons.mp hn
      have hrest : ∀ x, x ∈ rest → x ∈ left ++ right := by
        intro x hx
        have hm := hsub x (by simp [hx])
        simp only [List.mem_append, List.mem_cons] at hm ⊢
        rcases hm with hm | rfl | hm
        · exact Or.inl hm
        · exact False.elim (hn'.1 hx)
        · exact Or.inr hm
      have hle := ih hn'.2 hrest
      simp only [List.length_cons, List.length_append] at hle ⊢
      omega

omit [BEq V] [Hashable V] [LawfulBEq V] in
private theorem nodup_length_le_vertices (g : DirectedAdjacency V)
    {xs : List V} (hn : xs.Nodup) : xs.length ≤ g.vertices.length :=
  nodup_length_le_of_subset hn fun vertex _ => g.vertices_complete vertex

private theorem final_queue_empty (g : DirectedAdjacency V) (s : V) :
    Queue.contents (finalState g s).queue = [] := by
  by_contra hne
  have hlen := run_orderRev_length_of_queue_nonempty g.vertices.length (initialState s) hne
  have hcard := nodup_length_le_vertices g (final_invariant g s).nodup
  have hqpos : 0 < (Queue.contents (finalState g s).queue).length := by
    have hz : (Queue.contents (finalState g s).queue).length ≠ 0 := by
      intro hz
      exact hne (List.eq_nil_of_length_eq_zero hz)
    omega
  have hvertices : (finalState g s).vertices.length =
      (finalState g s).orderRev.length +
        (Queue.contents (finalState g s).queue).length := by
    simp [State.vertices, State.entries]
  have hdone : (finalState g s).orderRev.length = g.vertices.length := by
    simpa [finalState, initialState] using hlen
  omega

private theorem final_entries_eq_orderRev (g : DirectedAdjacency V) (s : V) :
    (finalState g s).entries = (finalState g s).orderRev.reverse := by
  simp [State.entries, final_queue_empty]

omit [BEq V] [Hashable V] [LawfulBEq V] in
private theorem entry_distance_unique {es : List (Entry V)}
    (hn : (es.map Prod.fst).Nodup) {v : V} {d₁ d₂ : Nat}
    (h₁ : (v, d₁) ∈ es) (h₂ : (v, d₂) ∈ es) : d₁ = d₂ := by
  induction es with
  | nil => simp at h₁
  | cons e rest ih =>
      have hn' := List.nodup_cons.mp hn
      simp only [List.mem_cons] at h₁ h₂
      rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
      · cases h₁
        cases h₂
        rfl
      · cases h₁
        exfalso
        apply hn'.1
        exact List.mem_map.mpr ⟨(v, d₂), h₂, rfl⟩
      · cases h₂
        exfalso
        apply hn'.1
        exact List.mem_map.mpr ⟨(v, d₁), h₁, rfl⟩
      · exact ih hn'.2 h₁ h₂

private theorem final_entry_iff_reachable (g : DirectedAdjacency V) (s v : V) :
    (∃ d, (v, d) ∈ (finalState g s).entries) ↔ g.Reachable s v := by
  rw [reachable_iff_exists_walk]
  constructor
  · rintro ⟨d, hd⟩
    exact ⟨d, (final_invariant g s).walks (v, d) hd⟩
  · rintro ⟨k, hw⟩
    induction hw with
    | refl => exact ⟨0, (final_invariant g s).source⟩
    | tail u v k hu hedge ih =>
        rcases ih with ⟨du, hdu⟩
        have hdDone : (u, du) ∈ (finalState g s).orderRev := by
          have : (u, du) ∈ (finalState g s).orderRev.reverse := by
            rw [← final_entries_eq_orderRev]
            exact hdu
          simpa using this
        rcases (final_invariant g s).closed (u, du) hdDone v hedge with
          ⟨dv, hdv, hle⟩
        exact ⟨dv, hdv⟩

private theorem final_distance_le_walk (g : DirectedAdjacency V) (s v : V)
    {d k : Nat} (hd : (v, d) ∈ (finalState g s).entries) (hw : Walk g k s v) :
    d ≤ k := by
  induction hw generalizing d with
  | refl =>
      have hz : d = 0 := entry_distance_unique (final_invariant g s).nodup hd
        (final_invariant g s).source
      omega
  | tail u v k hu hedge ih =>
      rcases (final_entry_iff_reachable g s u).2
        (reachable_iff_exists_walk.mpr ⟨k, hu⟩) with ⟨du, hdu⟩
      have hduDone : (u, du) ∈ (finalState g s).orderRev := by
        have : (u, du) ∈ (finalState g s).orderRev.reverse := by
          rw [← final_entries_eq_orderRev]
          exact hdu
        simpa using this
      rcases (final_invariant g s).closed (u, du) hduDone v hedge with
        ⟨dv, hdv, htri⟩
      have hsame : d = dv := entry_distance_unique (final_invariant g s).nodup hd hdv
      have hprev : du ≤ k := ih hdu
      omega

/-- **Breadth-first search.** Given a finite directed graph $G$ with ordered adjacency lists and a
source vertex $s$, breadth-first search keeps a FIFO queue of pairs $(v, d)$ of a vertex and a
distance and a table of discovered vertices with their distances, starting with the queue
$[(s, 0)]$ and $s$ discovered at distance $0$. It performs one round per vertex of $G$: if the
queue is empty, nothing changes; otherwise it dequeues the front pair $(u, d)$, records $u$ as
processed, and scans the adjacency list of $u$ from left to right, enqueueing each entry $w$ that
is not yet discovered as $(w, d + 1)$ and discovering it at distance $d + 1$. The result reports
for each vertex its discovered distance, or none if it was never discovered, and lists the
processed vertices in processing order.

The table is a hash map, so the search runs in expected time linear in the number of vertices
plus the total length of the adjacency lists. -/
def bfs (g : DirectedAdjacency V) (s : V) : BFSResult V :=
  let initial : List (V × Nat) × (Std.Queue (V × Nat) × Std.HashMap V Nat) :=
    ([], ((Std.Queue.empty : Std.Queue (V × Nat)).enqueue (s, 0),
      (Std.HashMap.emptyWithCapacity 1).insert s 0))
  let final := Nat.fold g.vertices.length (fun _ _ state =>
    match state.2.1.dequeue? with
    | none => state
    | some (entry, queue) =>
        (g.adjacency entry.1).foldl (fun state vertex =>
          if state.2.2.contains vertex then state
          else (state.1,
            (state.2.1.enqueue (vertex, entry.2 + 1),
              state.2.2.insert vertex (entry.2 + 1))))
          (entry :: state.1, (queue, state.2.2))) initial
  { distance := fun v => final.2.2[v]?
    order := final.1.reverse.map Prod.fst }

omit [LawfulBEq V] in
private theorem bfs_eq (g : DirectedAdjacency V) (s : V) :
    bfs g s =
      { distance := fun v => (finalState g s).distances[v]?
        order := (finalState g s).orderRev.reverse.map Prod.fst } := by
  unfold bfs finalState run step scan initialState State.enqueue
  rfl

omit [Hashable V] in
private theorem findDistance_eq_some_iff {entries : List (Entry V)}
    (nodup : (entries.map Prod.fst).Nodup) (v : V) (d : Nat) :
    ((entries.find? fun entry => entry.1 == v).map Prod.snd = some d) ↔
      (v, d) ∈ entries := by
  induction entries with
  | nil => simp
  | cons entry rest ih =>
      obtain ⟨entryVertex, entryDistance⟩ := entry
      have nodupParts := List.nodup_cons.mp nodup
      by_cases hvertex : entryVertex = v
      · subst entryVertex
        have hrest : (v, d) ∉ rest := by
          intro member
          apply nodupParts.1
          exact List.mem_map.mpr ⟨(v, d), member, rfl⟩
        simp [List.find?, hrest, eq_comm]
      · have hbeq : (entryVertex == v) = false := by simpa using hvertex
        have hentry : (v, d) ≠ (entryVertex, entryDistance) := by
          intro equal
          exact hvertex (congrArg Prod.fst equal).symm
        simp [List.find?, hbeq, hentry, ih nodupParts.2]

private theorem hashDistance_eq_findDistance (st : State V)
    (mapMatches : MapMatches st) (nodup : st.vertices.Nodup) (v : V) :
    st.distances[v]? = (st.entries.find? fun entry => entry.1 == v).map Prod.snd := by
  cases hget : st.distances[v]? with
  | none =>
      cases hfind : (st.entries.find? fun entry => entry.1 == v).map Prod.snd with
      | none => rfl
      | some d =>
          have member := (findDistance_eq_some_iff nodup v d).mp hfind
          have present := (mapMatches v d).mpr member
          rw [hget] at present
          contradiction
  | some d =>
      have member := (mapMatches v d).mp hget
      exact (findDistance_eq_some_iff nodup v d).mpr member |>.symm

omit [Hashable V] [LawfulBEq V] in
private theorem bfsModel_eq (g : DirectedAdjacency V) (s : V) :
    bfsModel g s =
      { distance := fun v =>
          ((modelFinal g s).entries.find? fun entry => entry.1 == v).map Prod.snd
        order := (modelFinal g s).orderRev.reverse.map Prod.fst } := by
  unfold bfsModel modelFinal modelInitial modelStep modelScan ModelState.entries
  rfl

/-- **The executable BFS agrees with the list model.** For every finite directed graph $G$ with
ordered adjacency lists and every source vertex $s$, the result of the executable breadth-first
search from $s$ equals the result of the list model of breadth-first search from $s$: both
report the same distance (or none) for every vertex and the same first-discovery order. -/
theorem bfs_eq_bfsModel (g : DirectedAdjacency V) (s : V) :
    bfs g s = bfsModel g s := by
  rw [bfs_eq, bfsModel_eq]
  have matchFinal := final_modelMatches g s
  have distanceMatch : (fun v => (finalState g s).distances[v]?) =
      (fun v => ((modelFinal g s).entries.find?
        fun entry => entry.1 == v).map Prod.snd) := by
    funext v
    rw [← matchFinal.entries]
    exact hashDistance_eq_findDistance (finalState g s)
      (final_invariant g s).map_matches (final_invariant g s).nodup v
  have orderMatch : (finalState g s).orderRev.reverse.map Prod.fst =
      (modelFinal g s).orderRev.reverse.map Prod.fst
      := by rw [matchFinal.1]
  rw [distanceMatch, orderMatch]

/-- **Breadth-first search on the vertices $0, \dots, n-1$.** Given a natural number $n$, an
adjacency function assigning to each vertex $i < n$ an ordered list of vertices among
$0, \dots, n-1$, and a source vertex $s < n$, this is the result of breadth-first search from $s$
on the finite directed graph with vertex enumeration $0, 1, \dots, n-1$ and these adjacency
lists. -/
def bfsFin {n : Nat} (adjacency : Fin n → List (Fin n)) (source : Fin n) :
    BFSResult (Fin n) :=
  bfs
    { vertices := List.finRange n
      vertices_nodup := List.nodup_finRange n
      vertices_complete := List.mem_finRange
      adjacency }
    source

omit [LawfulBEq V] in
private theorem attachedDistances_eq {g : DirectedAdjacency V} {s : V}
    (st : State V) (hi : Invariant g s st) :
    (st.entries.map Prod.fst).map (fun v => st.distances[v]?.getD 0) =
      st.entries.map Prod.snd := by
  rw [List.map_map]
  apply List.map_congr_left
  intro e he
  have hget := (hi.map_matches e.1 e.2).mpr he
  simp [hget]

/-- **BFS reports a distance exactly for the reachable vertices.** For every finite directed graph
$G$ with ordered adjacency lists and all vertices $s$ and $v$, breadth-first search from $s$
reports some distance for $v$ (rather than none) if and only if $v$ is reachable from $s$
in $G$. -/
theorem distance_present_iff_reachable (g : DirectedAdjacency V) (s v : V) :
    (∃ d, (bfs g s).distance v = some d) ↔ g.Reachable s v := by
  rw [bfs_eq]
  change (∃ d, (finalState g s).distances[v]? = some d) ↔ g.Reachable s v
  rw [← final_entry_iff_reachable]
  constructor
  · rintro ⟨d, hd⟩
    exact ⟨d, ((final_invariant g s).map_matches v d).mp hd⟩
  · rintro ⟨d, hd⟩
    exact ⟨d, ((final_invariant g s).map_matches v d).mpr hd⟩

/-- **BFS lists exactly the reachable vertices.** For every finite directed graph $G$ with ordered
adjacency lists and all vertices $s$ and $v$, the vertex $v$ occurs in the first-discovery order
of breadth-first search from $s$ if and only if $v$ is reachable from $s$ in $G$. -/
theorem order_mem_iff_reachable (g : DirectedAdjacency V) (s v : V) :
    v ∈ (bfs g s).order ↔ g.Reachable s v := by
  rw [bfs_eq]
  change v ∈ (finalState g s).orderRev.reverse.map Prod.fst ↔ g.Reachable s v
  rw [← final_entries_eq_orderRev]
  rw [← final_entry_iff_reachable]
  constructor
  · intro hv
    rcases List.mem_map.mp hv with ⟨e, he, hev⟩
    exact ⟨e.2, by simpa [← hev] using he⟩
  · rintro ⟨d, hd⟩
    exact List.mem_map_of_mem hd

/-- **BFS discovers each vertex at most once.** For every finite directed graph $G$ with ordered
adjacency lists and every vertex $s$, no vertex occurs twice in the first-discovery order of
breadth-first search from $s$. -/
theorem order_nodup (g : DirectedAdjacency V) (s : V) :
    (bfs g s).order.Nodup := by
  rw [bfs_eq]
  change ((finalState g s).orderRev.reverse.map Prod.fst).Nodup
  rw [← final_entries_eq_orderRev]
  exact (final_invariant g s).nodup

/-- **BFS reports exactly the shortest walk length.** For every finite directed graph $G$ with
ordered adjacency lists, all vertices $s$ and $v$, and every natural number $d$, breadth-first
search from $s$ reports distance $d$ for $v$ if and only if there is a walk of exactly $d$ edges
from $s$ to $v$ in $G$ and $d \le k$ for every natural number $k$ such that there is a walk of
exactly $k$ edges from $s$ to $v$. -/
theorem distance_eq_some_iff_shortest (g : DirectedAdjacency V) (s v : V) (d : Nat) :
    (bfs g s).distance v = some d ↔
      Walk g d s v ∧ ∀ k, Walk g k s v → d ≤ k := by
  rw [bfs_eq]
  change (finalState g s).distances[v]? = some d ↔ _
  constructor
  · intro hd
    have hentry := ((final_invariant g s).map_matches v d).mp hd
    exact ⟨(final_invariant g s).walks (v, d) hentry,
      fun k hw => final_distance_le_walk g s v hentry hw⟩
  · rintro ⟨hwalk, hminimal⟩
    rcases (final_entry_iff_reachable g s v).2
      (reachable_iff_exists_walk.mpr ⟨d, hwalk⟩) with ⟨dv, hdv⟩
    have h₁ : dv ≤ d := final_distance_le_walk g s v hdv hwalk
    have h₂ : d ≤ dv := hminimal dv ((final_invariant g s).walks (v, dv) hdv)
    have : dv = d := Nat.le_antisymm h₁ h₂
    subst dv
    exact ((final_invariant g s).map_matches v d).mpr hdv

/-- **Breadth-first search places the source at distance zero.** For every finite directed graph
$G$ given by ordered adjacency lists and every vertex $s$ of $G$, breadth-first search in $G$
from $s$ reports a distance for $s$ itself, and that distance is $0$ edges. -/
theorem source_distance (g : DirectedAdjacency V) (s : V) :
    (bfs g s).distance s = some 0 := by
  rw [bfs_eq]
  change (finalState g s).distances[s]? = some 0
  exact ((final_invariant g s).map_matches s 0).mpr (final_invariant g s).source

/-- **BFS discovers vertices in nondecreasing distance.** For every finite directed graph $G$ with
ordered adjacency lists and every vertex $s$, the distances reported by breadth-first search
from $s$, listed along its first-discovery order, form a nondecreasing sequence, where a vertex
without a reported distance counts as $0$. -/
theorem order_distances_nondecreasing (g : DirectedAdjacency V) (s : V) :
    (((bfs g s).order.map fun v => (bfs g s).distance v |>.getD 0).Pairwise (· ≤ ·)) := by
  rw [bfs_eq]
  change (((finalState g s).orderRev.reverse.map Prod.fst).map
    (fun v => (finalState g s).distances[v]?.getD 0)).Pairwise (· ≤ ·)
  rw [← final_entries_eq_orderRev, attachedDistances_eq _ (final_invariant g s)]
  exact (final_invariant g s).sorted

end BreadthFirstSearch

end Cslib.Algorithms.Lean
