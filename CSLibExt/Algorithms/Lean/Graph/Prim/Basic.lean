/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.IndexedMinQueue
public import CSLibExt.Algorithms.Lean.Graph.DirectedAdjacency
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Data.Sym.Sym2

/-!
# Prim's indexed-heap executor

Adapted from CLRS, fourth edition, section 21.2, Prim's algorithm.
Proofs and executable code authored with Codex under Adam Kiezun's authorization.
-/

open Cslib.Algorithms.Lean

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe u

@[no_expose] private def queueKey {W : Type u} [LinearOrder W] {n : Nat}
    (q : IndexedMinQueue W n) (v : Fin n) : WithTop W :=
  match h : q.position[v] with
  | none => ⊤
  | some i => (ofLex (q.heap.data[i.val]'(position_valid q v i h))).1

@[no_expose] private def liftHeap {α : Type u} (m : TimeM (Fin 5 → Nat) α) :
    TimeM ((Fin 5 → Nat) × Nat × Nat) α :=
  ⟨m.ret, (m.time, 0, 0)⟩

private structure State (W : Type u) [LinearOrder W] (n : Nat) where
  queue : IndexedMinQueue W n
  parent : Vector (Option (Fin n)) n
  extracted : List (WithTop W × Fin n)

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe upex7

@[no_expose] private def initQueue {W : Type upex7} [LinearOrder W] [Zero W] {n : Nat}
    (root : Fin n) : List (Fin n) → IndexedMinQueue W n →
    TimeM ((Fin 5 → Nat) × Nat × Nat) (IndexedMinQueue W n)
  | [], q => pure q
  | v :: vs, q => do
    let inserted ← liftHeap (insert q v (if v = root then (0 : W) else ⊤))
    match inserted with
    | none => pure q
    | some q' => initQueue root vs q'

@[no_expose] private def scan {W : Type upex7} [LinearOrder W] {n : Nat}
    (weight : Sym2 (Fin n) → W) (current : Fin n) :
    List (Fin n) → State W n → TimeM ((Fin 5 → Nat) × Nat × Nat) (State W n)
  | [], state => pure state
  | v :: vs, state => do
    TimeM.tick ((fun _ : Fin 5 => 0), 1, 0)
    TimeM.bind (liftHeap (Cslib.Algorithms.Lean.IndexedMinQueue.member state.queue v)) fun live =>
    if live = true then do
      TimeM.tick ((fun _ : Fin 5 => 0), 0, 1)
      if (weight (Sym2.mk current v) : WithTop W) < queueKey state.queue v then
        let parent := state.parent.set v (some current)
        let decreased ← liftHeap (decreaseKey state.queue v (weight (Sym2.mk current v)))
        match decreased with
        | none => pure { state with parent := parent }
        | some q' => scan weight current vs { state with queue := q', parent := parent }
      else scan weight current vs state
    else scan weight current vs state

@[no_expose] private def loop {W : Type upex7} [LinearOrder W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W) :
    Nat → State W n → TimeM ((Fin 5 → Nat) × Nat × Nat) (State W n)
  | 0, state => pure state
  | fuel + 1, state => do
    let extracted ← liftHeap (extractMin state.queue)
    match extracted with
    | none => pure state
    | some (entry, q') =>
      let updated ← scan weight (ofLex entry).2 (graph.adjacency (ofLex entry).2)
        { state with queue := q', extracted := ofLex entry :: state.extracted }
      loop graph weight fuel updated

@[no_expose] private def worker {W : Type upex7} [LinearOrder W] [Zero W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W) (root : Fin n) :
    TimeM ((Fin 5 → Nat) × Nat × Nat) (State W n) := do
  let parent := Vector.replicate n (none : Option (Fin n))
  let queue ← initQueue root graph.vertices (empty n)
  loop graph weight n ⟨queue, parent, []⟩

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

universe u

/-- **Prim's algorithm with an indexed binary heap.** Let $W$ be a linearly ordered type with a
zero element, let $W \cup \{\top\}$ be $W$ with a new greatest element $\top$ adjoined, let $D$
be a directed adjacency structure on the vertices $0, \dots, n-1$, with vertex list $L$ and
adjacency lists $A(u)$, let $w$ assign a weight $w(\{u, v\}) \in W$ to every unordered pair
$\{u, v\}$ of vertices, not necessarily distinct, and let $r$ be a vertex. Prim's algorithm
starts with no vertex having a parent and inserts the vertices, in the order of $L$, into an
empty indexed minimum queue over the identities $0, \dots, n-1$, with key $0$ for $r$ and key
$\top$ for every other vertex. It then repeats the following at most $n$ times, stopping early
when the queue is empty: it extracts the entry of minimum key, ties broken by the smaller
vertex, say with vertex $u$, and for each entry $v$ of $A(u)$ in order, if $v$ is still in the
queue and $w(\{u, v\})$ is strictly smaller than the current key of $v$, it sets the parent of
$v$ to $u$ and decreases the key of $v$ to $w(\{u, v\})$. It returns, for each vertex, its
parent or nothing.

Costs are counted as seven numbers: the five event counts of the queue operations (comparisons,
swaps, reads of the position vector, writes to the position vector, and entry appends, pops or
replacements), the number of adjacency entries inspected, and the number of inspected entries
found still in the queue, which is the number of key comparisons. On a disconnected graph every
vertex is still extracted and the parents form a forest. -/
public def prim {W : Type u} [LinearOrder W] [Zero W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W) (root : Fin n) :
    TimeM ((Fin 5 → Nat) × Nat × Nat) (Vector (Option (Fin n)) n) :=
  let actual := Cslib.Algorithms.Lean.Prim.worker graph weight root
  ⟨actual.ret.parent, actual.time⟩

end Cslib.Algorithms.Lean.Prim
