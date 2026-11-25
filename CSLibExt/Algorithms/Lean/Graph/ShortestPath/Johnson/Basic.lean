/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.ShortestPath.BellmanFord
import CSLibExt.Algorithms.Lean.Graph.ShortestPath.Dijkstra
import Mathlib.Algebra.Order.AddGroupWithTop

/-!
# Integer Johnson shortest paths

The actual Johnson composition over integer edge occurrences, with the canonical dense Dijkstra
algorithm. This is the integer/dense specialization of CLRS, fourth edition, Section 23.3.
The selected cost model does not assert the source's heap bounds or full machine/bit complexity.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Johnson

open BellmanFord

private def liftEdge {n : Nat} (edge : Edge n) : Edge (n + 1) :=
  ⟨edge.source.castSucc, edge.target.castSucc, edge.weight⟩

private def sourceEdges {n : Nat} : List (Fin n) → TimeM Nat (List (Edge (n + 1)))
  | [] => pure []
  | vertex :: rest => do
      TimeM.tick 1
      let tail ← sourceEdges rest
      pure (⟨Fin.last n, vertex.castSucc, 0⟩ :: tail)

private def liftEdges {n : Nat} (tail : List (Edge (n + 1))) :
    List (Edge n) → TimeM Nat (List (Edge (n + 1)))
  | [] => pure tail
  | edge :: rest => do
      TimeM.tick 1
      let lifted ← liftEdges tail rest
      pure (liftEdge edge :: lifted)

private def augment {n : Nat} (edges : List (Edge n)) :
    TimeM Nat (List (Edge (n + 1))) := do
  let zeros ← sourceEdges (List.finRange n)
  liftEdges zeros edges

private def buildVector {α : Type} :
    (n : Nat) → (Fin n → TimeM Nat α) → TimeM Nat (Vector α n)
  | 0, _ => pure #v[]
  | n + 1, action => do
      let previous ← buildVector n (fun vertex => action vertex.castSucc)
      let last ← action (Fin.last n)
      pure (previous.push last)

private def readPotentials {n : Nat} (result : Distances n) : TimeM Nat (Vector Int n) :=
  buildVector n fun vertex => do
    TimeM.tick 1
    pure ((result.distance.get vertex).getD 0)

private def reweightEdges {n : Nat} (potential : Vector Int n) :
    List (Edge n) → TimeM Nat (List (Edge n))
  | [] => pure []
  | edge :: rest => do
      TimeM.tick 1
      let tail ← reweightEdges potential rest
      pure (⟨edge.source, edge.target,
        edge.weight + potential.get edge.source - potential.get edge.target⟩ :: tail)

private structure Prepared (n : Nat) where
  buckets : Vector (List (Fin n)) n
  minima : Vector (Vector (Option Nat) n) n

private def emptyPrepared (n : Nat) : TimeM Nat (Prepared n) := do
  let minima ← buildVector n fun _ => buildVector n fun _ => do
    TimeM.tick 1
    pure none
  let buckets ← buildVector n fun _ => do
    TimeM.tick 1
    pure []
  pure ⟨buckets, minima⟩

private def insertPrepared {n : Nat} (prepared : Prepared n)
    (entry : Edge n × Edge (n + 1)) : TimeM Nat (Prepared n) := do
  TimeM.tick 1
  let source := entry.1.source
  let target := entry.1.target
  let weight := entry.2.weight.toNat
  let old := (prepared.minima.get source).get target
  let minimum := match old with
    | none => weight
    | some value => min value weight
  let row := (prepared.minima.get source).set target.val (some minimum) target.isLt
  pure ⟨prepared.buckets.set source.val (target :: prepared.buckets.get source) source.isLt,
    prepared.minima.set source.val row source.isLt⟩

private def insertEntries {n : Nat} :
    List (Edge n × Edge (n + 1)) → Prepared n → TimeM Nat (Prepared n)
  | [], prepared => pure prepared
  | entry :: rest, prepared => do
      let next ← insertPrepared prepared entry
      insertEntries rest next

private def reverseBucket {n : Nat} : List (Fin n) → List (Fin n) → TimeM Nat (List (Fin n))
  | [], accumulator => pure accumulator
  | vertex :: rest, accumulator => do
      TimeM.tick 1
      reverseBucket rest (vertex :: accumulator)

private def prepare {n : Nat} (edges : List (Edge n))
    (reweighted : List (Edge (n + 1))) : TimeM Nat (Prepared n) := do
  let empty ← emptyPrepared n
  let inserted ← insertEntries (edges.zip reweighted) empty
  let buckets ← buildVector n fun vertex => reverseBucket (inserted.buckets.get vertex) []
  pure ⟨buckets, inserted.minima⟩

private def Prepared.graph {n : Nat} (prepared : Prepared n) : DirectedAdjacency (Fin n) where
  vertices := List.finRange n
  vertices_nodup := List.nodup_finRange n
  vertices_complete := List.mem_finRange
  adjacency := prepared.buckets.get

private def Prepared.weight {n : Nat} (prepared : Prepared n) (source target : Fin n) : Nat :=
  ((prepared.minima.get source).get target).getD 0

private def runRow {n : Nat} (prepared : Prepared n) (potential : Vector Int (n + 1))
    (source : Fin n) : TimeM Nat (Vector (WithTop Int) n) := do
  TimeM.tick 1
  let run := prepared.graph.dijkstra prepared.weight source
  let result ← ({ ret := run.ret, time := run.time.total } : TimeM Nat _)
  buildVector n fun target => do
    TimeM.tick 1
    pure (match result.distance.get target with
      | none => ⊤
      | some distance => ((distance : Int) + potential.get target.castSucc -
          potential.get source.castSucc : Int))

/-- **Johnson's algorithm.** Let $E$ be a list of directed edges on the vertices
$\{0, \dots, n-1\}$ with integer weights. Johnson's algorithm adds a new vertex $s$ with an
edge of weight $0$ to every original vertex and runs Bellman–Ford from $s$. If Bellman–Ford
reports a negative cycle, the algorithm returns no table. Otherwise let $h(v)$ be the
Bellman–Ford distance of $v$ (taken to be $0$ if $v$ is unreached). Each edge from $u$ to $v$ of
weight $w$ gets the new weight $\max(0, w + h(u) - h(v))$.
For each original vertex $u$ the algorithm runs Dijkstra from $u$ on the original vertices,
where the weight from $x$ to $y$ is the least new weight of an edge from $x$ to $y$. It
returns the table whose entry at $(u, v)$ is $\infty$ if Dijkstra does not reach $v$, and
$d'(u, v) + h(v) - h(u)$ otherwise, where $d'(u, v)$ is the Dijkstra distance.

The cost counts the selected construction, scan, relaxation and decoding actions, not full RAM
or bit complexity. -/
public def johnson {n : Nat} (edges : List (Edge n)) :
    TimeM Nat (Option (Fin n → Fin n → WithTop Int)) := do
  let augmented ← augment edges
  let run := bellmanFord augmented (Fin.last n)
  let result ← ({ ret := run.ret, time := run.time.total } : TimeM Nat _)
  match result with
  | .negativeCycle _ => pure none
  | .distances distances => do
      let potential ← readPotentials distances
      let reweighted ← reweightEdges potential augmented
      let prepared ← prepare edges reweighted
      let rows ← buildVector n (runRow prepared potential)
      pure (some fun source target => (rows.get source).get target)

end Cslib.Algorithms.Lean.Johnson
