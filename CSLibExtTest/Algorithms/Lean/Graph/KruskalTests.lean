/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.Kruskal
public meta import CSLibExt.Algorithms.Lean.Graph.Kruskal
public meta import CSLibExt.Algorithms.Lean.DataStructures.UnionFind
import all Init.Data.List.Sort.Basic

import Mathlib.Tactic

/-! Importing tests for deterministic Kruskal minimum spanning forests. -/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.KruskalTests

open Kruskal
open UnionFind

private def ordinals {n : Nat} (graph : Graph n) : List Nat :=
  (kruskal graph).map WeightedEdge.ordinal

private def connected : Graph 4 where
  rawEdges := [
    ⟨0, 1, 1⟩,
    ⟨1, 2, 1⟩,
    ⟨0, 2, 1⟩,
    ⟨2, 3, 2⟩]

private def disconnected : Graph 5 where
  rawEdges := [⟨0, 1, 2⟩, ⟨3, 4, 1⟩]

private def edgeCases : Graph 3 where
  rawEdges := [
    ⟨0, 0, 0⟩,
    ⟨0, 9, 0⟩,
    ⟨0, 1, 2⟩,
    ⟨0, 1, 1⟩,
    ⟨1, 2, 1⟩,
    ⟨0, 2, 1⟩]

private def nontrivial : Graph 6 where
  rawEdges := [
    ⟨0, 1, 4⟩,
    ⟨0, 2, 3⟩,
    ⟨1, 2, 1⟩,
    ⟨1, 3, 2⟩,
    ⟨2, 3, 4⟩,
    ⟨3, 4, 2⟩,
    ⟨4, 5, 6⟩,
    ⟨3, 5, 3⟩,
    ⟨0, 8, 0⟩]

example : ordinals connected = [0, 1, 3] := by
  norm_num [ordinals, connected, kruskal, orderedEdges, validEdges, validEdgesFrom,
    decodeAt, sortEdges, List.mergeSort, KeyLE, WeightedEdge.key, keyLEDecidable, scan,
    State.step, initialForest, Equivalent, find, union, link, linkParent, linkDepth]

example : ordinals disconnected = [1, 0] := by
  norm_num [ordinals, disconnected, kruskal, orderedEdges, validEdges, validEdgesFrom,
    decodeAt, sortEdges, List.mergeSort, KeyLE, WeightedEdge.key, keyLEDecidable, scan,
    State.step, initialForest, Equivalent, find, union, link, linkParent, linkDepth]

example : ordinals edgeCases = [3, 4] := by
  norm_num [ordinals, edgeCases, kruskal, orderedEdges, validEdges, validEdgesFrom,
    decodeAt, sortEdges, List.mergeSort, KeyLE, WeightedEdge.key, keyLEDecidable, scan,
    State.step, initialForest, Equivalent, find, union, link, linkParent, linkDepth]

example : ordinals nontrivial = [2, 3, 5, 1, 7] := by
  norm_num [ordinals, nontrivial, kruskal, orderedEdges, validEdges, validEdgesFrom,
    decodeAt, sortEdges, List.mergeSort, KeyLE, WeightedEdge.key, keyLEDecidable, scan,
    State.step, initialForest, Equivalent, find, union, link, linkParent, linkDepth]

example : (validEdges edgeCases).map WeightedEdge.ordinal = [0, 2, 3, 4, 5] := by decide
example : (validEdges disconnected).length = 2 := by decide
example : (kruskal (n := 0) ⟨[]⟩) = [] := by
  simp [kruskal, orderedEdges, sortEdges, validEdges, validEdgesFrom, scan]

example {n : Nat} (graph : Graph n) (edge : WeightedEdge n)
    (h : edge ∈ kruskal graph) : edge ∈ validEdges graph :=
  kruskal_edge_mem_valid graph h

example {n : Nat} (graph : Graph n) : Acyclic (kruskal graph) :=
  kruskal_acyclic graph

example {n : Nat} (graph : Graph n) : Spans graph (kruskal graph) :=
  kruskal_spans graph

example {n : Nat} (graph : Graph n) :
    (kruskal graph).Pairwise (fun left right => KeyLE left.key right.key) :=
  kruskal_pairwise_key_le graph

example {n : Nat} (graph : Graph n) : HasGreedyCutProperty graph :=
  kruskal_greedy_cut_property graph

/-- Importing clients can apply the complete structural certificate. -/
public theorem imported_kruskal_certificate {n : Nat} (graph : Graph n) :
    IsOrderedSpanningForest graph (kruskal graph) :=
  kruskal_isOrderedSpanningForest graph

#check RawEdge
#check Graph
#check WeightedEdge
#check validEdges
#check orderedEdges
#check Connected
#check Acyclic
#check Spans
#check totalWeight
#check IsSpanningForest
#check IsOrderedSpanningForest
#check HasGreedyCutProperty
#check kruskal
#check kruskal_edge_mem_valid
#check kruskal_acyclic
#check kruskal_spans
#check kruskal_pairwise_key_le
#check kruskal_greedy_cut_property
#check kruskal_light_edge
#check kruskal_isSpanningForest
#check kruskal_isOrderedSpanningForest
#check imported_kruskal_certificate

#print axioms kruskal_edge_mem_valid
#print axioms kruskal_acyclic
#print axioms kruskal_spans
#print axioms kruskal_pairwise_key_le
#print axioms kruskal_greedy_cut_property
#print axioms kruskal_light_edge
#print axioms kruskal_isSpanningForest
#print axioms kruskal_isOrderedSpanningForest
#print axioms imported_kruskal_certificate

private def parallel : Graph 2 where
  rawEdges := [⟨0, 1, 5⟩, ⟨1, 0, 1⟩, ⟨0, 1, 1⟩, ⟨0, 0, 0⟩, ⟨2, 0, 0⟩]

private def strictCompetitor : List (WeightedEdge 2) := [⟨0, 0, 1, 5⟩]

private def tiedCompetitor : List (WeightedEdge 2) := [⟨2, 0, 1, 1⟩]

private theorem strictCompetitor_spanning : IsSpanningForest parallel strictCompetitor := by
  norm_num [IsSpanningForest, parallel, strictCompetitor, validEdges, validEdgesFrom,
    decodeAt, Acyclic, AcyclicRev, Spans, Connected, ConnectedRev]

private theorem tiedCompetitor_spanning : IsSpanningForest parallel tiedCompetitor := by
  norm_num [IsSpanningForest, parallel, tiedCompetitor, validEdges, validEdgesFrom,
    decodeAt, Acyclic, AcyclicRev, Spans, Connected, ConnectedRev]

private theorem competitor_lower_bounds :
    totalWeight (kruskal parallel) ≤ totalWeight strictCompetitor ∧
    totalWeight (kruskal parallel) ≤ totalWeight tiedCompetitor ∧
    totalWeight strictCompetitor = 5 ∧ totalWeight tiedCompetitor = 1 :=
  ⟨kruskal_minimal parallel strictCompetitor strictCompetitor_spanning,
    kruskal_minimal parallel tiedCompetitor tiedCompetitor_spanning, rfl, rfl⟩

#check kruskal_minimal
#print axioms kruskal_minimal
#print axioms competitor_lower_bounds

private theorem empty_not_spanning : ¬IsSpanningForest parallel [] := by
  norm_num [IsSpanningForest, parallel, validEdges, validEdgesFrom, decodeAt,
    Acyclic, AcyclicRev, Spans, Connected, ConnectedRev]

@[no_expose, instance_reducible] private def connectedRevDecidable {n : Nat}
    (edges : List (WeightedEdge n)) : DecidableRel (ConnectedRev edges) :=
  match edges with
  | [] => fun left right => inferInstanceAs (Decidable (left = right))
  | edge :: rest => fun left right =>
      letI : DecidableRel (ConnectedRev rest) := connectedRevDecidable rest
      inferInstanceAs (Decidable (ConnectedRev rest left right ∨
        (ConnectedRev rest left edge.source ∧ ConnectedRev rest right edge.target) ∨
        (ConnectedRev rest left edge.target ∧ ConnectedRev rest right edge.source)))

@[no_expose] private def acyclicRevDecidable {n : Nat}
    (edges : List (WeightedEdge n)) : Decidable (AcyclicRev edges) :=
  match edges with
  | [] => isTrue trivial
  | edge :: rest =>
      letI : DecidableRel (ConnectedRev rest) := connectedRevDecidable rest
      letI : Decidable (AcyclicRev rest) := acyclicRevDecidable rest
      inferInstanceAs (Decidable
        (¬ConnectedRev rest edge.source edge.target ∧ AcyclicRev rest))

@[no_expose] private def spanningForestDecidable {n : Nat} (graph : Graph n)
    (edges : List (WeightedEdge n)) : Decidable (IsSpanningForest graph edges) := by
  letI : DecidableRel (ConnectedRev edges.reverse) := connectedRevDecidable edges.reverse
  letI : Decidable (AcyclicRev edges.reverse) := acyclicRevDecidable edges.reverse
  unfold IsSpanningForest Acyclic Spans Connected
  infer_instance

@[no_expose] private def checkRuntime {n : Nat} (label : String) (graph : Graph n)
    (expectedOrdinals : List Nat) (expectedWeight : Nat) : IO Unit := do
  let selected := kruskal graph
  let actual := selected.map WeightedEdge.ordinal
  let weight := totalWeight selected
  letI : Decidable (IsSpanningForest graph selected) := spanningForestDecidable graph selected
  unless decide (IsSpanningForest graph selected) do
    throw (IO.userError s!"{label}: output is not a canonical spanning forest")
  unless actual == expectedOrdinals && weight == expectedWeight do
    throw (IO.userError s!"{label}: got {actual} with weight {weight}")
  IO.println s!"runtime {label}: ordinals {actual}, weight {weight}, canonical forest checked"

private def zeroWeights : Graph 3 where
  rawEdges := [⟨0, 1, 0⟩, ⟨1, 2, 0⟩, ⟨0, 2, 0⟩]

private def zeroVertices : Graph 0 where
  rawEdges := [⟨0, 0, 7⟩, ⟨0, 1, 0⟩]

private def oneVertex : Graph 1 where
  rawEdges := [⟨0, 0, 0⟩, ⟨0, 0, 3⟩, ⟨1, 0, 0⟩]

#eval do
  checkRuntime "connected" connected [0, 1, 3] 4
  checkRuntime "disconnected and isolated" disconnected [1, 0] 3
  checkRuntime "loops, invalid endpoints, parallel and ties" edgeCases [3, 4] 2
  checkRuntime "nontrivial" nontrivial [2, 3, 5, 1, 7] 11
  checkRuntime "reversed parallel occurrences" parallel [1] 1
  checkRuntime "zero weights" zeroWeights [0, 1] 0
  checkRuntime "zero vertices with invalid input" zeroVertices [] 0
  checkRuntime "one vertex with loops" oneVertex [] 0
  checkRuntime "edgeless isolated vertices" (Graph.mk [] : Graph 4) [] 0

@[no_expose] private def checkCompetitors : IO Unit := do
  let selected := kruskal parallel
  let strictForest := @decide (IsSpanningForest parallel strictCompetitor)
    (spanningForestDecidable parallel strictCompetitor)
  let tiedForest := @decide (IsSpanningForest parallel tiedCompetitor)
    (spanningForestDecidable parallel tiedCompetitor)
  let emptyForest := @decide (IsSpanningForest parallel []) (spanningForestDecidable parallel [])
  unless strictForest &&
      decide (totalWeight selected < totalWeight strictCompetitor) do
    throw (IO.userError "strict competitor: expected a canonical, strictly heavier forest")
  IO.println (s!"strict competitor: optimum {totalWeight selected}, " ++
    s!"competitor {totalWeight strictCompetitor}, canonical checked")
  unless tiedForest &&
      totalWeight selected == totalWeight tiedCompetitor &&
      selected.map WeightedEdge.ordinal != tiedCompetitor.map WeightedEdge.ordinal do
    throw (IO.userError "tied competitor: expected equal weight with different occurrence labels")
  if emptyForest then
    throw (IO.userError "missing-spanning control: empty forest incorrectly accepted")
  IO.println (s!"tied competitor: optimum {totalWeight selected}, " ++
    s!"competitor {totalWeight tiedCompetitor}, labels differ; empty nonforest rejected")

#eval checkCompetitors

end Cslib.Algorithms.Lean.KruskalTests
