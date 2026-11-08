/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.AdjacencyMatrix

/-!
# Tests for the adjacency-matrix API

These client examples exercise empty graphs, self-loops, repeated insertion, off-pair
preservation, deletion, and concrete increasing neighbor output through the public
executable and correctness API.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.AdjacencyMatrixTests

open Cslib.Algorithms.Lean

-- Empty graph: no edges, no neighbors, zero out-degree.
example : (AdjacencyMatrix.empty : AdjacencyMatrix 3).hasEdge 0 1 = false := by
  decide

example : (AdjacencyMatrix.empty : AdjacencyMatrix 3).neighbors 0 = [] := by
  decide

example : (AdjacencyMatrix.empty : AdjacencyMatrix 3).outDegree 2 = 0 := by
  decide

/-- Edges `0 -> 3`, `0 -> 1`, `0 -> 0` (self-loop), and `2 -> 0`, inserted out of order. -/
public def graph : AdjacencyMatrix 4 :=
  ((AdjacencyMatrix.empty.addEdge 0 3).addEdge 0 1).addEdge 0 0 |>.addEdge 2 0

-- Concrete increasing neighbor output, regardless of insertion order.
example : graph.neighbors 0 = [0, 1, 3] := by
  decide

example : graph.neighbors 2 = [0] := by
  decide

example : graph.neighbors 1 = [] := by
  decide

example : graph.outDegree 0 = 3 := by
  decide

-- Self-loop and directedness.
example : graph.hasEdge 0 0 = true := by
  decide

example : graph.hasEdge 0 2 = false := by
  decide

example : graph.hasEdge 3 0 = false := by
  decide

-- The documented ordering, through the public sortedness theorem.
example : List.Pairwise (· < ·) (graph.neighbors 0) :=
  graph.neighbors_pairwise_lt 0

example : List.Pairwise (· < ·) ([0, 1, 3] : List (Fin 4)) := by
  have h := graph.neighbors_pairwise_lt 0
  have he : graph.neighbors 0 = [0, 1, 3] := by decide
  rwa [he] at h

example : (graph.neighbors 0).Nodup :=
  graph.neighbors_nodup 0

-- Repeated insertion of the same edge changes nothing observable.
public def graphTwice : AdjacencyMatrix 4 :=
  graph.addEdge 0 1

example : graphTwice.neighbors 0 = [0, 1, 3] := by
  decide

example : graphTwice.hasEdge 0 1 = true := by
  decide

example : graphTwice.outDegree 0 = 3 := by
  decide

example : graphTwice = graph := by
  apply AdjacencyMatrix.ext
  intro a b
  by_cases h : a = 0 ∧ b = 1
  · obtain ⟨rfl, rfl⟩ := h
    decide
  · have hne : a ≠ 0 ∨ b ≠ 1 := not_and_or.mp h
    exact AdjacencyMatrix.hasEdge_addEdge_of_ne graph 0 1 a b hne

-- Off-pair preservation under insertion and deletion (abstract API).
example {n : Nat} (m : AdjacencyMatrix n) (i j a b : Fin n) (h : a ≠ i ∨ b ≠ j) :
    (m.addEdge i j).hasEdge a b = m.hasEdge a b :=
  m.hasEdge_addEdge_of_ne i j a b h

example {n : Nat} (m : AdjacencyMatrix n) (i j a b : Fin n) (h : a ≠ i ∨ b ≠ j) :
    (m.eraseEdge i j).hasEdge a b = m.hasEdge a b :=
  m.hasEdge_eraseEdge_of_ne i j a b h

-- Concrete off-pair preservation: inserting `1 -> 1` keeps the old edges.
public def graphPlus : AdjacencyMatrix 4 :=
  graph.addEdge 1 1

example : graphPlus.neighbors 0 = [0, 1, 3] := by
  decide

example : graphPlus.neighbors 1 = [1] := by
  decide

example : graphPlus.hasEdge 2 0 = true := by
  decide

-- Deletion removes exactly the named edge; deleting an absent edge is a no-op.
public def graphMinus : AdjacencyMatrix 4 :=
  graph.eraseEdge 0 1

example : graphMinus.neighbors 0 = [0, 3] := by
  decide

example : graphMinus.hasEdge 0 1 = false := by
  decide

example : graphMinus.hasEdge 0 0 = true := by
  decide

example : graphMinus.neighbors 2 = [0] := by
  decide

example : (graph.eraseEdge 1 2).neighbors 0 = [0, 1, 3] := by
  decide

example : (graph.eraseEdge 0 0).neighbors 0 = [1, 3] := by
  decide

-- Membership characterization and ordering/degree API on abstract matrices.
example {n : Nat} (m : AdjacencyMatrix n) (i j : Fin n) :
    j ∈ m.neighbors i ↔ m.hasEdge i j = true :=
  m.mem_neighbors i j

example {n : Nat} (m : AdjacencyMatrix n) (i : Fin n) :
    List.Pairwise (· < ·) (m.neighbors i) :=
  m.neighbors_pairwise_lt i

example {n : Nat} (m : AdjacencyMatrix n) (i j : Fin n) :
    j ∈ (m.addEdge i j).neighbors i :=
  m.mem_neighbors_addEdge i j

example {n : Nat} (m : AdjacencyMatrix n) (i j : Fin n) :
    j ∉ (m.eraseEdge i j).neighbors i :=
  m.not_mem_neighbors_eraseEdge i j

end Cslib.Algorithms.Lean.AdjacencyMatrixTests
