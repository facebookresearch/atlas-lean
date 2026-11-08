/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Basic

import Mathlib.Data.List.Nodup

/-!
# Adjacency matrices

An `AdjacencyMatrix n` is a finite directed graph on vertices `Fin n`,
represented by a Boolean edge predicate `adj : Fin n → Fin n → Bool` behind a
structure wrapper. The operations are the empty graph, edge insertion and
deletion at a single ordered pair, an edge query `hasEdge`, and the
out-neighborhood `neighbors m i` as a list of vertices in increasing order.

The main statements are the pointwise characterizations of insertion and
deletion (`hasEdge_addEdge`, `hasEdge_eraseEdge`, and their off-pair variants)
and the agreement of the neighbor list with the edge query
(`mem_neighbors`). No complexity bounds are proved.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

/-- A finite directed graph on `Fin n` given by its Boolean adjacency predicate. -/
structure AdjacencyMatrix (n : Nat) where
  /-- `adj i j = true` when there is a directed edge from `i` to `j`. -/
  adj : Fin n → Fin n → Bool

namespace AdjacencyMatrix

/-- The graph with no edges. -/
def empty {n : Nat} : AdjacencyMatrix n :=
  ⟨fun _ _ => false⟩

instance {n : Nat} : Inhabited (AdjacencyMatrix n) :=
  ⟨empty⟩

/-- Whether there is a directed edge from `i` to `j`. -/
def hasEdge {n : Nat} (m : AdjacencyMatrix n) (i j : Fin n) : Bool :=
  m.adj i j

/-- The empty graph has no edges. -/
@[simp]
theorem hasEdge_empty {n : Nat} (i j : Fin n) :
    (empty : AdjacencyMatrix n).hasEdge i j = false :=
  rfl

/-- Add the single directed edge from `i` to `j`; all other entries are kept. -/
def addEdge {n : Nat} (m : AdjacencyMatrix n) (i j : Fin n) : AdjacencyMatrix n :=
  ⟨fun a b => if a = i ∧ b = j then true else m.adj a b⟩

/-- The added edge is present after insertion. -/
@[simp]
theorem hasEdge_addEdge {n : Nat} (m : AdjacencyMatrix n) (i j : Fin n) :
    (m.addEdge i j).hasEdge i j = true := by
  simp [addEdge, hasEdge]

/-- Insertion does not change any other ordered pair. -/
theorem hasEdge_addEdge_of_ne {n : Nat} (m : AdjacencyMatrix n) (i j a b : Fin n)
    (h : a ≠ i ∨ b ≠ j) :
    (m.addEdge i j).hasEdge a b = m.hasEdge a b := by
  have hne : ¬(a = i ∧ b = j) := fun hp =>
    h.elim (fun hi => hi hp.1) (fun hj => hj hp.2)
  simp [addEdge, hasEdge, hne]

/-- Insertion adds the new edge to the old edge set and nothing else. -/
theorem hasEdge_addEdge_iff {n : Nat} (m : AdjacencyMatrix n) (i j a b : Fin n) :
    (m.addEdge i j).hasEdge a b = true ↔
      (a = i ∧ b = j) ∨ m.hasEdge a b = true := by
  by_cases h : a = i ∧ b = j <;> simp [addEdge, hasEdge, h]

/-- Remove the single directed edge from `i` to `j`; all other entries are kept. -/
def eraseEdge {n : Nat} (m : AdjacencyMatrix n) (i j : Fin n) : AdjacencyMatrix n :=
  ⟨fun a b => if a = i ∧ b = j then false else m.adj a b⟩

/-- The erased edge is absent after deletion. -/
@[simp]
theorem hasEdge_eraseEdge {n : Nat} (m : AdjacencyMatrix n) (i j : Fin n) :
    (m.eraseEdge i j).hasEdge i j = false := by
  simp [eraseEdge, hasEdge]

/-- Deletion does not change any other ordered pair. -/
theorem hasEdge_eraseEdge_of_ne {n : Nat} (m : AdjacencyMatrix n) (i j a b : Fin n)
    (h : a ≠ i ∨ b ≠ j) :
    (m.eraseEdge i j).hasEdge a b = m.hasEdge a b := by
  have hne : ¬(a = i ∧ b = j) := fun hp =>
    h.elim (fun hi => hi hp.1) (fun hj => hj hp.2)
  show (if a = i ∧ b = j then false else m.adj a b) = m.adj a b
  rw [ite_eq_right hne]

/-- Deletion removes the edge from the old edge set and nothing else. -/
theorem hasEdge_eraseEdge_iff {n : Nat} (m : AdjacencyMatrix n) (i j a b : Fin n) :
    (m.eraseEdge i j).hasEdge a b = true ↔
      ¬(a = i ∧ b = j) ∧ m.hasEdge a b = true := by
  by_cases h : a = i ∧ b = j
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [hasEdge_eraseEdge_of_ne m i j a b (not_and_or.mp h)]
    simp [h]

/-- Two adjacency matrices with the same edges everywhere are equal. -/
@[ext]
theorem ext {n : Nat} {m m' : AdjacencyMatrix n}
    (h : ∀ i j, m.hasEdge i j = m'.hasEdge i j) : m = m' := by
  cases m with
  | mk adj =>
    cases m' with
    | mk adj' =>
      congr
      funext i j
      exact h i j

/-- The out-neighbors of `i`, as a list of vertices in increasing order. -/
def neighbors {n : Nat} (m : AdjacencyMatrix n) (i : Fin n) : List (Fin n) :=
  (List.finRange n).filter fun j => m.hasEdge i j

/-- Membership in the neighbor list is the edge query. -/
@[simp]
theorem mem_neighbors {n : Nat} (m : AdjacencyMatrix n) (i j : Fin n) :
    j ∈ m.neighbors i ↔ m.hasEdge i j = true := by
  simp [neighbors]

/-- The neighbor list has no duplicate vertices. -/
theorem neighbors_nodup {n : Nat} (m : AdjacencyMatrix n) (i : Fin n) :
    (m.neighbors i).Nodup :=
  List.Nodup.filter _ (List.nodup_finRange n)

/-- The neighbor list is in strictly increasing order, as documented for
`neighbors`: earlier neighbors are smaller than later ones. -/
theorem neighbors_pairwise_lt {n : Nat} (m : AdjacencyMatrix n) (i : Fin n) :
    List.Pairwise (· < ·) (m.neighbors i) :=
  (List.pairwise_lt_finRange n).filter _

/-- Every vertex of the empty graph has an empty neighbor list. -/
@[simp]
theorem neighbors_empty {n : Nat} (i : Fin n) :
    (empty : AdjacencyMatrix n).neighbors i = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro j hj
  have h := (mem_neighbors (empty : AdjacencyMatrix n) i j).mp hj
  simp at h

/-- After insertion, the target vertex is a neighbor of the source. -/
theorem mem_neighbors_addEdge {n : Nat} (m : AdjacencyMatrix n) (i j : Fin n) :
    j ∈ (m.addEdge i j).neighbors i :=
  (mem_neighbors _ _ _).mpr (hasEdge_addEdge m i j)

/-- After deletion, the target vertex is no longer a neighbor of the source. -/
theorem not_mem_neighbors_eraseEdge {n : Nat} (m : AdjacencyMatrix n) (i j : Fin n) :
    j ∉ (m.eraseEdge i j).neighbors i := by
  rw [mem_neighbors]
  simp

/-- The neighbor list after insertion, characterized by membership. -/
theorem mem_neighbors_addEdge_iff {n : Nat} (m : AdjacencyMatrix n)
    (i j b : Fin n) :
    b ∈ (m.addEdge i j).neighbors i ↔ b = j ∨ b ∈ m.neighbors i := by
  rw [mem_neighbors, mem_neighbors, hasEdge_addEdge_iff]
  constructor
  · rintro (⟨-, hb⟩ | hb)
    · exact Or.inl hb
    · exact Or.inr hb
  · rintro (hb | hb)
    · exact Or.inl ⟨rfl, hb⟩
    · exact Or.inr hb

/-- The out-degree of a vertex: the number of its out-neighbors. -/
def outDegree {n : Nat} (m : AdjacencyMatrix n) (i : Fin n) : Nat :=
  (m.neighbors i).length

/-- Every vertex of the empty graph has out-degree zero. -/
@[simp]
theorem outDegree_empty {n : Nat} (i : Fin n) :
    (empty : AdjacencyMatrix n).outDegree i = 0 := by
  simp [outDegree]

end AdjacencyMatrix

end Cslib.Algorithms.Lean
