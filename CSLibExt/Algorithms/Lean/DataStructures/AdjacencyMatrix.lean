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

/-- **Adjacency matrix.** For a natural number $n$, an adjacency matrix on $n$ vertices is a
directed graph on the vertex set $\{0, \dots, n-1\}$ given by a Boolean-valued function
$\mathrm{adj}$ on ordered pairs of vertices: $\mathrm{adj}(i, j)$ is true exactly when there is a
directed edge from $i$ to $j$. -/
structure AdjacencyMatrix (n : Nat) where
  /-- `adj i j = true` when there is a directed edge from `i` to `j`. -/
  adj : Fin n → Fin n → Bool

namespace AdjacencyMatrix

/-- **Empty adjacency matrix.** For every natural number $n$, the empty adjacency matrix on $n$
vertices is the directed graph on $\{0, \dots, n-1\}$ with no edges: its adjacency function is
false on every ordered pair of vertices. -/
def empty {n : Nat} : AdjacencyMatrix n :=
  ⟨fun _ _ => false⟩

instance {n : Nat} : Inhabited (AdjacencyMatrix n) :=
  ⟨empty⟩

/-- **Edge query of an adjacency matrix.** For an adjacency matrix $m$ on the vertex set
$\{0, \dots, n-1\}$ and vertices $i, j$, the edge query of $m$ at $(i, j)$ is the Boolean value
that is true exactly when $m$ has a directed edge from $i$ to $j$. -/
def hasEdge {n : Nat} (m : AdjacencyMatrix n) (i j : Fin n) : Bool :=
  m.adj i j

/-- **The empty adjacency matrix has no edges.** For every natural number $n$ and all vertices $i$
and $j$ among the $n$ vertices, the empty adjacency matrix on $n$ vertices has no edge from $i$ to
$j$. -/
@[simp]
theorem hasEdge_empty {n : Nat} (i j : Fin n) :
    (empty : AdjacencyMatrix n).hasEdge i j = false :=
  rfl

/-- **Edge insertion in an adjacency matrix.** For an adjacency matrix $m$ on the vertex set
$\{0, \dots, n-1\}$ and vertices $i$ and $j$, adding the edge from $i$ to $j$ gives the adjacency
matrix that has an edge from $i$ to $j$ and agrees with $m$ on every other ordered pair of
vertices. -/
def addEdge {n : Nat} (m : AdjacencyMatrix n) (i j : Fin n) : AdjacencyMatrix n :=
  ⟨fun a b => if a = i ∧ b = j then true else m.adj a b⟩

/-- **An inserted edge is present.** For an adjacency matrix $m$ on $n$ vertices and vertices $i$
and $j$, the matrix obtained from $m$ by adding the edge from $i$ to $j$ has an edge from $i$ to
$j$. -/
@[simp]
theorem hasEdge_addEdge {n : Nat} (m : AdjacencyMatrix n) (i j : Fin n) :
    (m.addEdge i j).hasEdge i j = true := by
  simp [addEdge, hasEdge]

/-- **Inserting an edge leaves other pairs unchanged.** For an adjacency matrix $m$ on $n$
vertices and vertices $i$, $j$, $a$, $b$ with $a \ne i$ or $b \ne j$, the matrix obtained from $m$
by adding the edge from $i$ to $j$ has an edge from $a$ to $b$ if and only if $m$ does. -/
theorem hasEdge_addEdge_of_ne {n : Nat} (m : AdjacencyMatrix n) (i j a b : Fin n)
    (h : a ≠ i ∨ b ≠ j) :
    (m.addEdge i j).hasEdge a b = m.hasEdge a b := by
  have hne : ¬(a = i ∧ b = j) := fun hp =>
    h.elim (fun hi => hi hp.1) (fun hj => hj hp.2)
  simp [addEdge, hasEdge, hne]

/-- **Edges after inserting an edge.** For an adjacency matrix $m$ on $n$ vertices and vertices
$i$, $j$, $a$, $b$, the matrix obtained from $m$ by adding the edge from $i$ to $j$ has an edge
from $a$ to $b$ if and only if $a = i$ and $b = j$, or $m$ has an edge from $a$ to $b$. -/
theorem hasEdge_addEdge_iff {n : Nat} (m : AdjacencyMatrix n) (i j a b : Fin n) :
    (m.addEdge i j).hasEdge a b = true ↔
      (a = i ∧ b = j) ∨ m.hasEdge a b = true := by
  by_cases h : a = i ∧ b = j <;> simp [addEdge, hasEdge, h]

/-- **Edge deletion in an adjacency matrix.** For an adjacency matrix $m$ on the vertex set
$\{0, \dots, n-1\}$ and vertices $i$ and $j$, removing the edge from $i$ to $j$ gives the adjacency
matrix that has no edge from $i$ to $j$ and agrees with $m$ on every other ordered pair of
vertices. -/
def eraseEdge {n : Nat} (m : AdjacencyMatrix n) (i j : Fin n) : AdjacencyMatrix n :=
  ⟨fun a b => if a = i ∧ b = j then false else m.adj a b⟩

/-- **Deleting an edge removes it.** Let $m$ be an adjacency matrix on the vertex set
$\{0, \dots, n-1\}$ and let $i, j$ be vertices. Then the graph obtained from $m$ by deleting the
edge from $i$ to $j$ has no edge from $i$ to $j$. -/
@[simp]
theorem hasEdge_eraseEdge {n : Nat} (m : AdjacencyMatrix n) (i j : Fin n) :
    (m.eraseEdge i j).hasEdge i j = false := by
  simp [eraseEdge, hasEdge]

/-- **Deleting an edge leaves the other entries unchanged.** Let $m$ be an adjacency matrix on the
vertex set $\{0, \dots, n-1\}$ and let $i, j, a, b$ be vertices with $(a, b) \ne (i, j)$, that is,
$a \ne i$ or $b \ne j$. Then the graph obtained from $m$ by deleting the edge from $i$ to $j$ has
an edge from $a$ to $b$ if and only if $m$ has an edge from $a$ to $b$. -/
theorem hasEdge_eraseEdge_of_ne {n : Nat} (m : AdjacencyMatrix n) (i j a b : Fin n)
    (h : a ≠ i ∨ b ≠ j) :
    (m.eraseEdge i j).hasEdge a b = m.hasEdge a b := by
  have hne : ¬(a = i ∧ b = j) := fun hp =>
    h.elim (fun hi => hi hp.1) (fun hj => hj hp.2)
  show (if a = i ∧ b = j then false else m.adj a b) = m.adj a b
  rw [ite_eq_right hne]

/-- **Edges after deleting an edge.** For an adjacency matrix $m$ on $n$ vertices and vertices $i$,
$j$, $a$, $b$, the matrix obtained from $m$ by removing the edge from $i$ to $j$ has an edge from
$a$ to $b$ if and only if $(a, b) \ne (i, j)$ and $m$ has an edge from $a$ to $b$. -/
theorem hasEdge_eraseEdge_iff {n : Nat} (m : AdjacencyMatrix n) (i j a b : Fin n) :
    (m.eraseEdge i j).hasEdge a b = true ↔
      ¬(a = i ∧ b = j) ∧ m.hasEdge a b = true := by
  by_cases h : a = i ∧ b = j
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [hasEdge_eraseEdge_of_ne m i j a b (not_and_or.mp h)]
    simp [h]

/-- **Extensionality of adjacency matrices.** Two adjacency matrices $m$ and $m'$ on the same $n$
vertices are equal if, for all vertices $i$ and $j$, $m$ has an edge from $i$ to $j$ exactly when
$m'$ does. -/
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

/-- **Out-neighbor list.** For an adjacency matrix $m$ on the vertex set $\{0, \dots, n-1\}$ and a
vertex $i$, the out-neighbor list of $i$ is the list of all vertices $j$ such that $m$ has a
directed edge from $i$ to $j$, in increasing order. -/
def neighbors {n : Nat} (m : AdjacencyMatrix n) (i : Fin n) : List (Fin n) :=
  (List.finRange n).filter fun j => m.hasEdge i j

/-- **The out-neighbor list matches the edge query.** Let $m$ be an adjacency matrix on the vertex
set $\{0, \dots, n-1\}$ and let $i, j$ be vertices. Then $j$ belongs to the out-neighbor list of
$i$ if and only if $m$ has a directed edge from $i$ to $j$. -/
@[simp]
theorem mem_neighbors {n : Nat} (m : AdjacencyMatrix n) (i j : Fin n) :
    j ∈ m.neighbors i ↔ m.hasEdge i j = true := by
  simp [neighbors]

/-- **Out-neighbor lists have no duplicates.** For an adjacency matrix $m$ on the vertex set
$\{0, \dots, n-1\}$ and a vertex $i$, no vertex occurs twice in the out-neighbor list of $i$. -/
theorem neighbors_nodup {n : Nat} (m : AdjacencyMatrix n) (i : Fin n) :
    (m.neighbors i).Nodup :=
  List.Nodup.filter _ (List.nodup_finRange n)

/-- **Out-neighbor lists are strictly increasing.** For an adjacency matrix $m$ on the vertex set
$\{0, \dots, n-1\}$ and a vertex $i$, the out-neighbor list of $i$ is strictly increasing: every
vertex in it is smaller than every vertex that comes after it. -/
theorem neighbors_pairwise_lt {n : Nat} (m : AdjacencyMatrix n) (i : Fin n) :
    List.Pairwise (· < ·) (m.neighbors i) :=
  (List.pairwise_lt_finRange n).filter _

/-- **Out-neighbor lists of the empty graph.** In the graph with no edges on the vertex set
$\{0, \dots, n-1\}$, the out-neighbor list of every vertex $i$ is the empty list. -/
@[simp]
theorem neighbors_empty {n : Nat} (i : Fin n) :
    (empty : AdjacencyMatrix n).neighbors i = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro j hj
  have h := (mem_neighbors (empty : AdjacencyMatrix n) i j).mp hj
  simp at h

/-- **Adding an edge makes its target an out-neighbor.** Let $m$ be an adjacency matrix on the
vertex set $\{0, \dots, n-1\}$ and let $i, j$ be vertices. Then $j$ belongs to the out-neighbor
list of $i$ in the graph obtained from $m$ by adding the edge from $i$ to $j$. -/
theorem mem_neighbors_addEdge {n : Nat} (m : AdjacencyMatrix n) (i j : Fin n) :
    j ∈ (m.addEdge i j).neighbors i :=
  (mem_neighbors _ _ _).mpr (hasEdge_addEdge m i j)

/-- **Deleting an edge removes the out-neighbor.** Let $G$ be a directed graph on the vertices
$0, \dots, n-1$, given by its adjacency matrix, and let $i$ and $j$ be vertices. After the edge
from $i$ to $j$ is deleted from $G$ (whether or not $G$ had that edge), $j$ is not an
out-neighbor of $i$. -/
theorem not_mem_neighbors_eraseEdge {n : Nat} (m : AdjacencyMatrix n) (i j : Fin n) :
    j ∉ (m.eraseEdge i j).neighbors i := by
  rw [mem_neighbors]
  simp

/-- **Out-neighbors after adding an edge.** Let $m$ be an adjacency matrix on the vertex set
$\{0, \dots, n-1\}$ and let $i, j, b$ be vertices. Then $b$ belongs to the out-neighbor list of
$i$ in the graph obtained from $m$ by adding the edge from $i$ to $j$ if and only if $b = j$ or
$b$ belongs to the out-neighbor list of $i$ in $m$. -/
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

/-- **Out-degree.** The out-degree of a vertex $i$ of a directed graph given by an adjacency
matrix is the number of its out-neighbors, that is, the number of vertices $j$ such that there is
an edge from $i$ to $j$. -/
def outDegree {n : Nat} (m : AdjacencyMatrix n) (i : Fin n) : Nat :=
  (m.neighbors i).length

/-- **Vertices of the empty graph have out-degree zero.** For every $n$, every vertex of the
empty directed graph on the vertices $0, \dots, n-1$ has out-degree $0$. -/
@[simp]
theorem outDegree_empty {n : Nat} (i : Fin n) :
    (empty : AdjacencyMatrix n).outDegree i = 0 := by
  simp [outDegree]

end AdjacencyMatrix

end Cslib.Algorithms.Lean
