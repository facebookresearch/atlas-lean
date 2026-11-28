/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Foundations.Semantics.LTS.Basic
public import Cslib.Foundations.Relation.RelatesInSteps
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Logic.Relation

/-!
# Ordered finite directed-adjacency graphs

This module gives executable directed graphs a certified vertex order while
keeping their edge semantics independent of duplicate adjacency entries.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

universe u

/-- **Directed adjacency graph.** A directed adjacency graph on a type $V$ consists of a list of
vertices that has no duplicates and contains every element of $V$ (so $V$ is finite), together
with, for each vertex $v$, an ordered list of the out-neighbors of $v$, in which entries may
repeat. -/
structure DirectedAdjacency (V : Type u) where
  /-- The complete deterministic enumeration of vertices. -/
  vertices : List V
  /-- The vertex enumeration contains no duplicates. -/
  vertices_nodup : vertices.Nodup
  /-- Every vertex occurs in the enumeration. -/
  vertices_complete : ∀ vertex, vertex ∈ vertices
  /-- The ordered outgoing neighbors of each vertex. Entries may repeat. -/
  adjacency : V → List V

/-- **Edge of a directed adjacency graph.** For a directed adjacency graph $G$ on $V$ and
vertices $s, t \in V$, there is an edge from $s$ to $t$ in $G$ when $t$ occurs in the adjacency
list of $s$. -/
def DirectedAdjacency.Edge {V : Type u} (graph : DirectedAdjacency V)
    (source target : V) : Prop :=
  target ∈ graph.adjacency source

/-- **Walks of a given length.** For a directed adjacency graph $G$, a natural number $n$ and
vertices $s$ and $t$, there is a walk of length $n$ from $s$ to $t$ in $G$ when there are
vertices $v_0, \dots, v_n$ with $v_0 = s$ and $v_n = t$ such that $(v_i, v_{i+1})$ is an edge
of $G$ for every $i < n$. -/
abbrev DirectedAdjacency.Walk {V : Type u} (graph : DirectedAdjacency V)
    (length : Nat) (source target : V) : Prop :=
  Relation.RelatesInSteps graph.Edge source target length

namespace DirectedAdjacency

variable {V : Type u} {graph graph₁ graph₂ graph₃ : DirectedAdjacency V}
variable {length leftLength rightLength : Nat}
variable {source middle target : V}

/-- **The digraph of a directed adjacency graph.** The digraph associated with a directed
adjacency graph $G$ on a vertex type $V$ is the directed graph on $V$ in which $s$ is adjacent to
$t$ exactly when $G$ has an edge from $s$ to $t$. It forgets the order of the adjacency lists and
the multiplicity of their entries. -/
def toDigraph (graph : DirectedAdjacency V) : Digraph V where
  Adj := graph.Edge

/-- **Adjacency in the associated digraph.** For a directed adjacency graph $G$ and vertices $s$
and $t$, $s$ is adjacent to $t$ in the digraph associated with $G$ if and only if $G$ has an edge
from $s$ to $t$, that is, $t$ occurs in the adjacency list of $s$. -/
@[simp]
theorem toDigraph_adj : graph.toDigraph.Adj source target ↔ graph.Edge source target :=
  Iff.rfl

/-- **Walks of length zero.** In a directed adjacency graph, there is a walk of length $0$ from
a vertex $s$ to a vertex $t$ if and only if $s = t$. -/
@[simp]
theorem walk_zero_iff : Walk graph 0 source target ↔ source = target :=
  Relation.RelatesInSteps.zero_iff

/-- **Splitting off the first edge of a walk.** In a directed adjacency graph $G$, for every
natural number $n$ and all vertices $s$ and $t$, there is a walk of length $n + 1$ from $s$ to
$t$ if and only if there is a vertex $v$ such that $(s, v)$ is an edge of $G$ and there is a
walk of length $n$ from $v$ to $t$. -/
theorem walk_succ_iff :
    Walk graph (Nat.succ length) source target ↔
      ∃ next, graph.Edge source next ∧ Walk graph length next target := by
  simpa [Nat.succ_eq_add_one] using
    (Relation.RelatesInSteps.succ'_iff (r := graph.Edge)
      (a := source) (b := target) (n := length))

/-- **Concatenation of walks.** Let $G$ be a directed adjacency graph on $V$ and let
$s, m, t \in V$. If $G$ has a walk of length exactly $a$ from $s$ to $m$ and a walk of length
exactly $b$ from $m$ to $t$, then $G$ has a walk of length exactly $a + b$ from $s$ to $t$. -/
theorem Walk.append
    (left : Walk graph leftLength source middle)
    (right : Walk graph rightLength middle target) :
    Walk graph (leftLength + rightLength) source target :=
  Relation.RelatesInSteps.trans left right

/-- **Reachability in a directed graph.** For a directed adjacency graph $G$ and vertices $s$
and $t$, $t$ is reachable from $s$ when the pair $(s, t)$ lies in the reflexive-transitive
closure of the edge relation of $G$: either $s = t$, or a finite sequence of edges of $G$ leads
from $s$ to $t$. -/
def Reachable (graph : DirectedAdjacency V) (source target : V) : Prop :=
  Relation.ReflTransGen graph.Edge source target

/-- **Reachability by walks.** In a directed adjacency graph $G$, a vertex $t$ is reachable from
a vertex $s$ if and only if there is a natural number $n$ such that $G$ has a walk of length
exactly $n$ from $s$ to $t$. -/
theorem reachable_iff_exists_walk :
    graph.Reachable source target ↔ ∃ length, Walk graph length source target :=
  ⟨Relation.ReflTransGen.relatesInSteps,
    fun ⟨_, walk⟩ => Relation.RelatesInSteps.reflTransGen walk⟩

/-- **Reachability is the reflexive-transitive closure of the edge relation.** In a directed
adjacency graph $G$, a vertex $t$ is reachable from a vertex $s$ if and only if $(s, t)$ lies
in the reflexive-transitive closure of the edge relation of $G$. -/
theorem reachable_iff_reflTransGen :
    graph.Reachable source target ↔
      Relation.ReflTransGen graph.Edge source target :=
  Iff.rfl

/-- **The transition system of a directed adjacency graph.** The labelled transition system of a
directed adjacency graph $G$ has the vertices of $G$ as states and a single label, and it has a
transition from $s$ to $t$ exactly when $G$ has an edge from $s$ to $t$. -/
def toLTS (graph : DirectedAdjacency V) : _root_.Cslib.LTS V Unit where
  Tr source _ target := graph.Edge source target

private theorem Walk.toMTr
    (walk : Walk graph length source target) :
    graph.toLTS.MTr source (List.replicate length ()) target := by
  induction walk using Relation.RelatesInSteps.head_induction_on with
  | hrefl => exact _root_.Cslib.LTS.MTr.refl
  | hhead head _ induction =>
      simpa [List.replicate_succ] using
        (_root_.Cslib.LTS.MTr.stepL head induction)

private theorem mTr_to_walk {labels : List Unit}
    (trace : graph.toLTS.MTr source labels target) :
    Walk graph labels.length source target := by
  induction trace with
  | refl => exact Relation.RelatesInSteps.refl _
  | stepL head tail induction =>
      exact Relation.RelatesInSteps.head _ _ _ _ head induction

/-- **Reachability in the associated transition system.** In a directed adjacency graph $G$, a
vertex $t$ is reachable from a vertex $s$ if and only if, in the unit-labelled labelled
transition system of $G$, there is a finite list of labels along which $s$ reaches $t$ by a
multistep transition. -/
theorem reachable_iff_lts :
    graph.Reachable source target ↔
      ∃ labels, graph.toLTS.MTr source labels target := by
  constructor
  · intro reachable
    obtain ⟨walkLength, walk⟩ := reachable_iff_exists_walk.mp reachable
    exact ⟨List.replicate walkLength (), walk.toMTr⟩
  · rintro ⟨labels, trace⟩
    exact Relation.RelatesInSteps.reflTransGen (mTr_to_walk trace)

/-- **Transpose of a directed adjacency graph.** For a directed adjacency graph $G$ on a
vertex type with decidable equality, the transpose of $G$ has the same vertex enumeration as
$G$, and the adjacency list of a vertex $v$ consists of the vertices $u$ such that $v$ occurs
in the adjacency list of $u$ in $G$, each listed once and in the order of the vertex
enumeration. -/
def transpose [DecidableEq V] (graph : DirectedAdjacency V) : DirectedAdjacency V where
  vertices := graph.vertices
  vertices_nodup := graph.vertices_nodup
  vertices_complete := graph.vertices_complete
  adjacency target := graph.vertices.filter fun source => target ∈ graph.adjacency source

/-- **Edges of the transpose graph.** Let $V$ have decidable equality and let $G$ be a directed
adjacency graph on $V$. For all $s, t \in V$, the transpose of $G$ has an edge from $s$ to $t$
if and only if $G$ has an edge from $t$ to $s$. -/
@[simp]
theorem edge_transpose [DecidableEq V] :
    (graph.transpose).Edge source target ↔ graph.Edge target source := by
  simp only [transpose, Edge, List.mem_filter]
  constructor
  · rintro ⟨_, edge⟩
    exact of_decide_eq_true edge
  · intro edge
    exact ⟨graph.vertices_complete target, decide_eq_true edge⟩

/-- **Walks in the transpose are reversed walks.** For a directed adjacency graph $G$ on a
vertex type with decidable equality, every natural number $n$ and all vertices $s$ and $t$,
there is a walk of length $n$ from $s$ to $t$ in the transpose of $G$ if and only if there is
a walk of length $n$ from $t$ to $s$ in $G$. -/
theorem walk_transpose_iff [DecidableEq V] :
    Walk graph.transpose length source target ↔ Walk graph length target source := by
  constructor
  · intro walk
    induction walk with
    | refl => exact Relation.RelatesInSteps.refl _
    | tail _ _ _ _ last induction =>
        exact Relation.RelatesInSteps.head _ _ _ _ (edge_transpose.mp last) induction
  · intro walk
    induction walk with
    | refl => exact Relation.RelatesInSteps.refl _
    | tail _ _ _ _ last induction =>
        exact Relation.RelatesInSteps.head _ _ _ _ (edge_transpose.mpr last) induction

/-- **Reachability in the transpose graph.** Let $G$ be a directed adjacency graph on a vertex
type with decidable equality, and let $G^{\mathsf{T}}$ be its transpose. For all vertices $s$ and
$t$, $t$ is reachable from $s$ in $G^{\mathsf{T}}$ if and only if $s$ is reachable from $t$ in
$G$. -/
theorem reachable_transpose_iff [DecidableEq V] :
    graph.transpose.Reachable source target ↔ graph.Reachable target source := by
  simp only [reachable_iff_exists_walk]
  constructor
  · rintro ⟨walkLength, walk⟩
    exact ⟨walkLength, walk_transpose_iff.mp walk⟩
  · rintro ⟨walkLength, walk⟩
    exact ⟨walkLength, walk_transpose_iff.mpr walk⟩

/-- **Semantic equivalence of directed adjacency graphs.** Two directed adjacency graphs $G_1$
and $G_2$ on the same vertex type are semantically equivalent when they have the same edges: for
all vertices $s$ and $t$, $G_1$ has an edge from $s$ to $t$ if and only if $G_2$ does. -/
def SemanticallyEquivalent (graph₁ graph₂ : DirectedAdjacency V) : Prop :=
  ∀ source target, graph₁.Edge source target ↔ graph₂.Edge source target

/-- **Semantic equivalence of directed adjacency graphs is reflexive.** Every directed adjacency
graph $G$ is semantically equivalent to itself. -/
@[refl]
theorem semanticEquivalent_refl : SemanticallyEquivalent graph graph := by
  intro source target
  rfl

/-- **Semantic equivalence of directed adjacency graphs is symmetric.** If a directed adjacency
graph $G_1$ is semantically equivalent to a directed adjacency graph $G_2$, then $G_2$ is
semantically equivalent to $G_1$. -/
@[symm]
theorem SemanticallyEquivalent.symm
    (equivalent : SemanticallyEquivalent graph₁ graph₂) :
    SemanticallyEquivalent graph₂ graph₁ := by
  intro source target
  exact (equivalent source target).symm

/-- **Semantic equivalence of directed adjacency graphs is transitive.** If a directed adjacency
graph $G_1$ is semantically equivalent to $G_2$, and $G_2$ is semantically equivalent to $G_3$,
then $G_1$ is semantically equivalent to $G_3$. -/
@[trans]
theorem SemanticallyEquivalent.trans
    (equivalent₁₂ : SemanticallyEquivalent graph₁ graph₂)
    (equivalent₂₃ : SemanticallyEquivalent graph₂ graph₃) :
    SemanticallyEquivalent graph₁ graph₃ := by
  intro source target
  exact (equivalent₁₂ source target).trans (equivalent₂₃ source target)

/-- **Semantically equivalent graphs have the same walks.** If two directed adjacency graphs
$G_1$ and $G_2$ are semantically equivalent, then for every natural number $n$ and all
vertices $s$ and $t$, there is a walk of length $n$ from $s$ to $t$ in $G_1$ if and only if
there is a walk of length $n$ from $s$ to $t$ in $G_2$. -/
theorem SemanticallyEquivalent.walk_iff
    (equivalent : SemanticallyEquivalent graph₁ graph₂) :
    Walk graph₁ length source target ↔ Walk graph₂ length source target := by
  constructor
  · exact Relation.RelatesInSteps.map id fun a b edge => (equivalent a b).mp edge
  · exact Relation.RelatesInSteps.map id fun a b edge => (equivalent a b).mpr edge

/-- **Semantically equivalent graphs have the same reachability.** If two directed adjacency
graphs $G_1$ and $G_2$ on $V$ are semantically equivalent, then for all $s, t \in V$, $t$ is
reachable from $s$ in $G_1$ if and only if $t$ is reachable from $s$ in $G_2$. -/
theorem SemanticallyEquivalent.reachable_iff
    (equivalent : SemanticallyEquivalent graph₁ graph₂) :
    graph₁.Reachable source target ↔ graph₂.Reachable source target := by
  simp only [reachable_iff_exists_walk, equivalent.walk_iff]

/-- **Transposition preserves semantic equivalence.** For directed adjacency graphs $G_1$ and
$G_2$ on a vertex type with decidable equality, if $G_1$ and $G_2$ are semantically
equivalent, then their transposes are semantically equivalent. -/
theorem SemanticallyEquivalent.transpose [DecidableEq V]
    (equivalent : SemanticallyEquivalent graph₁ graph₂) :
    SemanticallyEquivalent graph₁.transpose graph₂.transpose := by
  intro source target
  simp only [edge_transpose]
  exact equivalent target source

/-- **Transposing twice gives a semantically equivalent graph.** Let $G$ be a directed adjacency
graph on a vertex type with decidable equality. The transpose of the transpose of $G$ is
semantically equivalent to $G$, that is, it has exactly the same edges as $G$. -/
theorem semanticEquivalent_transpose_transpose [DecidableEq V] :
    SemanticallyEquivalent graph.transpose.transpose graph := by
  intro source target
  simp

/-- **Boolean edge test.** For a type $V$ with decidable equality, a directed adjacency graph
$G$ on $V$ and vertices $s, t \in V$, the edge test of $G$ at $(s, t)$ is the Boolean value
that is true exactly when $t$ occurs in the adjacency list of $s$. -/
public def hasEdge {α : Type u} [DecidableEq α]
    (g : DirectedAdjacency α) (source target : α) : Bool :=
  decide (target ∈ g.adjacency source)

/-- **The Boolean edge test is correct.** For a type $V$ with decidable equality, a directed
adjacency graph $G$ on $V$ and vertices $s, t \in V$, the Boolean edge test of $G$ at $(s, t)$
returns true if and only if $G$ has an edge from $s$ to $t$. -/
public theorem hasEdge_eq_true {α : Type u} [DecidableEq α]
    (g : DirectedAdjacency α) (source target : α) :
    g.hasEdge source target = true ↔ g.Edge source target := by
  simp [hasEdge, Edge]

end DirectedAdjacency

end Cslib.Algorithms.Lean
