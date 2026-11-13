/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Data.Real.Basic

/-!
# `C`-expanders

Formalizes Definition 1 of Michael Krivelevich, Alan Lew, and Peleg Michaeli,
*Rigidity of expanders and pseudorandom graphs*,
https://arxiv.org/abs/2608.21058v1.

For `C > 0`, an `n`-vertex graph is a `C`-expander when every small vertex set
expands by a factor `C` and any two large disjoint vertex sets have an edge
between them.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- **External neighbourhood.** For a simple graph $G$ on a vertex set $V$ and a set
$A \subseteq V$, the external neighbourhood of $A$ in $G$ is the set of vertices $v \notin A$
that are adjacent in $G$ to some vertex of $A$. -/
def externalNeighborSet (A : Set V) : Set V :=
  { v | v ∉ A ∧ ∃ a ∈ A, G.Adj a v }

/-- **Membership in the external neighbourhood.** Let $G$ be a simple graph on a vertex set
$V$, let $A \subseteq V$ and let $v \in V$. Then $v$ lies in the external neighbourhood of $A$
in $G$ if and only if $v \notin A$ and $v$ is adjacent in $G$ to some vertex $a \in A$. -/
@[simp]
theorem mem_externalNeighborSet (A : Set V) (v : V) :
    v ∈ G.externalNeighborSet A ↔ v ∉ A ∧ ∃ a ∈ A, G.Adj a v :=
  Iff.rfl

/-- **The external neighbourhood is disjoint from the set.** For every simple graph $G$ on a
vertex set $V$ and every set $A \subseteq V$, the external neighbourhood of $A$ in $G$ is
disjoint from $A$. -/
theorem externalNeighborSet_disjoint (A : Set V) :
    Disjoint (G.externalNeighborSet A) A := by
  rw [Set.disjoint_left]
  intro v hv hA
  exact hv.1 hA

/-- **External neighbours have a neighbour in the set.** Let $G$ be a simple graph on a vertex
set $V$ and let $A \subseteq V$. If $v$ is an external neighbour of $A$ in $G$, then $v$ is
adjacent in $G$ to some vertex $a \in A$. -/
theorem exists_adj_of_mem_externalNeighborSet {A : Set V} {v : V}
    (h : v ∈ G.externalNeighborSet A) : ∃ a ∈ A, G.Adj a v :=
  h.2

/-- **C-expander.** Let $G$ be a simple graph on a finite vertex set $V$ with $n$ vertices, and
let $C$ be a real number. Then $G$ is a $C$-expander if $C > 0$, every set $A \subseteq V$
with $|A| < n/(2C)$ has an external neighbourhood in $G$ with at least $C|A|$ vertices, and
for any two disjoint sets $A, B \subseteq V$ with $|A| \ge n/(2C)$ and $|B| \ge n/(2C)$ some
vertex of $A$ is adjacent in $G$ to some vertex of $B$.

Source: Krivelevich, Lew and Michaeli, *Rigidity of expanders and pseudorandom graphs*,
Definition 1. -/
def IsCExpander [Finite V] (C : ℝ) : Prop :=
  0 < C ∧
    (∀ A : Set V, (A.ncard : ℝ) < (Nat.card V : ℝ) / (2 * C) →
      C * (A.ncard : ℝ) ≤ ((G.externalNeighborSet A).ncard : ℝ)) ∧
    ∀ A B : Set V, Disjoint A B →
      (Nat.card V : ℝ) / (2 * C) ≤ (A.ncard : ℝ) →
      (Nat.card V : ℝ) / (2 * C) ≤ (B.ncard : ℝ) →
      ∃ a ∈ A, ∃ b ∈ B, G.Adj a b

/-- **The parameter of a C-expander is positive.** Let $G$ be a simple graph on a finite vertex
set $V$ and let $C$ be a real number. If $G$ is a $C$-expander, then $C > 0$. -/
theorem IsCExpander.pos [Finite V] {C : ℝ} (h : G.IsCExpander C) : 0 < C :=
  h.1

/-- **Small sets expand in a $C$-expander.** Let $C$ be a real number and let $G$ be a
$C$-expander on a finite vertex set $V$. Then every set $A \subseteq V$ with $|A| < |V|/(2C)$ has
at least $C|A|$ external neighbours, that is, at least $C|A|$ vertices outside $A$ are adjacent to
some vertex of $A$. -/
theorem IsCExpander.small_expansion [Finite V] {C : ℝ} (h : G.IsCExpander C)
    (A : Set V) (hA : (A.ncard : ℝ) < (Nat.card V : ℝ) / (2 * C)) :
    C * (A.ncard : ℝ) ≤ ((G.externalNeighborSet A).ncard : ℝ) :=
  h.2.1 A hA

/-- **Large disjoint sets in a C-expander span an edge.** Let $G$ be a simple graph on a finite
vertex set $V$ with $n$ vertices, let $C$ be a real number, and suppose $G$ is a $C$-expander.
If $A, B \subseteq V$ are disjoint sets with $|A| \ge n/(2C)$ and $|B| \ge n/(2C)$, then some
vertex $a \in A$ is adjacent in $G$ to some vertex $b \in B$. -/
theorem IsCExpander.large_edge [Finite V] {C : ℝ} (h : G.IsCExpander C)
    (A B : Set V) (hdis : Disjoint A B)
    (hA : (Nat.card V : ℝ) / (2 * C) ≤ (A.ncard : ℝ))
    (hB : (Nat.card V : ℝ) / (2 * C) ≤ (B.ncard : ℝ)) :
    ∃ a ∈ A, ∃ b ∈ B, G.Adj a b :=
  h.2.2 A B hdis hA hB

/-- **Uniform vertex expander.** Let $G$ be a simple graph on a finite vertex set $V$ and let
$h$ be a real number. Then $G$ is a uniform vertex expander with parameter $h$ if $h > 0$ and
every set $S \subseteq V$ with $|S| \le |V|/2$ has an external neighbourhood in $G$ with at
least $h|S|$ vertices. -/
def IsUniformVertexExpander [Finite V] (h : ℝ) : Prop :=
  0 < h ∧
    ∀ S : Set V, (S.ncard : ℝ) ≤ (Nat.card V : ℝ) / 2 →
      h * (S.ncard : ℝ) ≤ ((G.externalNeighborSet S).ncard : ℝ)

/-- **The parameter of a uniform vertex expander is positive.** Let $G$ be a simple graph on a
finite vertex set $V$ and let $h$ be a real number. If $G$ is a uniform vertex expander with
parameter $h$, then $h > 0$. -/
theorem IsUniformVertexExpander.pos [Finite V] {h : ℝ}
    (hh : G.IsUniformVertexExpander h) : 0 < h :=
  hh.1

/-- **Small sets expand in a uniform vertex expander.** Let $G$ be a simple graph on a finite
vertex set $V$ and let $h$ be a real number. If $G$ is a uniform vertex expander with parameter
$h$ and $S \subseteq V$ satisfies $|S| \le |V|/2$, then the external neighbourhood of $S$ in
$G$ has at least $h|S|$ vertices. -/
theorem IsUniformVertexExpander.small_expansion [Finite V] {h : ℝ}
    (hh : G.IsUniformVertexExpander h)
    (S : Set V) (hS : (S.ncard : ℝ) ≤ (Nat.card V : ℝ) / 2) :
    h * (S.ncard : ℝ) ≤ ((G.externalNeighborSet S).ncard : ℝ) :=
  hh.2 S hS

end SimpleGraph
