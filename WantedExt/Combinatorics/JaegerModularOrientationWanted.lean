/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Jaeger's modular orientation conjecture
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.ZMod.Basic

@[expose] public section

namespace MathlibExt.Combinatorics.JaegerModularOrientationWanted

/-! Source record `OPG-130`.

We represent a finite undirected multigraph by finite types of vertices and edges together with
two endpoint maps. The endpoint order is only a reference orientation: `isReversed` below chooses
an orientation independently for each edge. This representation allows parallel edges and loops.
-/

/-- **Edges crossing a cut.** Consider a multigraph with vertex set $V$ and edge set $E$ in which
each edge has a first and a second endpoint. For a set $S \subseteq V$, an edge crosses the cut at
$S$ when exactly one of its two endpoints lies in $S$. -/
def CrossesCut {V E : Type} (end₁ end₂ : E → V) (S : Set V) (e : E) : Prop :=
  (end₁ e ∈ S ∧ end₂ e ∉ S) ∨ (end₁ e ∉ S ∧ end₂ e ∈ S)

/-- **Size of a cut.** Consider a multigraph with finitely many edges in which each edge has a
first and a second endpoint. For a set $S$ of vertices, the size of the cut at $S$ is the number
of edges crossing it, that is, having exactly one endpoint in $S$. Distinct parallel edges are
counted separately. -/
noncomputable def cutSize {V E : Type} [Fintype E]
    (end₁ end₂ : E → V) (S : Set V) : ℕ := by
  classical
  exact (Finset.univ.filter (CrossesCut end₁ end₂ S)).card

/-- **4k-edge-connected multigraphs.** For a natural number $k$, a finite multigraph is
$4k$-edge-connected when it has at least two vertices and, for every set $S$ of vertices such that
both $S$ and its complement are nonempty, at least $4k$ edges cross the cut at $S$, that is, have
exactly one endpoint in $S$. Parallel edges are counted separately. For $k \ge 1$ the condition
implies that the multigraph is connected.
-/
noncomputable def IsFourKEdgeConnected {V E : Type} [Fintype V] [Fintype E]
    (k : ℕ) (end₁ end₂ : E → V) : Prop :=
  2 ≤ Fintype.card V ∧
    ∀ S : Set V, S.Nonempty → Sᶜ.Nonempty → 4 * k ≤ cutSize end₁ end₂ S

/-- **Tail of an oriented edge.** Each edge $e$ of the multigraph has a reference direction from
its first endpoint to its second endpoint, and an orientation chooses for each edge whether to
reverse it. The tail of $e$ is its first endpoint if $e$ is not reversed and its second endpoint
if $e$ is reversed. -/
def orientedTail {V E : Type} (end₁ end₂ : E → V)
    (isReversed : E → Bool) (e : E) : V :=
  if isReversed e = true then end₂ e else end₁ e

/-- **Head of an oriented edge.** Each edge $e$ of the multigraph has a reference direction from
its first endpoint to its second endpoint, and an orientation chooses for each edge whether to
reverse it. The head of $e$ is its second endpoint if $e$ is not reversed and its first endpoint
if $e$ is reversed. -/
def orientedHead {V E : Type} (end₁ end₂ : E → V)
    (isReversed : E → Bool) (e : E) : V :=
  if isReversed e = true then end₁ e else end₂ e

/-- **Indegree.** In a multigraph with finitely many edges and a chosen orientation, the
indegree of a vertex $v$ is the number of edges whose head is $v$, parallel edges counted
separately. -/
noncomputable def indegree {V E : Type} [Fintype E]
    (end₁ end₂ : E → V) (isReversed : E → Bool) (v : V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun e => orientedHead end₁ end₂ isReversed e = v)).card

/-- **Outdegree.** In a multigraph with finitely many edges and a chosen orientation, the
outdegree of a vertex $v$ is the number of edges whose tail is $v$, parallel edges counted
separately. -/
noncomputable def outdegree {V E : Type} [Fintype E]
    (end₁ end₂ : E → V) (isReversed : E → Bool) (v : V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun e => orientedTail end₁ end₂ isReversed e = v)).card

/-- **Modular orientations.** For a natural number $k$, an orientation of a multigraph with
finitely many edges is a modulo $(2k+1)$ orientation when at every vertex the indegree minus the
outdegree is congruent to $0$ modulo $2k + 1$. -/
noncomputable def IsModularOrientation {V E : Type} [Fintype E]
    (k : ℕ) (end₁ end₂ : E → V) (isReversed : E → Bool) : Prop :=
  ∀ v : V,
    (indegree end₁ end₂ isReversed v : ZMod (2 * k + 1)) -
        (outdegree end₁ end₂ isReversed v : ZMod (2 * k + 1)) = 0

/-- **Jaeger's modular orientation conjecture.** This is the statement that for every integer
$k \ge 1$, every finite multigraph (loops and parallel edges allowed) that has at least two
vertices, and in which every partition of the vertices into two nonempty sets is crossed by at
least $4k$ edges, admits an orientation of its edges in which, at every vertex, the indegree minus
the outdegree is divisible by $2k + 1$.

The parameter $k$ is positive, as in the source discussion of $(2 + 1/k)$-flows and its
specializations at $k = 1$ and $k = 2$.
-/
def conjecture : Prop :=
  ∀ (k : ℕ), 0 < k →
    ∀ (V E : Type) [Fintype V] [Fintype E] (end₁ end₂ : E → V),
      IsFourKEdgeConnected k end₁ end₂ →
        ∃ isReversed : E → Bool, IsModularOrientation k end₁ end₂ isReversed

/-- **Jaeger's modular orientation conjecture is false.** There exist an integer $k \ge 1$ and a
finite multigraph (loops and parallel edges allowed) with at least two vertices, in which every
partition of the vertices into two nonempty sets is crossed by at least $4k$ edges, such that no
orientation of the edges makes the indegree minus the outdegree of every vertex divisible by
$2k + 1$.

Han, Li, Wu and Zhang (J. Combin. Theory Ser. B 131 (2018) 1-11) construct, for every $k \ge 3$,
a $4k$-edge-connected graph with no circular $(2+1/k)$-flow, equivalently no modulo $(2k+1)$
orientation; the cases $k = 1$ (Tutte's 3-flow conjecture) and $k = 2$ remain open.

Source: Daniel W. Cranston and Jiaao Li, Circular flows in planar graphs, SIAM J. Discrete
Math. (2020), arXiv:1812.09833, https://arxiv.org/abs/1812.09833. Moved from
`OpenConjectures/Combinatorics/JaegerModularOrientation`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.Combinatorics.JaegerModularOrientationWanted
