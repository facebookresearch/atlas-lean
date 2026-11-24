/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Petersen coloring conjecture
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.SimpleGraph.Bridgeless
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Set.Card
public import Mathlib.Data.ZMod.Basic

@[expose] public section

namespace MathlibExt.GraphTheory.PetersenColoringConjectureWanted

/-! Source record `OPG-143` (UnsolvedMath numeric id `3196`).

Graphs are finite simple graphs, so parallel edges are excluded from the model
(see the registry adequacy gaps). The `Bool` layer `false` is the outer 5-cycle
(`i -- i+1`) and the `Bool` layer `true` is the inner 5-star (`i -- i+2`),
joined by the spokes `(i, false) -- (i, true)`. Since `1 ≠ 0` and `2 ≠ 0` in
`ZMod 5`, every generator below joins distinct vertices, so the edge set is
loop-free and `SimpleGraph.fromEdgeSet` retains all of it.

This Petersen representation is intentionally distinct from
`PetersenMinorFourFlow.PetersenAdj`: that entry models branch sets in a host
multigraph (tail/head edges, `Sum (ZMod 5) (ZMod 5)` vertices), while a
Petersen coloring maps edges between simple graphs, so this entry uses a
`SimpleGraph` on `ZMod 5 × Bool` with incidence via `SimpleGraph.incidenceSet`.
Bridgelessness uses the canonical `SimpleGraph.IsBridgeless` predicate.
-/

/-- **Vertices of the Petersen graph.** The vertex set of the Petersen graph is
$\mathbb{Z}/5\mathbb{Z} \times \{\mathrm{false}, \mathrm{true}\}$; the vertices
$(i, \mathrm{false})$ with $i \in \mathbb{Z}/5\mathbb{Z}$ form the outer 5-cycle and the vertices
$(i, \mathrm{true})$ form the inner 5-star. -/
abbrev PVertex := ZMod 5 × Bool

/-- **Edges of the Petersen graph.** The edge set of the Petersen graph on
$\mathbb{Z}/5\mathbb{Z} \times \{\mathrm{false}, \mathrm{true}\}$ consists of the unordered
pairs $\{(i, \mathrm{false}), (i + 1, \mathrm{false})\}$ (the outer 5-cycle),
$\{(i, \mathrm{false}), (i, \mathrm{true})\}$ (the spokes) and
$\{(i, \mathrm{true}), (i + 2, \mathrm{true})\}$ (the inner 5-star), for
$i \in \mathbb{Z}/5\mathbb{Z}$. -/
def petersenEdgeSet : Set (Sym2 PVertex) :=
  {e | ∃ i : ZMod 5, e = s((i, false), (i + 1, false))} ∪
    {e | ∃ i : ZMod 5, e = s((i, false), (i, true))} ∪
      {e | ∃ i : ZMod 5, e = s((i, true), (i + 2, true))}

/-- **Petersen graph.** The Petersen graph is the simple graph on
$\mathbb{Z}/5\mathbb{Z} \times \{\mathrm{false}, \mathrm{true}\}$ whose edges are the outer
5-cycle edges $\{(i, \mathrm{false}), (i + 1, \mathrm{false})\}$, the spokes
$\{(i, \mathrm{false}), (i, \mathrm{true})\}$ and the inner 5-star edges
$\{(i, \mathrm{true}), (i + 2, \mathrm{true})\}$ for $i \in \mathbb{Z}/5\mathbb{Z}$. -/
def petersenGraph : SimpleGraph PVertex := SimpleGraph.fromEdgeSet petersenEdgeSet

/-- **Petersen coloring.** Let $G$ be a simple graph on a vertex type $V$ and let $P$ be the
Petersen graph. A map $f$ from unordered pairs of vertices of $G$ to unordered pairs of vertices
of $P$ is a Petersen coloring of $G$ when $f$ sends every edge of $G$ to an edge of $P$ and, for
every vertex $v$ of $G$, there is a vertex $w$ of $P$ such that $f$ maps the set of edges of $G$
incident to $v$ bijectively onto the set of edges of $P$ incident to $w$. -/
def IsPetersenColoring {V : Type*} (G : SimpleGraph V)
    (f : Sym2 V → Sym2 PVertex) : Prop :=
  (∀ e ∈ G.edgeSet, f e ∈ petersenGraph.edgeSet) ∧
    ∀ v : V, ∃ w : PVertex,
      Set.BijOn f (G.incidenceSet v) (petersenGraph.incidenceSet w)

/-- **Petersen coloring conjecture.** For every finite vertex type $V$ and every simple graph $G$
on $V$, if every vertex of $G$ has exactly three neighbors and $G$ is bridgeless, then $G$ admits
a Petersen coloring. -/
def conjecture : Prop :=
  ∀ (V : Type) [Finite V] (G : SimpleGraph V),
    (∀ v, (G.neighborSet v).ncard = 3) → G.IsBridgeless →
      ∃ f : Sym2 V → Sym2 PVertex, IsPetersenColoring G f

/-- **The Petersen coloring conjecture is false.** There are a finite vertex type $V$ and a
simple graph $G$ on $V$ in which every vertex has exactly three neighbors and no edge is a bridge,
such that $G$ has no Petersen coloring: no map $f$ from unordered pairs of vertices of $G$ to
unordered pairs of vertices of the Petersen graph $P$ sends every edge of $G$ to an edge of $P$
and, for every vertex $v$ of $G$, maps the edges of $G$ at $v$ bijectively onto the edges of $P$
at some vertex $w$ of $P$.

Putman (arXiv:2608.10012, Aug 2026) gave 112-vertex counterexamples with SAT/DRAT certificates,
and Goedgebeur, Jooken, Macajova, Mattiolo, Mazzuoccolo and Ulyanov (arXiv:2608.10028,
Theorem 6) prove two simple bridgeless cubic 52-vertex graphs have no Petersen colouring.

Source: Jan Goedgebeur, Jorik Jooken, Edita
Macajova, Davide Mattiolo, Giuseppe Mazzuoccolo and Nikolay Ulyanov, Disproving the Petersen
Coloring Conjecture: Theoretical Analysis and an Infinite Family of Counterexamples, arXiv
preprint (2026), arXiv:2608.10028, https://arxiv.org/abs/2608.10028; Bryce Putman, A 112-Vertex
Counterexample to the Petersen Coloring Conjecture, arXiv preprint (2026), arXiv:2608.10012,
https://arxiv.org/abs/2608.10012. Moved from
`OpenConjectures/GraphTheory/PetersenColoringConjecture`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.GraphTheory.PetersenColoringConjectureWanted
