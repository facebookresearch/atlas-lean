/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ODD CYCLE TRANSVERSAL is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), ODD CYCLE TRANSVERSAL
(vertex deletion to a bipartite graph).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Bipartite

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OddCycleTransversal

/-!
# ODD CYCLE TRANSVERSAL is NP-complete

An undirected graph and a bound `K`. The question is whether at most `K` vertices can be
removed to make the graph bipartite, witnessed by a two-coloring of the remaining vertices.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Odd cycle transversal instances.** An odd cycle transversal instance is a triple
$(n, es, K)$ of a natural number $n$ (the number of vertices), a list $es$ of pairs of natural
numbers (the edges) and a natural number $K$ (the bound on the number of removed vertices). -/
abbrev OddCycleTransversalInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- **Graph of an odd cycle transversal instance.** For an odd cycle transversal instance
$(n, es, K)$, its graph is the graph of the edge list $es$ on $n$ vertices: the simple graph on
$\{0, \dots, n-1\}$ in which distinct vertices $i$ and $j$ are adjacent when $(i, j)$ or $(j, i)$
belongs to $es$. -/
def Graph (i : OddCycleTransversalInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1


/-- **Well-formed odd cycle transversal instances.** An odd cycle transversal instance
$(n, es, K)$ is well formed when the list $es$ has no repeated entries and every pair $(u, v)$ in
$es$ satisfies $u < n$, $v < n$ and $u \ne v$, and $(v, u)$ does not belong to $es$. -/
def WellFormed (i : OddCycleTransversalInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- **Feasible odd cycle transversal instances.** An odd cycle transversal instance $(n, es, K)$
is feasible when there is a set $S$ of at most $K$ vertices of its graph such that the subgraph
induced on the vertices outside $S$ is bipartite. -/
def OddCycleTransversalFeasible
    (i : OddCycleTransversalInstance) : Prop :=
  ∃ S : Finset (Fin i.1), S.card ≤ i.2.2 ∧
    ((Graph i).induce (↑Sᶜ : Set (Fin i.1))).IsBipartite

open Classical in
/-- **ODD CYCLE TRANSVERSAL as a decision problem.** The decision problem ODD CYCLE TRANSVERSAL
accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding, to an
odd cycle transversal instance $(n, es, K)$ that is well formed and feasible. Well formed means
that $es$ has no repeated entries and every pair $(u, v)$ in $es$ satisfies $u < n$, $v < n$,
$u \ne v$ and $(v, u) \notin es$; feasible means that some set of at most $K$ vertices can be
removed from the graph of the instance so that the remaining induced subgraph is bipartite.
Bitstrings that do not decode to an instance are rejected. -/
noncomputable def oddCycleTransversalDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := OddCycleTransversalInstance) x with
  | some i => decide (WellFormed i ∧ OddCycleTransversalFeasible i)
  | none => false

/-- **ODD CYCLE TRANSVERSAL is NP-complete.** The decision problem ODD CYCLE TRANSVERSAL, which
accepts a bitstring exactly when it decodes to a well-formed instance $(n, es, K)$ whose graph
becomes bipartite after removing some set of at most $K$ vertices, belongs to NP, and every
decision problem in NP has a polynomial-time many-one reduction to it.

Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), ODD CYCLE TRANSVERSAL (vertex deletion to a
bipartite graph). -/
public theorem_wanted oddCycleTransversal_npComplete :
    oddCycleTransversalDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L oddCycleTransversalDec

end MetaMathlibExt.Complexity.NPComplete.OddCycleTransversal
