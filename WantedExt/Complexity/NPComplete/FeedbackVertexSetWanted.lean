/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEEDBACK VERTEX SET is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), FEEDBACK VERTEX SET.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSet

/-!
# FEEDBACK VERTEX SET is NP-complete

An undirected graph and a bound `K`. The question is whether at most `K` vertices can be
removed to make the graph acyclic, stated with the canonical `SimpleGraph.IsAcyclic` predicate
on the remaining induced subgraph.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Instances of FEEDBACK VERTEX SET.** An instance of FEEDBACK VERTEX SET is a triple
$(n, es, K)$ of a natural number $n$ (the number of vertices), a list $es$ of pairs of natural
numbers (the edges) and a natural number $K$ (the bound). -/
abbrev FeedbackVertexSetInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- **Graph of a FEEDBACK VERTEX SET instance.** For an instance $(n, es, K)$ of FEEDBACK VERTEX
SET, its graph is the simple graph on $\{0, \dots, n-1\}$ in which distinct vertices $i$ and
$j$ are adjacent when $(i, j)$ or $(j, i)$ belongs to $es$. -/
def Graph (i : FeedbackVertexSetInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1


/-- **Well-formed FEEDBACK VERTEX SET instances.** An instance $(n, es, K)$ of FEEDBACK VERTEX
SET is well formed when the list $es$ has no repeated entries and every pair $(u, v)$ in $es$
satisfies $u < n$, $v < n$ and $u \ne v$, and $(v, u)$ does not belong to $es$. -/
def WellFormed (i : FeedbackVertexSetInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- **Feedback vertex sets within the bound.** An instance $(n, es, K)$ of FEEDBACK VERTEX SET is
feasible when there is a set $S$ of at most $K$ vertices of its graph such that the subgraph of
its graph induced on the vertices outside $S$ is acyclic. -/
def FeedbackVertexSetFeasible
    (i : FeedbackVertexSetInstance) : Prop :=
  ∃ S : Finset (Fin i.1), S.card ≤ i.2.2 ∧
    ((Graph i).induce (↑Sᶜ : Set (Fin i.1))).IsAcyclic

open Classical in
/-- **FEEDBACK VERTEX SET as a decision problem.** The decision problem FEEDBACK VERTEX SET
accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of
instances, to an instance of FEEDBACK VERTEX SET that is well formed and feasible. Bitstrings
that do not decode to an instance are rejected. -/
noncomputable def feedbackVertexSetDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FeedbackVertexSetInstance) x with
  | some i => decide (WellFormed i ∧ FeedbackVertexSetFeasible i)
  | none => false

/-- **FEEDBACK VERTEX SET is NP-complete.** The decision problem FEEDBACK VERTEX SET belongs to
NP, and every decision problem in NP reduces to FEEDBACK VERTEX SET by a polynomial-time
many-one reduction.

Source: M. R. Garey and D. S. Johnson, *Computers
and Intractability* (1979), FEEDBACK VERTEX SET. -/
public theorem_wanted feedbackVertexSet_npComplete :
    feedbackVertexSetDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L feedbackVertexSetDec

end MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSet
