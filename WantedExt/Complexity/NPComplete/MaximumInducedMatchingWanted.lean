/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM INDUCED MATCHING is NP-complete

Source:
L. J. Stockmeyer and V. V. Vazirani, "NP-completeness of some generalizations of the maximum
matching problem", Information Processing Letters 15 (1982), 14-19; K. Cameron, "Induced
matchings", Discrete Applied Mathematics 24 (1989), 97-102 (NP-completeness for bipartite
graphs, polynomial for chordal graphs).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumInducedMatching

/-!
# MAXIMUM INDUCED MATCHING is NP-complete

An undirected graph and a bound `K`. The question is whether the graph has an induced matching
of at least `K` edges: a set of pairwise disjoint edges with no edge of the graph joining two
different matched edges.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Maximum-induced-matching instances.** A maximum-induced-matching instance is a triple
$(n, E, K)$ of a natural number $n$ (the vertex count), a list $E$ of pairs of natural numbers
(the edges) and a natural number $K$ (the bound). -/
abbrev MaximumInducedMatchingInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- **Well-formed maximum-induced-matching instances.** A maximum-induced-matching instance
$(n, E, K)$ is well formed when the edge list $E$ has no repeated entries and every pair $(u, v)$
in $E$ satisfies $u < n$, $v < n$ and $u \ne v$, with the reverse pair $(v, u)$ not in $E$. -/
def WellFormed (i : MaximumInducedMatchingInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- **Feasible maximum-induced-matching instances.** A maximum-induced-matching instance
$(n, E, K)$, with vertex count $n$, edge list $E$ of pairs of natural numbers and bound $K$, is
feasible when there is a sublist $M$ of $E$ of length at least $K$ such that any two distinct
pairs in $M$ share no endpoint, and no pair in $E$ joins an endpoint of one pair in $M$ to an
endpoint of a different pair in $M$. -/
def MaximumInducedMatchingFeasible
    (i : MaximumInducedMatchingInstance) : Prop :=
  ∃ M : List (ℕ × ℕ), M.Sublist i.2.1 ∧ i.2.2 ≤ M.length ∧
    (∀ e1 ∈ M, ∀ e2 ∈ M, e1 ≠ e2 →
      e1.1 ≠ e2.1 ∧ e1.1 ≠ e2.2 ∧ e1.2 ≠ e2.1 ∧ e1.2 ≠ e2.2) ∧
    ∀ e ∈ i.2.1, ∀ e1 ∈ M, ∀ e2 ∈ M, e1 ≠ e2 →
      ¬ ((e.1 = e1.1 ∨ e.1 = e1.2) ∧ (e.2 = e2.1 ∨ e.2 = e2.2) ∨
        (e.2 = e1.1 ∨ e.2 = e1.2) ∧ (e.1 = e2.1 ∨ e.1 = e2.2))

open Classical in
/-- **The MAXIMUM INDUCED MATCHING decision problem.** MAXIMUM INDUCED MATCHING is the decision
problem that accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring
encoding, to a maximum-induced-matching instance $(n, E, K)$ that is well formed and feasible:
the edge list $E$ has no repeated entries, every pair $(u, v)$ in $E$ satisfies $u < n$, $v < n$
and $u \ne v$ with $(v, u)$ not in $E$, and some sublist $M$ of $E$ of length at least $K$ is an
induced matching, meaning that any two distinct pairs in $M$ share no endpoint and no pair in $E$
joins an endpoint of one pair in $M$ to an endpoint of a different pair in $M$. Bitstrings that
do not decode are rejected. -/
noncomputable def maximumInducedMatchingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaximumInducedMatchingInstance) x with
  | some i => decide (WellFormed i ∧ MaximumInducedMatchingFeasible i)
  | none => false

/-- **MAXIMUM INDUCED MATCHING is NP-complete.** The MAXIMUM INDUCED MATCHING decision problem
belongs to NP, and every decision problem in NP reduces to it by a polynomial-time many-one
reduction.

Source: L. J. Stockmeyer and V. V. Vazirani,
"NP-completeness of some generalizations of the maximum matching problem", Information
Processing Letters 15 (1982), 14-19; K. Cameron, "Induced matchings", Discrete Applied
Mathematics 24 (1989), 97-102 (NP-completeness for bipartite graphs, polynomial for
chordal graphs). -/
public theorem_wanted maximumInducedMatching_npComplete :
    maximumInducedMatchingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maximumInducedMatchingDec

end MetaMathlibExt.Complexity.NPComplete.MaximumInducedMatching
