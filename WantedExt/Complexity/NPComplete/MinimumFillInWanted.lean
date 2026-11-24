/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM FILL-IN (CHORDAL COMPLETION) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), MINIMUM FILL-IN; M.
Yannakakis, "Computing the minimum fill-in is NP-complete" (1981).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumFillIn

/-!
# MINIMUM FILL-IN (CHORDAL COMPLETION) is NP-complete

An undirected graph and a bound `K`. The question is whether at most `K` edges can be added so
that the resulting graph is chordal, witnessed by a perfect elimination ordering: a vertex
ordering in which, for every vertex, its later neighbors form a clique in the augmented graph.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Instances of MINIMUM FILL-IN.** An instance of MINIMUM FILL-IN is a triple $(n, E, K)$
consisting of a natural number $n$ (the number of vertices), a list $E$ of pairs of natural
numbers (the edge list) and a natural number $K$ (the bound). -/
abbrev MinimumFillInInstance := ℕ × List (ℕ × ℕ) × ℕ


/-- **Graph augmented by added edges.** For an instance $(n, E, K)$ of MINIMUM FILL-IN and a
list $A$ of pairs of natural numbers, the augmented graph is the graph of the edge list $E$
followed by $A$ on $n$ vertices: the simple graph on $\{0, \dots, n - 1\}$ in which distinct
vertices $i$ and $j$ are adjacent when $(i, j)$ or $(j, i)$ belongs to $E$ or to $A$. -/
def GraphAug (i : MinimumFillInInstance) (added : List (ℕ × ℕ)) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 (i.2.1 ++ added)


/-- **Well-formed MINIMUM FILL-IN instances.** An instance $(n, E, K)$ of MINIMUM FILL-IN is well
formed when the list $E$ has no repeated entries and every pair $(u, v)$ in $E$ satisfies
$u < n$, $v < n$ and $u \ne v$, and its reverse $(v, u)$ does not belong to $E$. -/
def WellFormed (i : MinimumFillInInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- **Feasible MINIMUM FILL-IN instances.** An instance $(n, E, K)$ of MINIMUM FILL-IN is
feasible when there are an ordering $\sigma$ of the vertices $0, \dots, n - 1$ (a list that
contains each of them exactly once) and a list $A$ of pairs of natural numbers, with no repeated
entries and at most $K$ entries, such that every pair $(u, v)$ in $A$ satisfies $u < n$, $v < n$
and $u \ne v$, neither $(u, v)$ nor $(v, u)$ belongs to $E$, and $(v, u)$ does not belong to $A$,
and such that, in the graph augmented by $A$, any two distinct vertices $a$ and $b$ that are both
adjacent to a vertex $v$ and both come after $v$ in $\sigma$ are adjacent to each other.

The ordering $\sigma$ is thus a perfect elimination ordering of the augmented graph, so adding
the at most $K$ edges of $A$ to the graph makes it chordal. -/
def MinimumFillInFeasible
    (i : MinimumFillInInstance) : Prop :=
  ∃ ord : List (Fin i.1), ord.Perm (List.finRange i.1) ∧
    ∃ added : List (ℕ × ℕ), added.Nodup ∧ added.length ≤ i.2.2 ∧
      (∀ e ∈ added, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ added ∧
        (e.2, e.1) ∉ i.2.1 ∧ e ∉ i.2.1) ∧
      ∀ v a b : Fin i.1, a ≠ b → ord.idxOf v < ord.idxOf a →
        ord.idxOf v < ord.idxOf b → (GraphAug i added).Adj v a →
        (GraphAug i added).Adj v b → (GraphAug i added).Adj a b

open Classical in
/-- **The MINIMUM FILL-IN (CHORDAL COMPLETION) problem.** The decision problem MINIMUM FILL-IN
accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding, to an
instance $(n, E, K)$ of MINIMUM FILL-IN that is well formed and feasible. -/
noncomputable def minimumFillInDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumFillInInstance) x with
  | some i => decide (WellFormed i ∧ MinimumFillInFeasible i)
  | none => false

/-- **MINIMUM FILL-IN (CHORDAL COMPLETION) is NP-complete.** The decision problem
MINIMUM FILL-IN lies in NP, and every decision problem in NP has a polynomial-time many-one
reduction to MINIMUM FILL-IN.

Source: M. R. Garey and D. S.
Johnson, *Computers and Intractability* (1979), MINIMUM FILL-IN; M. Yannakakis, "Computing
the minimum fill-in is NP-complete" (1981). -/
public theorem_wanted minimumFillIn_npComplete :
    minimumFillInDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumFillInDec

end MetaMathlibExt.Complexity.NPComplete.MinimumFillIn
