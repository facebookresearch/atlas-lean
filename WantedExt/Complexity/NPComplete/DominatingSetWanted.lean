/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMINATING SET is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), DOMINATING SET.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DominatingSet

/-!
# DOMINATING SET is NP-complete

An undirected graph and a bound `K`. The question is whether some set of at most `K` vertices
dominates the graph: every vertex is in the set or adjacent to a vertex in the set.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Instances of DOMINATING SET.** An instance of DOMINATING SET is a triple $(n, E, K)$ of a
natural number $n$ (the number of vertices), a list $E$ of pairs of natural numbers (the edges)
and a natural number $K$ (the bound). -/
abbrev DominatingSetInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- **Graph of a DOMINATING SET instance.** For an instance $(n, E, K)$ of DOMINATING SET, its
graph is the simple graph on $\{0, \dots, n - 1\}$ in which distinct vertices $i$ and $j$ are
adjacent when $(i, j)$ or $(j, i)$ belongs to $E$. -/
def Graph (i : DominatingSetInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1


/-- **Well-formed DOMINATING SET instances.** An instance $(n, E, K)$ of DOMINATING SET is well
formed when the list $E$ has no repeated entries and every pair $(u, v) \in E$ satisfies $u < n$,
$v < n$, $u \ne v$ and $(v, u) \notin E$. -/
def WellFormed (i : DominatingSetInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- **Feasibility of a DOMINATING SET instance.** An instance $(n, E, K)$ of DOMINATING SET is
feasible when there is a set $S$ of at most $K$ vertices of its graph such that every vertex lies in
$S$ or is adjacent to a vertex of $S$, where the graph has vertex set $\{0, \dots, n - 1\}$ and
distinct vertices $i$ and $j$ are adjacent when $(i, j)$ or $(j, i)$ belongs to $E$. -/
def DominatingSetFeasible
    (i : DominatingSetInstance) : Prop :=
  ∃ S : Finset (Fin i.1), S.card ≤ i.2.2 ∧
    ∀ v : Fin i.1, v ∈ S ∨ ∃ u ∈ S, (Graph i).Adj u v

open Classical in
/-- **DOMINATING SET as a decision problem.** The decision problem DOMINATING SET accepts a
bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding, to a triple
$(n, E, K)$ of a natural number $n$, a list $E$ of pairs of natural numbers and a natural number
$K$ such that $E$ has no repeated entries, every pair $(u, v) \in E$ satisfies $u < n$, $v < n$,
$u \ne v$ and $(v, u) \notin E$, and there is a set $S$ of at most $K$ vertices with every vertex
in $S$ or adjacent to a vertex of $S$, in the graph on $\{0, \dots, n - 1\}$ where distinct $i$
and $j$ are adjacent when $(i, j)$ or $(j, i)$ belongs to $E$. Bitstrings that do not decode are
rejected. -/
noncomputable def dominatingSetDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ DominatingSetFeasible i)
  | none => false

/-- **DOMINATING SET is NP-complete.** The decision problem DOMINATING SET belongs to NP, and
every decision problem in NP reduces to DOMINATING SET by a polynomial-time many-one reduction.

Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), DOMINATING SET. -/
public theorem_wanted dominatingSet_npComplete :
    dominatingSetDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L dominatingSetDec

end MetaMathlibExt.Complexity.NPComplete.DominatingSet
