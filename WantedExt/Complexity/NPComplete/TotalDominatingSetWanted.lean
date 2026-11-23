/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TOTAL DOMINATING SET is NP-complete

Source:
E. J. Cockayne, R. M. Dawes, and S. T. Hedetniemi, "Total domination in graphs", Networks 10
(1980), 211-219; R. Laskar, J. Pfaff, S. M. Hedetniemi, and S. T. Hedetniemi, "On the
algorithmic complexity of total domination", SIAM Journal on Algebraic and Discrete Methods 5
(1984), 420-425.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TotalDominatingSet

/-!
# TOTAL DOMINATING SET is NP-complete

An undirected graph and a bound `K`. The question is whether some set `S` of at most `K`
vertices totally dominates the graph: every vertex, including those in `S`, has a neighbor in
`S` (open-neighborhood domination). An isolated vertex makes the instance a no-instance.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Instances of TOTAL DOMINATING SET.** An instance of TOTAL DOMINATING SET is a triple
$(n, E, K)$ consisting of a natural number $n$, the number of vertices, a list $E$ of pairs of
natural numbers, the edges, and a natural number $K$, the bound. -/
abbrev TotalDominatingSetInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- **Graph of a total dominating set instance.** The graph of an instance $(n, E, K)$ of TOTAL
DOMINATING SET is the simple graph on $\{0, \dots, n-1\}$ in which distinct vertices $i$ and $j$
are adjacent when $(i, j)$ or $(j, i)$ belongs to $E$. Loops are dropped, and pairs with an
endpoint at least $n$ contribute no edge. -/
def Graph (i : TotalDominatingSetInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1


/-- **Well-formed total dominating set instances.** An instance $(n, E, K)$ of TOTAL DOMINATING
SET is well formed when the list $E$ has no repeated entries and every pair $(u, v)$ in $E$
satisfies $u < n$, $v < n$ and $u \ne v$, and its reversal $(v, u)$ does not belong to $E$. -/
def WellFormed (i : TotalDominatingSetInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- **Feasibility of a total dominating set instance.** An instance $(n, E, K)$ of TOTAL
DOMINATING SET is feasible when there is a set $S$ of at most $K$ vertices of its graph such that
every vertex $v$ of the graph, including the vertices of $S$, is adjacent to some vertex
$u \in S$. -/
def TotalDominatingSetFeasible
    (i : TotalDominatingSetInstance) : Prop :=
  ∃ S : Finset (Fin i.1), S.card ≤ i.2.2 ∧
    ∀ v : Fin i.1, ∃ u ∈ S, (Graph i).Adj u v

open Classical in
/-- **The decision problem TOTAL DOMINATING SET.** TOTAL DOMINATING SET accepts a bitstring $x$
exactly when $x$ decodes, under the canonical bitstring encoding of triples of a natural number,
a list of pairs of natural numbers and a natural number, to an instance $(n, E, K)$ that is well
formed and feasible: some set of at most $K$ vertices of the graph of the instance contains a
neighbor of every vertex. Bitstrings that do not decode to an instance are rejected. -/
noncomputable def totalDominatingSetDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TotalDominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ TotalDominatingSetFeasible i)
  | none => false

/-- **TOTAL DOMINATING SET is NP-complete.** The decision problem TOTAL DOMINATING SET belongs to
NP, and every decision problem in NP reduces to TOTAL DOMINATING SET by a polynomial-time
many-one reduction.

Source: E. J. Cockayne, R. M. Dawes, and S. T.
Hedetniemi, "Total domination in graphs", Networks 10 (1980), 211-219; R. Laskar, J.
Pfaff, S. M. Hedetniemi, and S. T. Hedetniemi, "On the algorithmic complexity of total
domination", SIAM Journal on Algebraic and Discrete Methods 5 (1984), 420-425. -/
public theorem_wanted totalDominatingSet_npComplete :
    totalDominatingSetDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L totalDominatingSetDec

end MetaMathlibExt.Complexity.NPComplete.TotalDominatingSet
