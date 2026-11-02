/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH COLORING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), GRAPH COLORING (chromatic
number); R. M. Karp, "Reducibility among combinatorial problems" (1972).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphColoring

/-!
# GRAPH COLORING is NP-complete

An undirected graph and a bound `K`. The question is whether the chromatic number is at most
`K`: a coloring with colors `0, …, K - 1` in which adjacent vertices differ.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Instances of GRAPH COLORING.** An instance of GRAPH COLORING is a triple $(n, E, K)$
consisting of a natural number $n$, the number of vertices, a list $E$ of pairs of natural
numbers, the edges, and a natural number $K$, the bound on the number of colors. -/
abbrev GraphColoringInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- **Graph of a GRAPH COLORING instance.** The graph of an instance $(n, E, K)$ of GRAPH
COLORING is the simple graph on $\{0, \dots, n - 1\}$ in which distinct vertices $i$ and $j$ are
adjacent when $(i, j)$ or $(j, i)$ belongs to $E$. -/
def Graph (i : GraphColoringInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1


/-- **Well-formed GRAPH COLORING instances.** An instance $(n, E, K)$ of GRAPH COLORING is well
formed when the list $E$ has no repeated entries and every pair $(u, v)$ in $E$ satisfies
$u < n$, $v < n$, $u \ne v$ and $(v, u) \notin E$. -/
def WellFormed (i : GraphColoringInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- **Feasible GRAPH COLORING instances.** An instance $(n, E, K)$ of GRAPH COLORING is
feasible when its graph is $K$-colorable, that is, when its vertices can be assigned colors from
$\{0, \dots, K - 1\}$ so that adjacent vertices receive different colors. -/
def GraphColoringFeasible
    (i : GraphColoringInstance) : Prop :=
  (Graph i).Colorable i.2.2

open Classical in
/-- **GRAPH COLORING as a decision problem.** The decision problem GRAPH COLORING accepts a
bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding, to an instance
of GRAPH COLORING that is well formed and feasible. Bitstrings that do not decode to an instance
are rejected. -/
noncomputable def graphColoringDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ GraphColoringFeasible i)
  | none => false

/-- **GRAPH COLORING is NP-complete.** The decision problem GRAPH COLORING belongs to NP, and
every decision problem $L$ in NP has a polynomial-time many-one reduction to GRAPH COLORING.

Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), GRAPH COLORING (chromatic number); R. M. Karp, "Reducibility among
combinatorial problems" (1972). -/
public theorem_wanted graphColoring_npComplete :
    graphColoringDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L graphColoringDec

end MetaMathlibExt.Complexity.NPComplete.GraphColoring
