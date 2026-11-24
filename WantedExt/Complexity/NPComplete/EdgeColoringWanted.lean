/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EDGE COLORING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), EDGE COLORING; I. Holyer,
"The NP-completeness of edge-coloring" (1981).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EdgeColoring

/-!
# EDGE COLORING is NP-complete

An undirected graph and a bound `K`. The question is whether the chromatic index is at most
`K`: a coloring of the edges with colors `0, …, K - 1` in which edges sharing an endpoint
differ.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Edge coloring instances.** An instance of EDGE COLORING is a triple $(n, E, K)$ consisting
of a natural number $n$, the number of vertices, a finite list $E$ of ordered pairs of natural
numbers, the edges, and a natural number $K$, the bound on the number of colors. -/
abbrev EdgeColoringInstance := ℕ × List (ℕ × ℕ) × ℕ


/-- **Adjacency in an edge coloring edge list.** Given a list $E$ of ordered pairs of natural
numbers and natural numbers $u$ and $v$, the boolean adjacency of $u$ and $v$ in $E$ is true
exactly when $(u, v)$ or $(v, u)$ occurs in $E$. -/
def Adj (edges : List (ℕ × ℕ)) (u v : ℕ) : Bool :=
  edges.contains (u, v) || edges.contains (v, u)


/-- **Well-formed edge coloring instances.** An edge coloring instance $(n, E, K)$ is well formed
when the list $E$ has no repeated entries and every pair $(a, b)$ in $E$ satisfies $a < n$,
$b < n$ and $a \ne b$, and $(b, a)$ does not occur in $E$. -/
def WellFormed (i : EdgeColoringInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- **Feasible edge coloring instances.** Let $(n, E, K)$ be an edge coloring instance with edge
list $E = (e_0, \dots, e_{m-1})$, where the endpoints of a pair $(x, y)$ are $x$ and $y$. The
instance is feasible when there is a list $(c_0, \dots, c_{m-1})$ of natural numbers with
$c_j < K$ for every $j$ such that $c_a \ne c_b$ for all distinct $a, b < m$ for which $e_a$ and
$e_b$ share an endpoint. -/
def EdgeColoringFeasible
    (i : EdgeColoringInstance) : Prop :=
  ∃ coloring : List ℕ, coloring.length = i.2.1.length ∧ (∀ c ∈ coloring, c < i.2.2) ∧
    ∀ a < i.2.1.length, ∀ b < i.2.1.length, a ≠ b →
      ((i.2.1.getD a (0, 0)).1 = (i.2.1.getD b (0, 0)).1 ∨
        (i.2.1.getD a (0, 0)).1 = (i.2.1.getD b (0, 0)).2 ∨
        (i.2.1.getD a (0, 0)).2 = (i.2.1.getD b (0, 0)).1 ∨
        (i.2.1.getD a (0, 0)).2 = (i.2.1.getD b (0, 0)).2) →
      coloring.getD a 0 ≠ coloring.getD b 0

open Classical in
/-- **EDGE COLORING as a decision problem.** The EDGE COLORING decision problem accepts a
bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of edge coloring
instances, to an instance that is well formed and feasible. Bitstrings that do not decode are
rejected. -/
noncomputable def edgeColoringDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EdgeColoringInstance) x with
  | some i => decide (WellFormed i ∧ EdgeColoringFeasible i)
  | none => false

/-- **EDGE COLORING is NP-complete.** The EDGE COLORING decision problem belongs to NP, and every
decision problem in NP has a polynomial-time many-one reduction to it.

Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), EDGE COLORING; I. Holyer, "The NP-completeness of edge-coloring"
(1981). -/
public theorem_wanted edgeColoring_npComplete :
    edgeColoringDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L edgeColoringDec

end MetaMathlibExt.Complexity.NPComplete.EdgeColoring
