/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DIRECTED PATH COVER is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), PATH COVER (the `K = 1`
slice is Hamiltonian path).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity


@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DirectedPathCover

/-!
# DIRECTED PATH COVER is NP-complete

A directed graph and a bound `K`. The question is whether all vertices can be covered by at
most `K` directed paths: simple vertex-disjoint paths (singleton paths allowed) whose vertex
sets partition the vertex set.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Instances of DIRECTED PATH COVER.** An instance of DIRECTED PATH COVER is a triple
$(n, E, K)$, where the natural number $n$ is the number of vertices, the list $E$ of ordered
pairs of natural numbers lists the directed edges, and the natural number $K$ bounds the number
of paths. -/
abbrev DirectedPathCoverInstance := ℕ × List (ℕ × ℕ) × ℕ


/-- **Directed adjacency in an edge list.** For a list $E$ of ordered pairs of natural numbers
and natural numbers $u$ and $v$, the directed adjacency test of $E$ at $(u, v)$ is the boolean
that is true exactly when the pair $(u, v)$ occurs in $E$, that is, when $E$ contains an edge
from $u$ to $v$. -/
def DAdj (edges : List (ℕ × ℕ)) (u v : ℕ) : Bool :=
  edges.contains (u, v)


/-- **Well-formed DIRECTED PATH COVER instances.** An instance $(n, E, K)$ of
DIRECTED PATH COVER is well formed when the edge list $E$ has no repeated entries and every
edge $(a, b)$ in $E$ satisfies $a < n$, $b < n$ and $a \ne b$. -/
def WellFormed (i : DirectedPathCoverInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2

/-- **Feasible DIRECTED PATH COVER instances.** An instance $(n, E, K)$ of DIRECTED PATH
COVER is feasible when there is a list of at most $K$ paths, each a list of natural numbers,
such that every path has no repeated vertex, every vertex on a path is less than $n$, and
whenever $v$ immediately follows $u$ on a path the pair $(u, v)$ occurs in $E$; and such that
every vertex $v < n$ lies on some path, and all paths containing $v$ are equal. -/
def DirectedPathCoverFeasible
    (i : DirectedPathCoverInstance) : Prop :=
  ∃ paths : List (List ℕ), paths.length ≤ i.2.2 ∧
    (∀ p ∈ paths, p.Nodup ∧ (∀ v ∈ p, v < i.1) ∧
      ∀ j, j + 1 < p.length → DAdj i.2.1 (p.getD j 0) (p.getD (j + 1) 0)) ∧
    ∀ v < i.1, ∃ p ∈ paths, v ∈ p ∧ ∀ p' ∈ paths, v ∈ p' → p' = p

open Classical in
/-- **DIRECTED PATH COVER as a decision problem.** DIRECTED PATH COVER is the decision problem
that accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding,
to an instance $(n, E, K)$ of DIRECTED PATH COVER that is well formed and feasible; bitstrings
that do not decode to an instance are rejected. -/
noncomputable def directedPathCoverDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DirectedPathCoverInstance) x with
  | some i => decide (WellFormed i ∧ DirectedPathCoverFeasible i)
  | none => false

/-- **DIRECTED PATH COVER is NP-complete.** The decision problem DIRECTED PATH COVER is in NP,
and every decision problem in NP has a polynomial-time many-one reduction to
DIRECTED PATH COVER.

Source: M. R. Garey and D. S. Johnson, *Computers
and Intractability* (1979), PATH COVER (the `K = 1` slice is Hamiltonian path). -/
public theorem_wanted directedPathCover_npComplete :
    directedPathCoverDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L directedPathCoverDec

end MetaMathlibExt.Complexity.NPComplete.DirectedPathCover
