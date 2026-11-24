/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM EQUIVALENT DIGRAPH is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), MINIMUM EQUIVALENT
DIGRAPH; A. V. Aho, M. R. Garey, and J. D. Ullman, "The transitive reduction of a directed
graph", SIAM Journal on Computing 1 (1972), 131-137 (distinguishing transitive reduction from
the minimum equivalent subgraph and the hardness connection); D. M. Moyles and G. L. Thompson,
"An algorithm for finding a minimum equivalent graph of a digraph", Journal of the ACM 16
(1969), 455-460.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity


@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumEquivalentDigraph

/-!
# MINIMUM EQUIVALENT DIGRAPH is NP-complete

A directed graph and a bound `K`. The question is whether some spanning subdigraph with at most
`K` arcs has exactly the same reachability relation: two vertices are joined by a directed path
in the subdigraph iff they are in the original. Reachability is witnessed by paths of length at
most `n + 1`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Instances of MINIMUM EQUIVALENT DIGRAPH.** An instance of MINIMUM EQUIVALENT DIGRAPH is a
triple $(n, E, K)$ consisting of a natural number $n$ (the number of vertices), a finite list $E$
of ordered pairs of natural numbers (the arcs) and a natural number $K$ (the bound on the number
of arcs). -/
abbrev MinimumEquivalentDigraphInstance := ℕ × List (ℕ × ℕ) × ℕ


/-- **Directed adjacency for MINIMUM EQUIVALENT DIGRAPH.** For a finite list $E$ of ordered pairs
of natural numbers and natural numbers $u$ and $v$, the directed adjacency test of $E$ at $(u, v)$
returns true when the pair $(u, v)$ occurs in $E$, and false otherwise. -/
def DAdj (edges : List (ℕ × ℕ)) (u v : ℕ) : Bool :=
  edges.contains (u, v)

/-- **Bounded reachability in a digraph.** Let $E$ be a finite list of ordered pairs of natural
numbers, read as the arcs of a directed graph, and let $n$, $u$ and $v$ be natural numbers. Then
$v$ is reachable from $u$ within $n$ steps along $E$ when there are natural numbers
$w_0, w_1, \dots, w_k$ with $k \le n$, $w_0 = u$ and $w_k = v$ such that $(w_j, w_{j+1})$ occurs
in $E$ for every $j < k$. -/
def Reachable (n : ℕ) (E : List (ℕ × ℕ)) (u v : ℕ) : Prop :=
  ∃ path : List ℕ, path.length ≤ n + 1 ∧ path ≠ [] ∧
    path.getD 0 0 = u ∧ path.getD (path.length - 1) 0 = v ∧
    ∀ j, j + 1 < path.length → DAdj E (path.getD j 0) (path.getD (j + 1) 0)


/-- **Well-formed MINIMUM EQUIVALENT DIGRAPH instances.** An instance $(n, E, K)$ of MINIMUM
EQUIVALENT DIGRAPH is well formed when the list $E$ has no repeated entries and every pair
$(a, b)$ in $E$ satisfies $a < n$, $b < n$ and $a \ne b$; that is, $E$ lists distinct arcs
without loops between vertices among $0, \dots, n - 1$. -/
def WellFormed (i : MinimumEquivalentDigraphInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2

/-- **Feasible MINIMUM EQUIVALENT DIGRAPH instances.** An instance $(n, E, K)$ of MINIMUM
EQUIVALENT DIGRAPH is feasible when some sublist $F$ of $E$ (obtained by deleting entries of
$E$) has at most $K$ entries and, for all vertices $u < n$ and $v < n$, $v$ is reachable from $u$
within $n$ steps along $E$ if and only if $v$ is reachable from $u$ within $n$ steps along
$F$. -/
def MinimumEquivalentDigraphFeasible
    (i : MinimumEquivalentDigraphInstance) : Prop :=
  ∃ F : List (ℕ × ℕ), F.Sublist i.2.1 ∧ F.length ≤ i.2.2 ∧
    ∀ u < i.1, ∀ v < i.1, Reachable i.1 i.2.1 u v ↔ Reachable i.1 F u v

open Classical in
/-- **MINIMUM EQUIVALENT DIGRAPH as a decision problem.** The decision problem MINIMUM
EQUIVALENT DIGRAPH accepts a bitstring $x$ exactly when $x$ decodes, under the canonical
bitstring encoding, to an instance of MINIMUM EQUIVALENT DIGRAPH that is well formed and
feasible. Bitstrings that do not decode to an instance are rejected. -/
noncomputable def minimumEquivalentDigraphDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumEquivalentDigraphInstance) x with
  | some i => decide (WellFormed i ∧ MinimumEquivalentDigraphFeasible i)
  | none => false

/-- **MINIMUM EQUIVALENT DIGRAPH is NP-complete.** The decision problem MINIMUM EQUIVALENT
DIGRAPH belongs to NP, and every decision problem in NP has a polynomial-time many-one reduction
to it.

Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), MINIMUM EQUIVALENT DIGRAPH; A. V. Aho, M. R. Garey,
and J. D. Ullman, "The transitive reduction of a directed graph", SIAM Journal on
Computing 1 (1972), 131-137 (distinguishing transitive reduction from the minimum
equivalent subgraph and the hardness connection); D. M. Moyles and G. L. Thompson, "An
algorithm for finding a minimum equivalent graph of a digraph", Journal of the ACM 16
(1969), 455-460. -/
public theorem_wanted minimumEquivalentDigraph_npComplete :
    minimumEquivalentDigraphDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumEquivalentDigraphDec

end MetaMathlibExt.Complexity.NPComplete.MinimumEquivalentDigraph
