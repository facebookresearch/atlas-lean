/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN PATH (UNDIRECTED) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), HAMILTONIAN PATH.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianPathUndirected

/-!
# HAMILTONIAN PATH (UNDIRECTED) is NP-complete

An undirected graph on vertices 0, …, n - 1, given by an explicit edge list. The question is
whether the graph has a Hamiltonian path: a permutation of all vertices in which consecutive
vertices are adjacent.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Instances of undirected Hamiltonian path.** An instance of undirected Hamiltonian path is a
pair $(n, E)$ of a natural number $n$, the number of vertices, and a finite list $E$ of pairs of
natural numbers, the edge list. -/
abbrev HamiltonianPathUndirectedInstance := ℕ × List (ℕ × ℕ)

/-- **Graph of an undirected Hamiltonian path instance.** For an instance $(n, E)$ of undirected
Hamiltonian path, its graph is the simple graph on the vertex set $\{0, \dots, n-1\}$ in which
distinct vertices $i$ and $j$ are adjacent when $(i, j)$ or $(j, i)$ belongs to $E$. -/
def Graph (i : HamiltonianPathUndirectedInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2


/-- **Well-formed undirected Hamiltonian path instances.** An instance $(n, E)$ of undirected
Hamiltonian path is well formed when $n > 0$, the list $E$ has no repeated entries, and every pair
$(u, v)$ in $E$ satisfies $u < n$, $v < n$ and $u \ne v$, and the reversed pair $(v, u)$ does not
belong to $E$. -/
def WellFormed (i : HamiltonianPathUndirectedInstance) : Prop :=
  0 < i.1 ∧ i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- **Feasible undirected Hamiltonian path instances.** An instance $(n, E)$ of undirected
Hamiltonian path is feasible when its graph has a Hamiltonian path: a list of length $n$ of
vertices of the graph, with no repeated entries and containing every vertex, in which any two
consecutive entries are adjacent. -/
def HamiltonianPathUndirectedFeasible
    (i : HamiltonianPathUndirectedInstance) : Prop :=
  ∃ path : List (Fin i.1), path.Nodup ∧ path.length = i.1 ∧ (∀ v, v ∈ path) ∧
    ∀ j (h : j + 1 < path.length),
      (Graph i).Adj (path[j]'(by omega)) (path[j + 1]'h)

open Classical in
/-- **HAMILTONIAN PATH (UNDIRECTED) as a decision problem.** The decision problem HAMILTONIAN PATH
(UNDIRECTED) accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring
encoding, to an instance $(n, E)$ of undirected Hamiltonian path that is well formed and feasible;
bitstrings that do not decode to an instance are rejected. -/
noncomputable def hamiltonianPathUndirectedDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianPathUndirectedInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianPathUndirectedFeasible i)
  | none => false

/-- **HAMILTONIAN PATH (UNDIRECTED) is NP-complete.** The decision problem HAMILTONIAN PATH
(UNDIRECTED) belongs to NP, and every decision problem in NP reduces to it by a polynomial-time
many-one reduction.

Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), HAMILTONIAN PATH. -/
public theorem_wanted hamiltonianPathUndirected_npComplete :
    hamiltonianPathUndirectedDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hamiltonianPathUndirectedDec

end MetaMathlibExt.Complexity.NPComplete.HamiltonianPathUndirected
