/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CYCLE (UNDIRECTED) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), HAMILTONIAN CIRCUIT; R.
M. Karp, "Reducibility among combinatorial problems" (1972).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCycleUndirected

/-!
# HAMILTONIAN CYCLE (UNDIRECTED) is NP-complete

An undirected graph on vertices 0, …, n - 1, given by an explicit edge list. The question is
whether the graph has a Hamiltonian cycle: a permutation of all vertices in which consecutive
vertices, including the last and the first, are adjacent. A genuine cycle needs at least three
vertices: the two-vertex graph with one edge is a no-instance.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Instances of HAMILTONIAN CYCLE (UNDIRECTED).** An instance of HAMILTONIAN CYCLE
(UNDIRECTED) is a pair $(n, E)$ of a natural number $n$, the number of vertices, and a finite
list $E$ of pairs of natural numbers, the edges. -/
abbrev HamiltonianCycleUndirectedInstance := ℕ × List (ℕ × ℕ)

/-- **Graph of a HAMILTONIAN CYCLE (UNDIRECTED) instance.** For an instance $(n, E)$, its graph
is the simple graph on the vertices $\{0, \dots, n-1\}$ in which distinct vertices $i$ and $j$
are adjacent when $(i, j)$ or $(j, i)$ belongs to $E$. -/
def Graph (i : HamiltonianCycleUndirectedInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2


/-- **Well-formed HAMILTONIAN CYCLE (UNDIRECTED) instances.** An instance $(n, E)$ is well formed
when $0 < n$, the list $E$ has no repeated entries, and every pair $(u, v)$ in $E$ satisfies
$u < n$, $v < n$ and $u \ne v$, and its reversal $(v, u)$ does not belong to $E$. -/
def WellFormed (i : HamiltonianCycleUndirectedInstance) : Prop :=
  0 < i.1 ∧ i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- **Feasible HAMILTONIAN CYCLE (UNDIRECTED) instances.** An instance $(n, E)$ is feasible when
$n \ge 3$ and its graph has a Hamiltonian cycle, that is, a cycle that visits every vertex exactly
once. -/
def HamiltonianCycleUndirectedFeasible
    (i : HamiltonianCycleUndirectedInstance) : Prop :=
  3 ≤ i.1 ∧ (Graph i).IsHamiltonian

open Classical in
/-- **HAMILTONIAN CYCLE (UNDIRECTED) as a decision problem.** The decision problem HAMILTONIAN
CYCLE (UNDIRECTED) accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring
encoding, to a well-formed instance $(n, E)$ with $n \ge 3$ whose graph has a Hamiltonian cycle.
It rejects every bitstring that does not decode to an instance. -/
noncomputable def hamiltonianCycleUndirectedDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianCycleUndirectedInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianCycleUndirectedFeasible i)
  | none => false

/-- **HAMILTONIAN CYCLE (UNDIRECTED) is NP-complete.** The decision problem HAMILTONIAN CYCLE
(UNDIRECTED) belongs to NP, and every decision problem in NP has a polynomial-time many-one
reduction to it.

Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), HAMILTONIAN CIRCUIT; R. M. Karp, "Reducibility
among combinatorial problems" (1972). -/
public theorem_wanted hamiltonianCycleUndirected_npComplete :
    hamiltonianCycleUndirectedDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hamiltonianCycleUndirectedDec

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCycleUndirected
