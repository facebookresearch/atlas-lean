/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CYCLE (DIRECTED) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), HAMILTONIAN CIRCUIT
(directed); R. M. Karp, "Reducibility among combinatorial problems" (1972).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCycleDirected

/-!
# HAMILTONIAN CYCLE (DIRECTED) is NP-complete

A directed graph on vertices 0, …, n - 1, given by an explicit arc list. The question is
whether the graph has a directed Hamiltonian cycle: a permutation of all vertices in which
consecutive vertices, including the last and the first, are joined by arcs in the forward
direction.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Instances of HAMILTONIAN CYCLE (DIRECTED).** An instance of HAMILTONIAN CYCLE (DIRECTED)
is a pair $(n, E)$ of a natural number $n$, the number of vertices, and a finite list $E$ of
ordered pairs of natural numbers, the arcs. -/
abbrev HamiltonianCycleDirectedInstance := ℕ × List (ℕ × ℕ)


/-- **Directed adjacency for HAMILTONIAN CYCLE (DIRECTED).** For a finite list $E$ of ordered
pairs of natural numbers and natural numbers $u$ and $v$, the directed adjacency of $u$ to $v$
in $E$ is the boolean value that is true exactly when the pair $(u, v)$ occurs in $E$. -/
def DAdj (edges : List (ℕ × ℕ)) (u v : ℕ) : Bool :=
  edges.contains (u, v)


/-- **Well-formed instances of HAMILTONIAN CYCLE (DIRECTED).** An instance $(n, E)$ of
HAMILTONIAN CYCLE (DIRECTED), with $n$ a natural number and $E$ a finite list of ordered pairs
of natural numbers, is well formed when $n > 0$, the list $E$ has no repeated entries, and
every pair $(u, v)$ in $E$ satisfies $u < n$, $v < n$ and $u \ne v$. -/
def WellFormed (i : HamiltonianCycleDirectedInstance) : Prop :=
  0 < i.1 ∧ i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2

/-- **Directed Hamiltonian cycles of an instance.** An instance $(n, E)$ of HAMILTONIAN CYCLE
(DIRECTED), with $n$ a natural number and $E$ a finite list of ordered pairs of natural numbers,
has a directed Hamiltonian cycle when there is a list $(v_0, \dots, v_{n-1})$ of $n$ distinct
natural numbers containing every natural number below $n$ such that the pair
$(v_j, v_{(j+1) \bmod n})$ occurs in $E$ for every $j < n$. -/
def HamiltonianCycleDirectedFeasible
    (i : HamiltonianCycleDirectedInstance) : Prop :=
  ∃ cycle : List ℕ, cycle.Nodup ∧ cycle.length = i.1 ∧ (∀ v < i.1, v ∈ cycle) ∧
    ∀ j < i.1, DAdj i.2 (cycle.getD j 0) (cycle.getD ((j + 1) % i.1) 0)

open Classical in
/-- **The directed Hamiltonian cycle decision problem.** The decision problem HAMILTONIAN CYCLE
(DIRECTED) accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring
encoding, to an instance $(n, E)$, consisting of a natural number $n$ and a finite list $E$ of
ordered pairs of natural numbers, such that $(n, E)$ is well formed ($n > 0$, $E$ has no
repeated entries, and every pair $(u, v)$ in $E$ satisfies $u < n$, $v < n$ and $u \ne v$) and
has a directed Hamiltonian cycle (a list $(v_0, \dots, v_{n-1})$ of $n$ distinct natural
numbers containing every natural number below $n$ such that $(v_j, v_{(j+1) \bmod n})$ occurs
in $E$ for every $j < n$). It rejects every bitstring that does not decode to an instance. -/
noncomputable def hamiltonianCycleDirectedDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianCycleDirectedInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianCycleDirectedFeasible i)
  | none => false

/-- **HAMILTONIAN CYCLE (DIRECTED) is NP-complete.** The decision problem HAMILTONIAN CYCLE
(DIRECTED) belongs to NP, and every decision problem $L$ in NP has a polynomial-time many-one
reduction to it.

Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), HAMILTONIAN CIRCUIT (directed); R. M. Karp,
"Reducibility among combinatorial problems" (1972). -/
public theorem_wanted hamiltonianCycleDirected_npComplete :
    hamiltonianCycleDirectedDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hamiltonianCycleDirectedDec

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCycleDirected
