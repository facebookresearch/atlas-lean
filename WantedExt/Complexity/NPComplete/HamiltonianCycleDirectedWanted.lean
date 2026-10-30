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

/-- An instance: vertex count, edge list. -/
abbrev HamiltonianCycleDirectedInstance := ℕ × List (ℕ × ℕ)


/-- Directed adjacency from an edge list (as a Bool, for use in filters). -/
def DAdj (edges : List (ℕ × ℕ)) (u v : ℕ) : Bool :=
  edges.contains (u, v)


/-- Well-formedness of an instance. -/
def WellFormed (i : HamiltonianCycleDirectedInstance) : Prop :=
  0 < i.1 ∧ i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2

/-- A directed Hamiltonian cycle. -/
def HamiltonianCycleDirectedFeasible
    (i : HamiltonianCycleDirectedInstance) : Prop :=
  ∃ cycle : List ℕ, cycle.Nodup ∧ cycle.length = i.1 ∧ (∀ v < i.1, v ∈ cycle) ∧
    ∀ j < i.1, DAdj i.2 (cycle.getD j 0) (cycle.getD ((j + 1) % i.1) 0)

open Classical in
/-- HAMILTONIAN CYCLE (DIRECTED) as a decision problem over bitstrings. -/
noncomputable def hamiltonianCycleDirectedDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianCycleDirectedInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianCycleDirectedFeasible i)
  | none => false

/-- **HAMILTONIAN CYCLE (DIRECTED) is NP-complete.** Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), HAMILTONIAN CIRCUIT (directed); R. M. Karp,
"Reducibility among combinatorial problems" (1972). -/
public theorem_wanted hamiltonianCycleDirected_npComplete :
    hamiltonianCycleDirectedDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hamiltonianCycleDirectedDec

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCycleDirected
