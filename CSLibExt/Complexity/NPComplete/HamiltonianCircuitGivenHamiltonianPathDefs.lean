/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT given a Hamiltonian path: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT37] HAMILTONIAN CIRCUIT (comment:
NP-complete even if a Hamiltonian path for `G` is given as part of the instance);
C. H. Papadimitriou and K. Steiglitz, "On the complexity of local search for the traveling
salesman problem", SIAM Journal on Computing 6(1) (1977), 76-83, doi:10.1137/0206005.
-/
module

public import Batteries.Data.List.Basic
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitGivenHamiltonianPath

/-- An instance: vertex count `n` (vertices `0, …, n - 1`), edge list, and a Hamiltonian path
as a list of vertices. -/
abbrev HamiltonianCircuitGivenHamiltonianPathInstance := ℕ × List (ℕ × ℕ) × List ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : HamiltonianCircuitGivenHamiltonianPathInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: at least one vertex (a path has one), the edge list
describes a simple graph (no duplicate edges in either orientation, no self-loops, endpoints in
range), and the given list is a Hamiltonian path of it: it lists `n` distinct vertices, each
`< n` (so every vertex exactly once), and consecutive entries are joined by an edge. -/
def WellFormed (i : HamiltonianCircuitGivenHamiltonianPathInstance) : Prop :=
  0 < i.1 ∧ (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    i.2.2.Nodup ∧ i.2.2.length = i.1 ∧ (∀ v ∈ i.2.2, v < i.1) ∧
    i.2.2.IsChain (fun a b => (a, b) ∈ i.2.1 ∨ (b, a) ∈ i.2.1)

/-- `G` has a Hamiltonian circuit. -/
def HamiltonianCircuitGivenHamiltonianPathFeasible
    (i : HamiltonianCircuitGivenHamiltonianPathInstance) : Prop :=
  ∃ v : Fin i.1, ∃ p : (Graph i).Walk v v, p.IsHamiltonianCycle

open Classical in
/-- HAMILTONIAN CIRCUIT given a Hamiltonian path as a decision problem over bitstrings. -/
noncomputable def hamiltonianCircuitGivenHamiltonianPathDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianCircuitGivenHamiltonianPathInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianCircuitGivenHamiltonianPathFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitGivenHamiltonianPath
