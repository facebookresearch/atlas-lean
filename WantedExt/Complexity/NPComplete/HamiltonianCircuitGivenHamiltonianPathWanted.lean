/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT given a Hamiltonian path is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT37] HAMILTONIAN CIRCUIT (comment:
NP-complete even if a Hamiltonian path for `G` is given as part of the instance);
C. H. Papadimitriou and K. Steiglitz, "On the complexity of local search for the traveling
salesman problem", SIAM Journal on Computing 6(1) (1977), 76-83, doi:10.1137/0206005.
-/
module

public import Batteries.Data.List.Basic
public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitGivenHamiltonianPath

/-!
# HAMILTONIAN CIRCUIT given a Hamiltonian path is NP-complete

An instance is a graph `G = (V, E)` together with a Hamiltonian path of `G`. The question is
whether `G` contains a Hamiltonian circuit, a simple cycle through every vertex exactly once.
Papadimitriou and Steiglitz (1977) proved that knowing a Hamiltonian path does not help: the
problem stays NP-complete, which they used to show that polynomial local search for the
traveling salesman problem cannot guarantee near-optimal tours unless `P = NP`.

The graph is simple and given by an edge list on `Fin n`. The Hamiltonian path is a list of
vertices that visits each of `0, …, n - 1` exactly once, consecutive entries being adjacent;
that it is a Hamiltonian path of `G` is part of the instance class (`WellFormed`). A
Hamiltonian circuit is Mathlib's `SimpleGraph.Walk.IsHamiltonianCycle`: a cycle (so at least
three vertices) visiting every vertex exactly once.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **HAMILTONIAN CIRCUIT given a Hamiltonian path is NP-complete.** Source: Garey and Johnson
(1979), [GT37]; Papadimitriou and Steiglitz (1977). -/
public theorem_wanted hamiltonianCircuitGivenHamiltonianPath_npComplete :
    hamiltonianCircuitGivenHamiltonianPathDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hamiltonianCircuitGivenHamiltonianPathDec

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitGivenHamiltonianPath
