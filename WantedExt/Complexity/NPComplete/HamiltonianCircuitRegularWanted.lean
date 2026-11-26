/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT on k-regular graphs (fixed k ≥ 4) is NP-complete

Source:
C. Picouleau, "Complexity of the Hamiltonian cycle in regular graph problem", Theoretical
Computer Science 131(2) (1994), 463-473, doi:10.1016/0304-3975(94)90185-6 (abstract: "for any
fixed k > 3, deciding whether a k-regular graph has a hamiltonian cycle (or path) is a
NP-complete problem");
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT37] HAMILTONIAN CIRCUIT (the parent
problem);
ISGCI, *Information System on Graph Classes and their Inclusions*, classes "4-regular" (gc_1101)
and "5-regular" (gc_1104), problem Hamiltonian cycle: NP-complete, with the reference to
Picouleau (1994).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import CSLibExt.Complexity.NPComplete.HamiltonianCycleUndirectedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitRegular

open HamiltonianCycleUndirected (HamiltonianCycleUndirectedInstance Graph
  HamiltonianCycleUndirectedFeasible)

/-!
# HAMILTONIAN CIRCUIT on k-regular graphs (fixed k ≥ 4) is NP-complete

For a fixed `k ≥ 4`: INSTANCE: a finite simple undirected graph `G = (V, E)` that is
`k`-regular (every vertex has degree `k`). QUESTION: does `G` contain a Hamiltonian circuit?

This is HAMILTONIAN CIRCUIT ([GT37], stated on `main` as
`CSLibExt.Complexity.NPComplete.HamiltonianCycleUndirectedDefs`) restricted to `k`-regular
graphs, one decision problem for each fixed `k`. The instance type, the graph, the parent's
well-formedness (at least one vertex, simple edge list on `Fin n`) and the question (`3 ≤ n` and
Mathlib's `SimpleGraph.IsHamiltonian`) are the parent's; the restriction adds to `WellFormed` that
the graph is `k`-regular, Mathlib's `SimpleGraph.IsRegularOfDegree k`, as in
`ChromaticIndexRegularWanted`. Picouleau proves NP-completeness for every fixed `k > 3`; the
cases `k = 4` and `k = 5` are the ISGCI classes "4-regular" and "5-regular". Binary encoding of
all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

open Classical in
/-- Well-formedness of an instance for a fixed `k`: a well-formed HAMILTONIAN CIRCUIT instance
(at least one vertex, simple edge list on `Fin n`) whose graph is `k`-regular. -/
def WellFormed (k : ℕ) (i : HamiltonianCycleUndirectedInstance) : Prop :=
  HamiltonianCycleUndirected.WellFormed i ∧ (Graph i).IsRegularOfDegree k

open Classical in
/-- HAMILTONIAN CIRCUIT on `k`-regular graphs as a decision problem over bitstrings. -/
noncomputable def hamiltonianCircuitRegularDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianCycleUndirectedInstance) x with
  | some i => decide (WellFormed k i ∧ HamiltonianCycleUndirectedFeasible i)
  | none => false

/-- **HAMILTONIAN CIRCUIT on `k`-regular graphs is NP-complete for every fixed `k ≥ 4`.**
Source: Picouleau (1994); Garey and Johnson (1979), [GT37] (parent problem). -/
public theorem_wanted hamiltonianCircuitRegular_npComplete (k : ℕ) (_hk : 4 ≤ k) :
    hamiltonianCircuitRegularDec k ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (hamiltonianCircuitRegularDec k)

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitRegular
