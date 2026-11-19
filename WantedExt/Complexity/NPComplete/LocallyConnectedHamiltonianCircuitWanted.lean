/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT on locally connected graphs of maximum degree 7 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT37] HAMILTONIAN CIRCUIT;
V. S. Gordon, Y. L. Orlovich, C. N. Potts and V. A. Strusevich, "Hamiltonian properties of
locally connected graphs with bounded vertex degree", Discrete Applied Mathematics 159 (2011),
1759-1774, doi:10.1016/j.dam.2010.10.005.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import WantedExt.Complexity.NPComplete.HamiltonianCycleUndirectedWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LocallyConnectedHamiltonianCircuit

open MetaMathlibExt.Complexity.NPComplete.HamiltonianCycleUndirected

/-!
# HAMILTONIAN CIRCUIT on locally connected graphs of maximum degree 7 is NP-complete

INSTANCE: a locally connected graph `G = (V, E)` with maximum degree `Δ(G) ≤ 7`; locally
connected means that for every vertex `v` the subgraph induced by its neighbourhood `N(v)` is
connected.
QUESTION: does `G` contain a Hamiltonian circuit?

Gordon, Orlovich, Potts and Strusevich (2011, abstract): "we prove that problem Hamilton Cycle
for the locally connected graphs with Δ(G) ⩽ 7 is NP-complete".

The instance, its well-formedness and the question are those of
`WantedExt.Complexity.NPComplete.HamiltonianCycleUndirectedWanted` ([GT37]: a simple graph on
`Fin n`, `n > 0`, given by an edge list; a Hamiltonian circuit needs at least three vertices).
The restriction adds that every vertex has degree at most `7` (`SimpleGraph.degree`) and that
every neighbourhood induces a connected graph: `G.induce (G.neighborSet v)` is
`SimpleGraph.Connected`. Mathlib's `Connected` includes nonemptiness, so a graph with an
isolated vertex is not locally connected here; such a graph is a no-instance under either
convention (a Hamiltonian circuit has at least three vertices and passes through every vertex), so
this choice does not change which bitstrings are yes-instances.

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
/-- Well-formedness of an instance: a well-formed HAMILTONIAN CIRCUIT instance whose graph has
every vertex of degree at most `7` and is locally connected (every neighbourhood induces a
connected graph). -/
def WellFormed (i : HamiltonianCycleUndirectedInstance) : Prop :=
  HamiltonianCycleUndirected.WellFormed i ∧ (∀ v, (Graph i).degree v ≤ 7) ∧
    ∀ v, ((Graph i).induce ((Graph i).neighborSet v)).Connected

open Classical in
/-- HAMILTONIAN CIRCUIT on locally connected graphs of maximum degree 7 as a decision problem
over bitstrings. -/
noncomputable def locallyConnectedHamiltonianCircuitDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianCycleUndirectedInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianCycleUndirectedFeasible i)
  | none => false

/-- **HAMILTONIAN CIRCUIT on locally connected graphs of maximum degree 7 is NP-complete.**
Source: Garey and Johnson (1979), [GT37]; Gordon, Orlovich, Potts and Strusevich (2011). -/
public theorem_wanted locallyConnectedHamiltonianCircuit_npComplete :
    locallyConnectedHamiltonianCircuitDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L locallyConnectedHamiltonianCircuitDec

end MetaMathlibExt.Complexity.NPComplete.LocallyConnectedHamiltonianCircuit
