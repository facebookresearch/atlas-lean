/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT on 2-connected cubic planar graphs is NP-complete

Source:
M. R. Garey, D. S. Johnson and R. E. Tarjan, "The planar Hamiltonian circuit problem is
NP-complete", SIAM Journal on Computing 5(4) (1976), 704-714, doi:10.1137/0205049 (abstract: "We
consider the problem of determining whether a planar, cubic, triply-connected graph G has a
Hamiltonian circuit. We show that this problem is NP-complete. Hence the Hamiltonian circuit
problem for this class of graphs, or any larger class containing all such graphs, is probably
computationally intractable.");
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT37] HAMILTONIAN CIRCUIT (the parent
problem);
ISGCI, *Information System on Graph Classes and their Inclusions*, class
"2-connected ∩ cubic ∩ planar" (gc_1183), problem Hamiltonian cycle: NP-complete, with the
reference to Garey, Johnson and Tarjan (1976).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Combinatorics.SimpleGraph.VertexConnectivity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import WantedExt.Complexity.NPComplete.HamiltonianCycleUndirectedWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitCubicPlanarBiconnected

open HamiltonianCycleUndirected (HamiltonianCycleUndirectedInstance Graph
  HamiltonianCycleUndirectedFeasible)

/-!
# HAMILTONIAN CIRCUIT on 2-connected cubic planar graphs is NP-complete

INSTANCE: a finite simple undirected graph `G = (V, E)` that is 2-connected, cubic (every vertex
has degree 3) and planar. QUESTION: does `G` contain a Hamiltonian circuit?

This is HAMILTONIAN CIRCUIT ([GT37], stated on `main` as
`WantedExt.Complexity.NPComplete.HamiltonianCycleUndirectedWanted`) restricted to the ISGCI class
"2-connected ∩ cubic ∩ planar". The instance type, the graph, the parent's well-formedness (at
least one vertex, simple edge list on `Fin n`) and the question (`3 ≤ n` and Mathlib's
`SimpleGraph.IsHamiltonian`) are the parent's; the restriction adds to `WellFormed` that the graph
is 2-connected, the shared MathlibExt predicate `SimpleGraph.IsVertexConnected 2` (more than two
vertices, and connected after deleting any single vertex), cubic, Mathlib's
`SimpleGraph.IsRegularOfDegree 3`, and planar, the shared MathlibExt predicate
`SimpleGraph.IsPlanar` (a crossing-free straight-line drawing; by Fáry's theorem this is planarity
for finite simple graphs). Garey, Johnson and Tarjan prove NP-completeness for planar cubic
3-connected graphs, a subclass, and note that hardness extends to any larger class; membership in
NP holds for all graphs. Binary encoding of all numbers.

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
/-- Well-formedness of an instance: a well-formed HAMILTONIAN CIRCUIT instance (at least one
vertex, simple edge list on `Fin n`) whose graph is 2-connected, cubic and planar. -/
def WellFormed (i : HamiltonianCycleUndirectedInstance) : Prop :=
  HamiltonianCycleUndirected.WellFormed i ∧ (Graph i).IsVertexConnected 2 ∧
    (Graph i).IsRegularOfDegree 3 ∧ (Graph i).IsPlanar

open Classical in
/-- HAMILTONIAN CIRCUIT on 2-connected cubic planar graphs as a decision problem over
bitstrings. -/
noncomputable def hamiltonianCircuitCubicPlanarBiconnectedDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianCycleUndirectedInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianCycleUndirectedFeasible i)
  | none => false

/-- **HAMILTONIAN CIRCUIT on 2-connected cubic planar graphs is NP-complete.** Source: Garey,
Johnson and Tarjan (1976); Garey and Johnson (1979), [GT37] (parent problem). -/
public theorem_wanted hamiltonianCircuitCubicPlanarBiconnected_npComplete :
    hamiltonianCircuitCubicPlanarBiconnectedDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hamiltonianCircuitCubicPlanarBiconnectedDec

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitCubicPlanarBiconnected
