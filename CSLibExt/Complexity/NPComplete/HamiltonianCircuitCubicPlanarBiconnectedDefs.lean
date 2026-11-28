/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT on 2-connected cubic planar graphs: definitions

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

public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Combinatorics.SimpleGraph.VertexConnectivity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import CSLibExt.Complexity.NPComplete.HamiltonianCycleUndirectedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitCubicPlanarBiconnected

open HamiltonianCycleUndirected (HamiltonianCycleUndirectedInstance Graph
  HamiltonianCycleUndirectedFeasible)

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

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitCubicPlanarBiconnected
