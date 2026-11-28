/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT on 2-connected cubic planar bipartite graphs: definitions

Source:
T. Akiyama, T. Nishizeki and N. Saito, "NP-completeness of the Hamiltonian cycle problem for
bipartite graphs", Journal of Information Processing 3(2) (1980), 73-76 (abstract: "We show that
this problem is NP-complete for two classes of bipartite graphs: 2-connected cubic bipartite
planar graphs; and 3-connected cubic bipartite graphs.");
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT37] HAMILTONIAN CIRCUIT (the parent
problem).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import CSLibExt.Complexity.NPComplete.HamiltonianCircuitCubicPlanarBiconnectedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitCubicPlanarBipartiteBiconnected

open HamiltonianCycleUndirected (HamiltonianCycleUndirectedInstance Graph
  HamiltonianCycleUndirectedFeasible)

open Classical in
/-- Well-formedness of an instance: a well-formed instance of HAMILTONIAN CIRCUIT on 2-connected
cubic planar graphs whose graph is also bipartite. -/
def WellFormed (i : HamiltonianCycleUndirectedInstance) : Prop :=
  HamiltonianCircuitCubicPlanarBiconnected.WellFormed i ∧ (Graph i).IsBipartite

open Classical in
/-- HAMILTONIAN CIRCUIT on 2-connected cubic planar bipartite graphs as a decision problem over
bitstrings. -/
noncomputable def hamiltonianCircuitCubicPlanarBipartiteBiconnectedDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianCycleUndirectedInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianCycleUndirectedFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitCubicPlanarBipartiteBiconnected
