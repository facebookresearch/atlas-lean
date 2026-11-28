/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT for bipartite graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT37] HAMILTONIAN CIRCUIT, comment (2);
M. S. Krishnamoorthy, "An NP-hard problem in bipartite graphs", ACM SIGACT News 7(1) (1975), 26,
doi:10.1145/990518.990521;
T. Akiyama, T. Nishizeki and N. Saito, "NP-completeness of the Hamiltonian cycle problem for
bipartite graphs", Journal of Information Processing 3 (1980), 73-76.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import CSLibExt.Complexity.NPComplete.HamiltonianCycleUndirectedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitBipartite

open HamiltonianCycleUndirected
  (HamiltonianCycleUndirectedInstance Graph HamiltonianCycleUndirectedFeasible)

/-- Well-formedness of an instance: a well-formed HAMILTONIAN CIRCUIT instance (at least one
vertex and a simple edge list on the vertices `0, ..., n - 1`) whose graph is bipartite
(`SimpleGraph.IsBipartite`). -/
def WellFormed (i : HamiltonianCycleUndirectedInstance) : Prop :=
  HamiltonianCycleUndirected.WellFormed i ∧ (Graph i).IsBipartite

open Classical in
/-- HAMILTONIAN CIRCUIT for bipartite graphs as a decision problem over bitstrings. -/
noncomputable def hamiltonianCircuitBipartiteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianCycleUndirectedInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianCycleUndirectedFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitBipartite
