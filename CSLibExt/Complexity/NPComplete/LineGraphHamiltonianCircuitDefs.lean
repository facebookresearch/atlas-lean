/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT on line graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT37] HAMILTONIAN CIRCUIT;
A. A. Bertossi, "The edge Hamiltonian path problem is NP-complete", Information Processing
Letters 13 (1981), 157-159, doi:10.1016/0020-0190(81)90048-X;
recorded in R. Faudree, E. Flandrin and Z. Ryjáček, "Claw-free graphs — A survey", Discrete
Mathematics 164 (1997), 87-147, doi:10.1016/S0012-365X(96)00045-3.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.LineGraph
public import CSLibExt.Complexity.NPComplete.HamiltonianCycleUndirectedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LineGraphHamiltonianCircuit

open MetaMathlibExt.Complexity.NPComplete.HamiltonianCycleUndirected

/-- Well-formedness of an instance: a well-formed HAMILTONIAN CIRCUIT instance whose graph is
a line graph. -/
def WellFormed (i : HamiltonianCycleUndirectedInstance) : Prop :=
  HamiltonianCycleUndirected.WellFormed i ∧ MetaMathlibExt.SimpleGraph.IsLineGraph (Graph i)

open Classical in
/-- HAMILTONIAN CIRCUIT on line graphs as a decision problem over bitstrings. -/
noncomputable def lineGraphHamiltonianCircuitDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianCycleUndirectedInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianCycleUndirectedFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.LineGraphHamiltonianCircuit
