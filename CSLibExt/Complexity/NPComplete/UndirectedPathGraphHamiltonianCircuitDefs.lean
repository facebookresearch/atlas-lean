/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT IN UNDIRECTED PATH GRAPHS: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT37] HAMILTONIAN CIRCUIT;
A. A. Bertossi and M. A. Bonuccelli, "Hamiltonian circuits in interval graph generalizations",
Information Processing Letters 23 (1986), 195-200, doi:10.1016/0020-0190(86)90135-3;
ISGCI (Information System on Graph Classes and their Inclusions), class undirected path (gc_129),
problem Hamiltonian cycle: NP-complete [Bertossi and Bonuccelli 1986].
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.DominatingSetUndirectedPathGraphsDefs
public import CSLibExt.Complexity.NPComplete.HamiltonianCycleUndirectedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UndirectedPathGraphHamiltonianCircuit

open MetaMathlibExt.Complexity.NPComplete.HamiltonianCycleUndirected
  (HamiltonianCycleUndirectedInstance Graph HamiltonianCycleUndirectedFeasible)

/-- Well-formedness of an instance: a well-formed HAMILTONIAN CIRCUIT instance whose graph is an
undirected path graph. -/
def WellFormed (i : HamiltonianCycleUndirectedInstance) : Prop :=
  HamiltonianCycleUndirected.WellFormed i ∧
    DominatingSetUndirectedPathGraphs.IsUndirectedPathGraph (Graph i)

open Classical in
/-- HAMILTONIAN CIRCUIT IN UNDIRECTED PATH GRAPHS as a decision problem over bitstrings. -/
noncomputable def undirectedPathGraphHamiltonianCircuitDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := HamiltonianCycleUndirectedInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianCycleUndirectedFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UndirectedPathGraphHamiltonianCircuit
