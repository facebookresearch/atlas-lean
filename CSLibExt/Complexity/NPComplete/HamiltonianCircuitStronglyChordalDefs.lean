/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT on strongly chordal graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT37] HAMILTONIAN CIRCUIT;
H. Müller, "Hamiltonian circuits in chordal bipartite graphs", Discrete Mathematics 156 (1996),
291-298, doi:10.1016/0012-365X(95)00057-4 (NP-complete already for strongly chordal split graphs).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.HamiltonianCycleUndirectedDefs
public import CSLibExt.Complexity.NPComplete.StronglyChordalSplitHamiltonianPathDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitStronglyChordal

open MetaMathlibExt.Complexity.NPComplete.HamiltonianCycleUndirected

/-- Well-formedness of an instance: a well-formed HAMILTONIAN CIRCUIT instance whose graph is
strongly chordal. -/
def WellFormed (i : HamiltonianCycleUndirectedInstance) : Prop :=
  HamiltonianCycleUndirected.WellFormed i ∧
    StronglyChordalSplitHamiltonianPath.IsStronglyChordal (Graph i)

open Classical in
/-- HAMILTONIAN CIRCUIT on strongly chordal graphs as a decision problem over bitstrings. -/
noncomputable def hamiltonianCircuitStronglyChordalDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianCycleUndirectedInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianCycleUndirectedFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitStronglyChordal
