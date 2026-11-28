/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN PATH IN GRID GRAPHS: definitions

Source:
A. Itai, C. H. Papadimitriou and J. L. Szwarcfiter, "Hamilton paths in grid graphs", SIAM
Journal on Computing 11 (1982), 676-686, doi:10.1137/0211056;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT39] HAMILTONIAN PATH (the parent
problem);
ISGCI, *Information System on Graph Classes and their Inclusions*, class `gc_1057` (grid graph),
problem Hamiltonian path: NP-complete (Itai, Papadimitriou and Szwarcfiter 1982).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GridGraphHamiltonianCircuitDefs
public import CSLibExt.Complexity.NPComplete.HamiltonianPathUndirectedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GridGraphHamiltonianPath

open MetaMathlibExt.Complexity.NPComplete.GridGraphHamiltonianCircuit
  (GridGraphHamiltonianCircuitInstance toHamiltonianInstance)
open MetaMathlibExt.Complexity.NPComplete.HamiltonianPathUndirected
  (HamiltonianPathUndirectedFeasible)

/-- Well-formedness of an instance: the listed points are pairwise distinct, and the grid graph
is a well-formed HAMILTONIAN PATH instance (at least one point). -/
def WellFormed (i : GridGraphHamiltonianCircuitInstance) : Prop :=
  GridGraphHamiltonianCircuit.WellFormed i ∧
    HamiltonianPathUndirected.WellFormed (toHamiltonianInstance i)

open Classical in
/-- HAMILTONIAN PATH IN GRID GRAPHS as a decision problem over bitstrings. -/
noncomputable def gridGraphHamiltonianPathDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GridGraphHamiltonianCircuitInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianPathUndirectedFeasible (toHamiltonianInstance i))
  | none => false

end MetaMathlibExt.Complexity.NPComplete.GridGraphHamiltonianPath
