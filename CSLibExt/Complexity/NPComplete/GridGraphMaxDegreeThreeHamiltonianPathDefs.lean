/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN PATH IN GRID GRAPHS OF MAXIMUM DEGREE 3: definitions

Source:
C. H. Papadimitriou and U. V. Vazirani, "On two geometric problems related to the travelling
salesman problem", Journal of Algorithms 5 (1984), 231-246, doi:10.1016/0196-6774(84)90029-4;
A. Itai, C. H. Papadimitriou and J. L. Szwarcfiter, "Hamilton paths in grid graphs", SIAM
Journal on Computing 11 (1982), 676-686, doi:10.1137/0211056;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT39] HAMILTONIAN PATH (the parent
problem);
ISGCI, *Information System on Graph Classes and their Inclusions*, class `gc_1114` (grid graph ∩
maximum degree 3), problem Hamiltonian path: NP-complete (Papadimitriou and Vazirani 1984).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import CSLibExt.Complexity.NPComplete.GridGraphHamiltonianCircuitDefs
public import CSLibExt.Complexity.NPComplete.HamiltonianPathUndirectedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GridGraphMaxDegreeThreeHamiltonianPath

open MetaMathlibExt.Complexity.NPComplete.GridGraphHamiltonianCircuit
  (GridGraphHamiltonianCircuitInstance toHamiltonianInstance)
open MetaMathlibExt.Complexity.NPComplete.HamiltonianPathUndirected
  (HamiltonianPathUndirectedFeasible)

open Classical in
/-- Well-formedness of an instance: the listed points are pairwise distinct, the grid graph is a
well-formed HAMILTONIAN PATH instance (at least one point), and every point has at most `3`
neighbours in it. -/
def WellFormed (i : GridGraphHamiltonianCircuitInstance) : Prop :=
  GridGraphHamiltonianCircuit.WellFormed i ∧
    HamiltonianPathUndirected.WellFormed (toHamiltonianInstance i) ∧
    ∀ v, (HamiltonianPathUndirected.Graph (toHamiltonianInstance i)).degree v ≤ 3

open Classical in
/-- HAMILTONIAN PATH IN GRID GRAPHS OF MAXIMUM DEGREE 3 as a decision problem over bitstrings. -/
noncomputable def gridGraphMaxDegreeThreeHamiltonianPathDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GridGraphHamiltonianCircuitInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianPathUndirectedFeasible (toHamiltonianInstance i))
  | none => false

end MetaMathlibExt.Complexity.NPComplete.GridGraphMaxDegreeThreeHamiltonianPath
