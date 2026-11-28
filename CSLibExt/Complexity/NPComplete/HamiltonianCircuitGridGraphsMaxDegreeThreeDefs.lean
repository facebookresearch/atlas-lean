/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT IN GRID GRAPHS OF MAXIMUM DEGREE 3: definitions

Source:
C. H. Papadimitriou and U. V. Vazirani, "On two geometric problems related to the travelling
salesman problem", Journal of Algorithms 5 (1984), 231-246, doi:10.1016/0196-6774(84)90029-4;
A. Itai, C. H. Papadimitriou and J. L. Szwarcfiter, "Hamilton paths in grid graphs", SIAM Journal
on Computing 11 (1982), 676-686, doi:10.1137/0211056;
E. M. Arkin, S. P. Fekete, K. Islam, H. Meijer, J. S. B. Mitchell, Y. Núñez-Rodríguez,
V. Polishchuk, D. Rappaport and H. Xiao, "Not being (super)thin or solid is hard: A study of grid
Hamiltonicity", Computational Geometry 42 (2009), 582-605, doi:10.1016/j.comgeo.2008.11.004.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GridGraphHamiltonianCircuitDefs
public import CSLibExt.Complexity.NPComplete.HamiltonianCycleUndirectedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitGridGraphsMaxDegreeThree

open MetaMathlibExt.Complexity.NPComplete.GridGraphHamiltonianCircuit
  (GridGraphHamiltonianCircuitInstance toHamiltonianInstance)

open Classical in
/-- Well-formedness of an instance: a well-formed HAMILTONIAN CIRCUIT IN GRID GRAPHS instance
(pairwise distinct points) whose grid graph has every vertex of degree at most 3. -/
def WellFormed (i : GridGraphHamiltonianCircuitInstance) : Prop :=
  GridGraphHamiltonianCircuit.WellFormed i ∧
    ∀ v, (HamiltonianCycleUndirected.Graph (toHamiltonianInstance i)).degree v ≤ 3

open Classical in
/-- HAMILTONIAN CIRCUIT IN GRID GRAPHS OF MAXIMUM DEGREE 3 as a decision problem over bitstrings. -/
noncomputable def hamiltonianCircuitGridGraphsMaxDegreeThreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GridGraphHamiltonianCircuitInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianCycleUndirected.HamiltonianCycleUndirectedFeasible
      (toHamiltonianInstance i))
  | none => false

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitGridGraphsMaxDegreeThree
