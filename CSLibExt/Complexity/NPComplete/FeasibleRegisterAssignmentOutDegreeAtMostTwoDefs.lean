/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEASIBLE REGISTER ASSIGNMENT with out-degree at most 2: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 272, problem [PO2]
FEASIBLE REGISTER ASSIGNMENT (comment: remains NP-complete even if all vertices of `G` have
out-degree 2 or less);
R. Sethi, "Complete register allocation problems", SIAM Journal on Computing 4
(1975), 226-248, doi:10.1137/0204020.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.FeasibleRegisterAssignmentDefs
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeasibleRegisterAssignmentOutDegreeAtMostTwo

/-- Well-formedness of an instance: it is a well-formed FEASIBLE REGISTER ASSIGNMENT instance
(a directed acyclic graph, `K ≥ 1`, and a register index below `K` for each vertex), and every
vertex has out-degree at most 2. -/
def WellFormed (i : FeasibleRegisterAssignment.FeasibleRegisterAssignmentInstance) : Prop :=
  FeasibleRegisterAssignment.WellFormed i ∧
    ∀ v, {u | (RegisterSufficiency.Graph
      (FeasibleRegisterAssignment.toRegisterSufficiency i)).Adj v u}.ncard ≤ 2

open Classical in
/-- FEASIBLE REGISTER ASSIGNMENT with out-degree at most 2 as a decision problem over
bitstrings. -/
noncomputable def feasibleRegisterAssignmentOutDegreeAtMostTwoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FeasibleRegisterAssignment.FeasibleRegisterAssignmentInstance) x with
  | some i =>
    decide (WellFormed i ∧ FeasibleRegisterAssignment.FeasibleRegisterAssignmentFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.FeasibleRegisterAssignmentOutDegreeAtMostTwo
