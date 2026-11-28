/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INEQUIVALENCE OF PROGRAMS WITH ASSIGNMENTS for `V = {0, 1}`: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO12] INEQUIVALENCE OF PROGRAMS
WITH ASSIGNMENTS, p. 275 (comment: remains NP-complete for `V = {0, 1}`; reference
[Downey and Sethi, 1976]);
P. J. Downey and R. Sethi, "Assignment commands and array structures", Proceedings of the
17th Annual Symposium on Foundations of Computer Science (1976), 57-66,
doi:10.1109/SFCS.1976.7.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.InequivalenceProgramsAssignmentsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.InequivalenceProgramsAssignmentsBoolean

/-- Well-formedness of an instance: it is a well-formed INEQUIVALENCE OF PROGRAMS WITH
ASSIGNMENTS instance (every assignment names only variables of `X`), and the value set is
`V = {0, 1}` (`|V| = 2`). -/
def WellFormed
    (i : InequivalenceProgramsAssignments.InequivalenceProgramsAssignmentsInstance) : Prop :=
  InequivalenceProgramsAssignments.WellFormed i ∧ i.2.2.2 = 2

open Classical in
/-- INEQUIVALENCE OF PROGRAMS WITH ASSIGNMENTS for `V = {0, 1}` as a decision problem over
bitstrings. -/
noncomputable def inequivalenceProgramsAssignmentsBooleanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := InequivalenceProgramsAssignments.InequivalenceProgramsAssignmentsInstance) x with
  | some i =>
      decide (WellFormed i ∧
        InequivalenceProgramsAssignments.InequivalenceProgramsAssignmentsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.InequivalenceProgramsAssignmentsBoolean
