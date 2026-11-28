/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NON-FREEDOM FOR LOOP-FREE PROGRAM SCHEMES with two variables: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 278, problem [PO19]
NON-FREEDOM FOR LOOP-FREE PROGRAM SCHEMES (reference: Constable, Hunt, and Sahni, 1974, a
Cornell technical report; comment: remains NP-complete for `|X| = 2`);
H. B. Hunt III, R. L. Constable, and S. Sahni, "On the computational complexity of program
scheme equivalence", SIAM Journal on Computing 9 (1980), 396-416, doi:10.1137/0209031, the
journal paper of that work.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.NonFreedomForLoopFreeProgramSchemesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.NonFreedomForLoopFreeProgramSchemesTwoVariables

/-- Well-formedness of an instance: it is a well-formed NON-FREEDOM FOR LOOP-FREE PROGRAM
SCHEMES instance (well-formed instructions, acyclic flow graph) with exactly two variables. -/
def WellFormed
    (i : NonFreedomForLoopFreeProgramSchemes.NonFreedomForLoopFreeProgramSchemesInstance) :
    Prop :=
  NonFreedomForLoopFreeProgramSchemes.WellFormed i ∧ i.2.2.1 = 2

open Classical in
/-- NON-FREEDOM FOR LOOP-FREE PROGRAM SCHEMES with two variables as a decision problem over
bitstrings. -/
noncomputable def nonFreedomForLoopFreeProgramSchemesTwoVariablesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := NonFreedomForLoopFreeProgramSchemes.NonFreedomForLoopFreeProgramSchemesInstance)
      x with
  | some i =>
    decide (WellFormed i ∧
      NonFreedomForLoopFreeProgramSchemes.NonFreedomForLoopFreeProgramSchemesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.NonFreedomForLoopFreeProgramSchemesTwoVariables
