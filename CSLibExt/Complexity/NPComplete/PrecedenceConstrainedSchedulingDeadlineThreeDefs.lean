/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PRECEDENCE CONSTRAINED SCHEDULING (deadline 3): definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS9] PRECEDENCE CONSTRAINED
SCHEDULING (comment: remains NP-complete for `D = 3`);
J. K. Lenstra and A. H. G. Rinnooy Kan, "Complexity of scheduling under precedence
constraints", Operations Research 26 (1978), 22-35, doi:10.1287/opre.26.1.22.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.PrecedenceConstrainedSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PrecedenceConstrainedSchedulingDeadlineThree

/-- Well-formedness of an instance: a well-formed PRECEDENCE CONSTRAINED SCHEDULING instance
whose deadline `D` is `3`. -/
def WellFormed (i : PrecedenceConstrainedScheduling.PrecedenceConstrainedSchedulingInstance) :
    Prop :=
  PrecedenceConstrainedScheduling.WellFormed i ∧ i.2.2.2 = 3

open Classical in
/-- PRECEDENCE CONSTRAINED SCHEDULING (deadline 3) as a decision problem over bitstrings. -/
noncomputable def precedenceConstrainedSchedulingDeadlineThreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PrecedenceConstrainedScheduling.PrecedenceConstrainedSchedulingInstance) x with
  | some i =>
    decide (WellFormed i ∧
      PrecedenceConstrainedScheduling.PrecedenceConstrainedSchedulingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PrecedenceConstrainedSchedulingDeadlineThree
