/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TIMETABLE DESIGN with three work periods: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 243, problem [SS19] TIMETABLE
DESIGN, comment: "Remains NP-complete even if `|H| = 3`, `A(t) = H` for all `t ∈ T`, and each
`R(c, t) ∈ {0, 1}`";
S. Even, A. Itai, and A. Shamir, "On the complexity of timetable and
multicommodity flow problems", SIAM Journal on Computing 5 (1976), 691-703,
doi:10.1137/0205048 (the reference Garey and Johnson give for [SS19]).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.TimetableDesignDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TimetableDesignThreePeriods

open MetaMathlibExt.Complexity.NPComplete.TimetableDesign

/-- Well-formedness of an instance of the restriction: the instance is a well-formed TIMETABLE
DESIGN instance, `|H| = 3`, every task's list of available hours contains every period, and
every requirement `R(c, t)` is `0` or `1`. -/
def RestrictedWellFormed (i : TimetableDesignInstance) : Prop :=
  WellFormed i ∧ i.1 = 3 ∧ (∀ a ∈ i.2.2.2.2.1, ∀ h < i.1, h ∈ a) ∧
    ∀ row ∈ i.2.2.2.2.2, ∀ r ∈ row, r ≤ 1

open Classical in
/-- TIMETABLE DESIGN with three work periods, as a decision
problem over bitstrings. -/
noncomputable def timetableDesignThreePeriodsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TimetableDesignInstance) x with
  | some i => decide (RestrictedWellFormed i ∧ TimetableDesignFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TimetableDesignThreePeriods
