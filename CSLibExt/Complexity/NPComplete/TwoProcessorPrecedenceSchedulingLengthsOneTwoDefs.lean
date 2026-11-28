/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR PRECEDENCE CONSTRAINED SCHEDULING (task lengths 1 and 2): definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS9] PRECEDENCE CONSTRAINED
SCHEDULING (comment: the `m = 2` case becomes NP-complete if both task lengths 1 and 2 are
allowed);
J. D. Ullman, "NP-complete scheduling problems", Journal of Computer and System Sciences 10
(1975), 384-393, doi:10.1016/S0022-0000(75)80008-0.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Order.Defs.Unbundled
public import CSLibExt.Complexity.NPComplete.PrecedenceConstrainedSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorPrecedenceSchedulingLengthsOneTwo

/-- Well-formedness of an instance: every task has length `1` or `2`, the number `m` of
processors is `2`, every listed pair names two tasks, the listed pairs form a strict partial
order, and `D` is positive. -/
def WellFormed (i : PrecedenceConstrainedScheduling.PrecedenceConstrainedSchedulingInstance) :
    Prop :=
  (∀ l ∈ i.1, l = 1 ∨ l = 2) ∧ i.2.1 = 2 ∧
    (∀ p ∈ i.2.2.1, p.1 < i.1.length ∧ p.2 < i.1.length) ∧
    IsStrictOrder (PrecedenceConstrainedScheduling.Task i)
      (PrecedenceConstrainedScheduling.Prec i) ∧ 0 < i.2.2.2

open Classical in
/-- TWO-PROCESSOR PRECEDENCE CONSTRAINED SCHEDULING (task lengths 1 and 2) as a decision
problem over bitstrings. -/
noncomputable def twoProcessorPrecedenceSchedulingLengthsOneTwoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PrecedenceConstrainedScheduling.PrecedenceConstrainedSchedulingInstance) x with
  | some i =>
    decide (WellFormed i ∧
      PrecedenceConstrainedScheduling.PrecedenceConstrainedSchedulingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorPrecedenceSchedulingLengthsOneTwo
