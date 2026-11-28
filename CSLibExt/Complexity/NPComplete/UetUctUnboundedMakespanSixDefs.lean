/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UET-UCT SCHEDULING ON UNBOUNDEDLY MANY PROCESSORS WITH MAKESPAN AT MOST 6: definitions

Source:
J. A. Hoogeveen, J. K. Lenstra and B. Veltman, "Three, four, five, six, or the complexity of
scheduling with communication delays", Operations Research Letters 16 (1994), 129-137,
doi:10.1016/0167-6377(94)90024-8 (problem `P̄|prec,c=1,p_j=1|C_max`, schedule of length at most
6; Theorem 4 of the preprint, CWI Report BS-R9229, 1992).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.UetUctSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UetUctUnboundedMakespanSix

open MetaMathlibExt.Complexity.NPComplete.UetUctScheduling (UetUctSchedulingInstance)

/-- Well-formedness of an instance: a well-formed UET-UCT SCHEDULING instance with at least as
many machines as jobs (`n ≤ m`, so the number of machines is not restrictive) and bound
`d = 6`. -/
def WellFormed (i : UetUctSchedulingInstance) : Prop :=
  UetUctScheduling.WellFormed i ∧ i.2.1.length ≤ i.1 ∧ i.2.2.2 = 6

open Classical in
/-- UET-UCT SCHEDULING ON UNBOUNDEDLY MANY PROCESSORS WITH MAKESPAN AT MOST 6 as a decision
problem over bitstrings. -/
noncomputable def uetUctUnboundedMakespanSixDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := UetUctSchedulingInstance) x with
  | some i => decide (WellFormed i ∧ UetUctScheduling.UetUctSchedulingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UetUctUnboundedMakespanSix
