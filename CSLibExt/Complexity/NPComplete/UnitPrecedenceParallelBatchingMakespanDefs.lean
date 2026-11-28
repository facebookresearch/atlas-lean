/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARALLEL BATCHING `1|prec;p_i=1;p-batch;b<n|C_max`: definitions

Source:
P. Brucker, A. Gladky, H. Hoogeveen, M. Y. Kovalyov, C. N. Potts, T. Tautenhahn and
S. L. van de Velde, "Scheduling a batching machine", Journal of Scheduling 1 (1998), 31-54,
doi:10.1002/(SICI)1099-1425(199806)1:1<31::AID-JOS4>3.0.CO;2-R (the parallel batching model);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class "Parallel batching problems"
(`1|prec;p_i=1;p-batch;b<n|C_max`, minimal NP-hard in the strong sense,
by reduction from the parallel machine problem `P|prec;p_i=1|C_max`);
J. D. Ullman, "NP-complete scheduling problems", Journal of Computer and System Sciences 10
(1975), 384-393, doi:10.1016/S0022-0000(75)80008-0 (`P|prec;p_i=1|C_max`; Garey and Johnson,
[SS9]).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.PrecedenceConstrainedSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitPrecedenceParallelBatchingMakespan

open MetaMathlibExt.Complexity.NPComplete.PrecedenceConstrainedScheduling
  (PrecedenceConstrainedSchedulingInstance PrecedenceConstrainedSchedulingFeasible)

/-- Well-formedness of an instance: it is well-formed for PRECEDENCE CONSTRAINED SCHEDULING (unit
lengths, `b > 0`, the listed pairs name jobs and form a strict partial order, `K > 0`), and the
batch capacity is bounded: `b < n`. -/
def WellFormed (i : PrecedenceConstrainedSchedulingInstance) : Prop :=
  PrecedenceConstrainedScheduling.WellFormed i ∧ i.2.1 < i.1.length

open Classical in
/-- `1|prec;p_i=1;p-batch;b<n|C_max` as a decision problem over bitstrings. -/
noncomputable def unitPrecedenceParallelBatchingMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PrecedenceConstrainedSchedulingInstance) x with
  | some i => decide (WellFormed i ∧ PrecedenceConstrainedSchedulingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UnitPrecedenceParallelBatchingMakespan
