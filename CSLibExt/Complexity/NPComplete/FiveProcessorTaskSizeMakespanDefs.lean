/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FIVE-PROCESSOR TASKS, MAKESPAN `P5|size_i|C_max`: definitions

Source:
J. Du and J. Y.-T. Leung, "Complexity of scheduling parallel task systems", SIAM Journal on
Discrete Mathematics 2 (1989), 473-487, doi:10.1137/0402042 (only the abstract was available);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `pmpt_nop` (multiprocessor tasks on
parallel processors, without preemption), entry `P5|size_i|C_max` (minimal NP-hard in the
strong sense, citing Du and Leung 1989).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.RCPSPDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FiveProcessorTaskSizeMakespan

open RCPSP (RCPSPInstance RCPSPFeasible)

/-- Well-formedness of an instance: a well-formed RESOURCE-CONSTRAINED PROJECT SCHEDULING
instance with no precedence pairs and capacity `5` (the five processors), every task having a
positive processing time and size `1 ≤ size_i ≤ 5`. -/
def WellFormed (i : RCPSPInstance) : Prop :=
  RCPSP.WellFormed i ∧ i.2.1 = [] ∧ i.2.2.1 = 5 ∧ ∀ t ∈ i.1, 0 < t.1 ∧ 1 ≤ t.2 ∧ t.2 ≤ 5

open Classical in
/-- `P5|size_i|C_max` as a decision problem over bitstrings. -/
noncomputable def fiveProcessorTaskSizeMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := RCPSPInstance) x with
  | some i => decide (WellFormed i ∧ RCPSPFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.FiveProcessorTaskSizeMakespan
