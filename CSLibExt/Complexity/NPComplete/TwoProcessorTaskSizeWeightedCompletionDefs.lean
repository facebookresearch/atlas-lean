/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR TASKS, TOTAL WEIGHTED COMPLETION TIME `P2|size_i|Σw_iC_i`: definitions

Source:
C.-Y. Lee and X. Cai, "Scheduling one and two-processor tasks on two parallel processors",
IIE Transactions 31 (1999), 445-455, doi:10.1080/07408179908969847 (only the abstract was
available);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `pmpt_nop` (multiprocessor tasks on
parallel processors, without preemption), entry `P2|size_i|Σw_iC_i` (minimal NP-hard in the
strong sense, citing Lee and Cai 1999).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.TwoProcessorTaskSizeTotalCompletionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorTaskSizeWeightedCompletion

open TwoProcessorTaskSizeTotalCompletion (TwoProcessorTaskSizeTotalCompletionInstance
  FitsOnTwoProcessors)

/-- An instance: a `P2|size_i|ΣC_i` instance (tasks `(p_i, size_i)`, bound `K`) and the weights,
task `j` having the `j`-th listed weight `w_j`. -/
abbrev TwoProcessorTaskSizeWeightedCompletionInstance :=
  TwoProcessorTaskSizeTotalCompletionInstance × List ℕ

/-- The weight `w_j` of task `j`. -/
def weight (i : TwoProcessorTaskSizeWeightedCompletionInstance) (j : Fin i.1.1.length) : ℕ :=
  i.2.getD j 0

/-- Well-formedness: a well-formed `P2|size_i|ΣC_i` instance (every size `1` or `2`) with one
weight per task. -/
def WellFormed (i : TwoProcessorTaskSizeWeightedCompletionInstance) : Prop :=
  TwoProcessorTaskSizeTotalCompletion.WellFormed i.1 ∧ i.2.length = i.1.1.length

/-- There are start times `s` that fit on two processors with total weighted completion time
`∑_j w_j (s j + p_j) ≤ K`. -/
def TwoProcessorTaskSizeWeightedCompletionFeasible
    (i : TwoProcessorTaskSizeWeightedCompletionInstance) : Prop :=
  ∃ s : Fin i.1.1.length → ℕ, FitsOnTwoProcessors i.1.1 s ∧
    ∑ j, weight i j * (s j + (i.1.1.get j).1) ≤ i.1.2

open Classical in
/-- `P2|size_i|Σw_iC_i` as a decision problem over bitstrings. -/
noncomputable def twoProcessorTaskSizeWeightedCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoProcessorTaskSizeWeightedCompletionInstance) x with
  | some i => decide (WellFormed i ∧ TwoProcessorTaskSizeWeightedCompletionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorTaskSizeWeightedCompletion
