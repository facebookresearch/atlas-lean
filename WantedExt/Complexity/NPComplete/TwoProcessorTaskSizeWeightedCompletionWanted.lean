/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR TASKS, TOTAL WEIGHTED COMPLETION TIME `P2|size_i|Σw_iC_i` is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.TwoProcessorTaskSizeTotalCompletionWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorTaskSizeWeightedCompletion

open TwoProcessorTaskSizeTotalCompletion (TwoProcessorTaskSizeTotalCompletionInstance
  FitsOnTwoProcessors)

/-!
# TWO-PROCESSOR TASKS, TOTAL WEIGHTED COMPLETION TIME `P2|size_i|Σw_iC_i` is NP-complete

INSTANCE: two identical processors, each executing at most one task at a time; `n` tasks, task
`i` with a processing time `p_i ∈ ℤ₀⁺`, a size `size_i ∈ {1, 2}` (the task uses `size_i`
processors, any of them, simultaneously during its whole uninterrupted processing) and a weight
`w_i ∈ ℤ₀⁺`; and a bound `K`. QUESTION: is there a schedule with total weighted completion time
`∑_i w_i C_i ≤ K`, where `C_i` is the completion time of task `i`?

Lee and Cai's abstract: for two processors where some tasks are processed by one processor and
the others by both processors simultaneously, minimizing the total weighted completion time "is
NP-complete in the strong sense". The Brucker-Knust tables record `P2|size_i|Σw_iC_i` as minimal
NP-hard in the strong sense, credited to Lee and Cai.

Encoding. The processors, tasks and bound are a `P2|size_i|ΣC_i` instance
(`TwoProcessorTaskSizeTotalCompletionWanted`: tasks `(p_i, size_i)` listed one per entry, sizes
`1` or `2`, and the bound `K`), whose schedules are reused: start times `s` with
`FitsOnTwoProcessors` (at every time the running tasks have total size at most `2`, which is
exactly when processors can be assigned; see that module), so `C_i = s_i + p_i`. The weights are
listed one per task. Natural start times lose no generality: rounding all start times down keeps
the capacity and does not increase the weighted total. Membership in NP is the certificate
argument: in a yes-instance every task of positive weight completes by `K`, and the tasks of
weight `0` can be moved to run one after another from time `K` on, so all start times are at
most `K + ∑_i p_i` and are checked in polynomial time.
Binary encoding of all numbers (the problem is NP-hard in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **TWO-PROCESSOR TASKS, TOTAL WEIGHTED COMPLETION TIME `P2|size_i|Σw_iC_i` is
NP-complete.** Source: Lee and Cai (1999), as recorded in the Brucker-Knust classification. -/
public theorem_wanted twoProcessorTaskSizeWeightedCompletion_npComplete :
    twoProcessorTaskSizeWeightedCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoProcessorTaskSizeWeightedCompletionDec

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorTaskSizeWeightedCompletion
