/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR TASKS, TOTAL COMPLETION TIME `P2|size_i|ΣC_i`: definitions

Source:
C.-Y. Lee and X. Cai, "Scheduling one and two-processor tasks on two parallel processors",
IIE Transactions 31 (1999), 445-455, doi:10.1080/07408179908969847 (only the abstract was
available);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `pmpt_nop` (multiprocessor tasks on
parallel processors, without preemption), entry `P2|size_i|ΣC_i` (minimal NP-hard, citing Lee
and Cai 1999);
K. Jansen and K. Kahler, "On the complexity of scheduling problems with a fixed number of
parallel identical machines", Lecture Notes in Computer Science, Springer, 192-206,
doi:10.1007/978-3-031-23101-8_13 (records that Lee and Cai proved `P2|size|ΣC_j` NP-hard and
that its strong NP-hardness is open).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorTaskSizeTotalCompletion

/-- An instance: the tasks `(p_i, size_i)` (processing time, size), one per entry, and the
bound `K`. -/
abbrev TwoProcessorTaskSizeTotalCompletionInstance := List (ℕ × ℕ) × ℕ

/-- Well-formedness: every task has size `1` or `2`. -/
def WellFormed (i : TwoProcessorTaskSizeTotalCompletionInstance) : Prop :=
  ∀ t ∈ i.1, 1 ≤ t.2 ∧ t.2 ≤ 2

/-- Start times `s` of the tasks `(p_j, size_j)` fit on two processors: at every time `t`, the
tasks running at `t` (`s j ≤ t < s j + p_j`) have total size at most `2`. -/
def FitsOnTwoProcessors (tasks : List (ℕ × ℕ)) (s : Fin tasks.length → ℕ) : Prop :=
  ∀ t : ℕ, ∑ j ∈ Finset.univ.filter (fun j => s j ≤ t ∧ t < s j + (tasks.get j).1),
    (tasks.get j).2 ≤ 2

/-- There are start times `s` that fit on two processors with total completion time
`∑_j (s j + p_j) ≤ K`. -/
def TwoProcessorTaskSizeTotalCompletionFeasible
    (i : TwoProcessorTaskSizeTotalCompletionInstance) : Prop :=
  ∃ s : Fin i.1.length → ℕ, FitsOnTwoProcessors i.1 s ∧ ∑ j, (s j + (i.1.get j).1) ≤ i.2

open Classical in
/-- `P2|size_i|ΣC_i` as a decision problem over bitstrings. -/
noncomputable def twoProcessorTaskSizeTotalCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoProcessorTaskSizeTotalCompletionInstance) x with
  | some i => decide (WellFormed i ∧ TwoProcessorTaskSizeTotalCompletionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorTaskSizeTotalCompletion
