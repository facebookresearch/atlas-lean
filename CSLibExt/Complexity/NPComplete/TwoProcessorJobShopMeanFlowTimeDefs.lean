/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR JOB-SHOP MEAN FLOW TIME (J2||ΣC_i): definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS18] JOB-SHOP SCHEDULING (the
parent problem) and problem [SS15] FLOW-SHOP SCHEDULING, p. 241 (comment: with a bound `K` on
the sum of the completion times in place of the deadline, the problem is NP-complete in the
strong sense even if `m = 2`);
M. R. Garey, D. S. Johnson and R. Sethi, "The complexity of flowshop and jobshop scheduling",
Mathematics of Operations Research 1 (1976), 117-129, doi:10.1287/moor.1.2.117;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `j_nop`, entry `J2||ΣC_i`
(minimal NP-hard in the strong sense, citing Garey, Johnson and Sethi 1976).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import CSLibExt.Complexity.NPComplete.JobShopSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorJobShopMeanFlowTime

open JobShopScheduling (JobShopSchedulingInstance taskLength taskProcessor)

/-- Well-formedness of an instance: the parent's (`0 < m`, `1 ≤ n_j`, processors in
`{1, …, m}`, consecutive tasks of a job on different processors, `0 < K` in the place of the
deadline) and `m = 2`. -/
def WellFormed (i : JobShopSchedulingInstance) : Prop :=
  JobShopScheduling.WellFormed i ∧ i.1 = 2

/-- There is a job-shop schedule with total completion time at most `K`: start times `σ` that
are one-to-one on the tasks of each processor, such that a task of a processor starting after
another task `t'` of that processor starts no earlier than `t'` finishes, each task of a job
starts no earlier than the previous task of that job finishes, and the completion times `C j`
(the finishing times of the last tasks) sum to at most `K`. -/
def TwoProcessorJobShopMeanFlowTimeFeasible (i : JobShopSchedulingInstance) : Prop :=
  ∃ σ : JobShopScheduling.Task i → ℕ,
    (∀ t t', taskProcessor i t = taskProcessor i t' → σ t = σ t' → t = t') ∧
    (∀ t t', taskProcessor i t = taskProcessor i t' → σ t' < σ t →
      σ t' + taskLength i t' ≤ σ t) ∧
    (∀ j (k k' : Fin (i.2.1.get j).length), k'.1 = k.1 + 1 →
      σ ⟨j, k⟩ + taskLength i ⟨j, k⟩ ≤ σ ⟨j, k'⟩) ∧
    ∃ C : Fin i.2.1.length → ℕ,
      (∀ j (k : Fin (i.2.1.get j).length), k.1 + 1 = (i.2.1.get j).length →
        C j = σ ⟨j, k⟩ + taskLength i ⟨j, k⟩) ∧
      ∑ j, C j ≤ i.2.2

open Classical in
/-- TWO-PROCESSOR JOB-SHOP MEAN FLOW TIME as a decision problem over bitstrings. -/
noncomputable def twoProcessorJobShopMeanFlowTimeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := JobShopSchedulingInstance) x with
  | some i => decide (WellFormed i ∧ TwoProcessorJobShopMeanFlowTimeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorJobShopMeanFlowTime
