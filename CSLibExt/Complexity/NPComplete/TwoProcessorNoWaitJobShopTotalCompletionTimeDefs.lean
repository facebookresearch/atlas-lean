/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR NO-WAIT JOB-SHOP TOTAL COMPLETION TIME: definitions

Source:
H. Röck, "Some new results in flow shop scheduling", Zeitschrift für Operations Research 28
(1984), 1-16, doi:10.1007/BF01919082 (the two-processor no-wait flow shop with total completion
time, `F2|no-wait|∑ C_i`, is NP-hard in the strong sense; it is the special case of this problem
in which every job has a task on processor 1 followed by a task on processor 2);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class table "Job-shop problems with nowait" (`J2|no-wait|∑ C_i`: minimal NP-hard in the strong
sense, Röck (1984));
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problems [SS18] JOB-SHOP SCHEDULING and [SS16] NO-WAIT
FLOW-SHOP SCHEDULING (definitions; the comment to [SS16] states the sum bound `K` and the
no-wait versions of JOB-SHOP SCHEDULING).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import CSLibExt.Complexity.NPComplete.JobShopSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorNoWaitJobShopTotalCompletionTime

/-- Well-formedness of an instance: the parent's (`0 < m`, `1 ≤ n_j`, processors in
`{1, …, m}`, consecutive tasks of a job on different processors, `0 < K` in the last component)
and `m = 2`. -/
def WellFormed (i : JobShopScheduling.JobShopSchedulingInstance) : Prop :=
  JobShopScheduling.WellFormed i ∧ i.1 = 2

open JobShopScheduling (Task taskLength taskProcessor) in
/-- There is a no-wait job-shop schedule with total completion time at most `K`: start times
`σ` that are one-to-one on the tasks of each processor, such that a task of a processor starting
after another task `t'` of that processor starts no earlier than `t'` finishes, each task of a
job starts no earlier than the previous task of that job finishes, and each task of a job after
the first starts exactly when the previous task of that job finishes, together with completion
times `C j` equal to the finishing time of the last task of job `j`, whose sum is at most
`K`. -/
def TwoProcessorNoWaitJobShopTotalCompletionTimeFeasible
    (i : JobShopScheduling.JobShopSchedulingInstance) : Prop :=
  ∃ σ : Task i → ℕ,
    (∀ t t', taskProcessor i t = taskProcessor i t' → σ t = σ t' → t = t') ∧
    (∀ t t', taskProcessor i t = taskProcessor i t' → σ t' < σ t →
      σ t' + taskLength i t' ≤ σ t) ∧
    (∀ j (k k' : Fin (i.2.1.get j).length), k'.1 = k.1 + 1 →
      σ ⟨j, k⟩ + taskLength i ⟨j, k⟩ ≤ σ ⟨j, k'⟩) ∧
    (∀ j (k k' : Fin (i.2.1.get j).length), k'.1 = k.1 + 1 →
      σ ⟨j, k'⟩ = σ ⟨j, k⟩ + taskLength i ⟨j, k⟩) ∧
    ∃ C : Fin i.2.1.length → ℕ,
      (∀ j (k : Fin (i.2.1.get j).length), k.1 + 1 = (i.2.1.get j).length →
        C j = σ ⟨j, k⟩ + taskLength i ⟨j, k⟩) ∧
      ∑ j, C j ≤ i.2.2

open Classical in
/-- TWO-PROCESSOR NO-WAIT JOB-SHOP TOTAL COMPLETION TIME as a decision problem over
bitstrings. -/
noncomputable def twoProcessorNoWaitJobShopTotalCompletionTimeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := JobShopScheduling.JobShopSchedulingInstance) x with
  | some i => decide (WellFormed i ∧ TwoProcessorNoWaitJobShopTotalCompletionTimeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorNoWaitJobShopTotalCompletionTime
