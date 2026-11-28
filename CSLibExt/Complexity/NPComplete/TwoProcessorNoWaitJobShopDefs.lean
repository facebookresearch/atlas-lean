/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR NO-WAIT JOB-SHOP SCHEDULING: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS16] NO-WAIT FLOW-SHOP SCHEDULING,
p. 242 (comment: "The analogous 'no-wait' versions of OPEN-SHOP SCHEDULING and JOB-SHOP
SCHEDULING are NP-complete in the strong sense for `m = 2`"), with JOB-SHOP SCHEDULING [SS18];
S. Sahni and Y. Cho, "Complexity of scheduling shops with no wait in process", Mathematics of
Operations Research 4 (1979), 448-457, doi:10.1287/moor.4.4.448.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.JobShopSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorNoWaitJobShop

/-- Well-formedness of an instance: the parent's (`0 < m`, `1 ≤ n_j`, processors in
`{1, …, m}`, consecutive tasks of a job on different processors, `0 < D`) and `m = 2`. -/
def WellFormed (i : JobShopScheduling.JobShopSchedulingInstance) : Prop :=
  JobShopScheduling.WellFormed i ∧ i.1 = 2

open JobShopScheduling (Task taskLength taskProcessor) in
/-- There is a no-wait job-shop schedule meeting the deadline: start times `σ` that are
one-to-one on the tasks of each processor, such that a task of a processor starting after
another task `t'` of that processor starts no earlier than `t'` finishes, each task of a job
starts no earlier than the previous task of that job finishes, the last task of every job
finishes by `D`, and each task of a job after the first starts exactly when the previous task
of that job finishes. -/
def TwoProcessorNoWaitJobShopFeasible (i : JobShopScheduling.JobShopSchedulingInstance) :
    Prop :=
  ∃ σ : Task i → ℕ,
    (∀ t t', taskProcessor i t = taskProcessor i t' → σ t = σ t' → t = t') ∧
    (∀ t t', taskProcessor i t = taskProcessor i t' → σ t' < σ t →
      σ t' + taskLength i t' ≤ σ t) ∧
    (∀ j (k k' : Fin (i.2.1.get j).length), k'.1 = k.1 + 1 →
      σ ⟨j, k⟩ + taskLength i ⟨j, k⟩ ≤ σ ⟨j, k'⟩) ∧
    (∀ j (k : Fin (i.2.1.get j).length), k.1 + 1 = (i.2.1.get j).length →
      σ ⟨j, k⟩ + taskLength i ⟨j, k⟩ ≤ i.2.2) ∧
    ∀ j (k k' : Fin (i.2.1.get j).length), k'.1 = k.1 + 1 →
      σ ⟨j, k'⟩ = σ ⟨j, k⟩ + taskLength i ⟨j, k⟩

open Classical in
/-- TWO-PROCESSOR NO-WAIT JOB-SHOP SCHEDULING as a decision problem over bitstrings. -/
noncomputable def twoProcessorNoWaitJobShopDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := JobShopScheduling.JobShopSchedulingInstance) x with
  | some i => decide (WellFormed i ∧ TwoProcessorNoWaitJobShopFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorNoWaitJobShop
