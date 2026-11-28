/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# THREE-PROCESSOR UNIT-TIME NO-WAIT JOB-SHOP TOTAL COMPLETION TIME: definitions

Source:
C. Sriskandarajah and P. Ladet, "Some no-wait shops scheduling problems: complexity aspect",
European Journal of Operational Research 24 (1986), 424-438, doi:10.1016/0377-2217(86)90036-6
(`n/3/J, no-wait, pᵢⱼ = 1/F` is NP-hard; in three-field notation `J3|pᵢⱼ = 1; no-wait|∑ Cᵢ`);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
table "Job-shop problems with no-wait" (`J3|pᵢⱼ = 1; no-wait|∑ Cᵢ`, minimal NP-hard, credited to
Sriskandarajah and Ladet 1986);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS18] JOB-SHOP SCHEDULING (the
parent problem).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import CSLibExt.Complexity.NPComplete.JobShopSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeProcessorUnitNoWaitJobShopCompletionTime

open JobShopScheduling (JobShopSchedulingInstance taskLength taskProcessor)

/-- Well-formedness of an instance: the [SS18] instance is well-formed (`0 < m`, `1 ≤ n_j`,
processors in `{1, …, m}`, consecutive tasks of a job on different processors, `0 < K`),
`m = 3`, and every task has length `1`. -/
def WellFormed (i : JobShopSchedulingInstance) : Prop :=
  JobShopScheduling.WellFormed i ∧ i.1 = 3 ∧ ∀ job ∈ i.2.1, ∀ t ∈ job, t.1 = 1

/-- There is a no-wait job-shop schedule with total completion time at most `K`: start times
`σ` that are one-to-one on the tasks of each processor, such that a task of a processor starting
after another task `t'` of that processor starts no earlier than `t'` finishes, each task of a
job starts exactly when the previous task of that job finishes, and the completion times `C j`
(the finishing times of the last tasks) sum to at most `K`. -/
def ThreeProcessorUnitNoWaitJobShopCompletionTimeFeasible (i : JobShopSchedulingInstance) :
    Prop :=
  ∃ σ : JobShopScheduling.Task i → ℕ,
    (∀ t t', taskProcessor i t = taskProcessor i t' → σ t = σ t' → t = t') ∧
    (∀ t t', taskProcessor i t = taskProcessor i t' → σ t' < σ t →
      σ t' + taskLength i t' ≤ σ t) ∧
    (∀ j (k k' : Fin (i.2.1.get j).length), k'.1 = k.1 + 1 →
      σ ⟨j, k'⟩ = σ ⟨j, k⟩ + taskLength i ⟨j, k⟩) ∧
    ∃ C : Fin i.2.1.length → ℕ,
      (∀ j (k : Fin (i.2.1.get j).length), k.1 + 1 = (i.2.1.get j).length →
        C j = σ ⟨j, k⟩ + taskLength i ⟨j, k⟩) ∧
      ∑ j, C j ≤ i.2.2

open Classical in
/-- THREE-PROCESSOR UNIT-TIME NO-WAIT JOB-SHOP TOTAL COMPLETION TIME as a decision
problem over bitstrings. -/
noncomputable def threeProcessorUnitNoWaitJobShopCompletionTimeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := JobShopSchedulingInstance) x with
  | some i => decide (WellFormed i ∧ ThreeProcessorUnitNoWaitJobShopCompletionTimeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ThreeProcessorUnitNoWaitJobShopCompletionTime
