/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# THREE-PROCESSOR UNIT-TIME NO-WAIT JOB-SHOP TOTAL COMPLETION TIME is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import WantedExt.Complexity.NPComplete.JobShopSchedulingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeProcessorUnitNoWaitJobShopCompletionTime

open JobShopScheduling (JobShopSchedulingInstance taskLength taskProcessor)

/-!
# THREE-PROCESSOR UNIT-TIME NO-WAIT JOB-SHOP TOTAL COMPLETION TIME is NP-complete

INSTANCE: `m = 3` processors, a set `J` of jobs, each job `j ∈ J` consisting of an ordered
collection of tasks `t_k[j]`, `1 ≤ k ≤ n_j`, each of length `l(t) = 1` and with a processor
`p(t) ∈ {1, 2, 3}`, where `p(t_k[j]) ≠ p(t_{k+1}[j])`, and a bound `K ∈ ℤ⁺`. QUESTION: is there a
job-shop schedule for `J` in which every task of a job starts exactly when the previous task of
that job finishes (no wait), and whose total completion time `∑_{j ∈ J} C_j` is at most `K`,
`C_j` being the time the last task of `j` finishes?

This is `J3|pᵢⱼ = 1; no-wait|∑ Cᵢ`: JOB-SHOP SCHEDULING ([SS18], `JobShopSchedulingWanted`) with
`m = 3`, unit task lengths, the no-wait condition, and the deadline replaced by a bound `K` on the
total completion time (Sriskandarajah and Ladet's `n/3/J, no-wait, pᵢⱼ = 1/F`, `F` the total
flow time, which with all jobs available at time `0` is `∑ Cᵢ`). The instance type
`JobShopScheduling.JobShopSchedulingInstance`, `JobShopScheduling.WellFormed` (which includes
`n_j ≥ 1`), the tasks and their lengths and processors are the parent's; the last component of
the instance is the bound `K ∈ ℤ⁺` in place of the deadline `D ∈ ℤ⁺`. The schedule conditions
are the parent's (one-to-one start times on each processor, one task at a time on each
processor), the parent's job-order condition `σ(t_{k+1}[j]) ≥ σ(t_k[j]) + l(t_k[j])` strengthened
to equality (no wait), and the parent's deadline condition replaced by the bound on `∑ C_j`,
where `C j` is pinned to the finishing time of the last task of `j` (every job has a task,
`n_j ≥ 1`). Unit lengths are a well-formedness condition. Task positions are numbered from `0`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **THREE-PROCESSOR UNIT-TIME NO-WAIT JOB-SHOP TOTAL COMPLETION TIME is
NP-complete.** Source: Sriskandarajah and Ladet (1986); Brucker and Knust's classification
(`J3|pᵢⱼ = 1; no-wait|∑ Cᵢ`). -/
public theorem_wanted threeProcessorUnitNoWaitJobShopCompletionTime_npComplete :
    threeProcessorUnitNoWaitJobShopCompletionTimeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L threeProcessorUnitNoWaitJobShopCompletionTimeDec

end MetaMathlibExt.Complexity.NPComplete.ThreeProcessorUnitNoWaitJobShopCompletionTime
