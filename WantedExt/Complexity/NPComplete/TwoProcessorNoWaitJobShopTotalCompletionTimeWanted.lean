/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR NO-WAIT JOB-SHOP TOTAL COMPLETION TIME is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import WantedExt.Complexity.NPComplete.JobShopSchedulingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorNoWaitJobShopTotalCompletionTime

/-!
# TWO-PROCESSOR NO-WAIT JOB-SHOP TOTAL COMPLETION TIME is NP-complete

INSTANCE: `m = 2` processors, a set `J` of jobs, each job `j ∈ J` consisting of an ordered
collection of tasks `t_k[j]`, `1 ≤ k ≤ n_j`, for each such task `t` a length `l(t) ∈ ℤ₀⁺` and a
processor `p(t) ∈ {1, 2}`, where `p(t_k[j]) ≠ p(t_{k+1}[j])` for all `j ∈ J` and `1 ≤ k < n_j`,
and a bound `K ∈ ℤ⁺`.
QUESTION: is there a job-shop schedule for `J` with no wait in process, i.e.
`σ(t_{k+1}[j]) = σ(t_k[j]) + l(t_k[j])` for all `j ∈ J` and `1 ≤ k < n_j`, such that the sum,
over all `j ∈ J`, of the completion times `C_j = σ(t_{n_j}[j]) + l(t_{n_j}[j])` is at most `K`?

In the Brucker-Knust notation this is `J2|no-wait|∑ C_i`. It is the no-wait version of
JOB-SHOP SCHEDULING ([SS18], `JobShopSchedulingWanted`) with `m = 2`, with the overall deadline
replaced by a bound `K` on the sum of the completion times, as Garey and Johnson do for
NO-WAIT FLOW-SHOP SCHEDULING in the comment to [SS16]. The instance type,
`JobShopScheduling.WellFormed`, `JobShopScheduling.Task`, `JobShopScheduling.taskLength` and
`JobShopScheduling.taskProcessor` are the parent's, unchanged; the last component of the
instance is the bound `K ∈ ℤ⁺` in place of the deadline `D ∈ ℤ⁺` (following Garey and
Johnson's convention for such bounds; `K = 0` is excluded by the parent's well-formedness), and
`WellFormed` adds `m = 2`. The schedule conditions are the parent's (one-processor schedules
[SS1] and the job order) plus the no-wait equality; the parent's deadline conjunct is replaced
by the sum bound. Every job has at least one task (parent's well-formedness), so `C_j` is
determined. Task positions are numbered from `0` below.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **TWO-PROCESSOR NO-WAIT JOB-SHOP TOTAL COMPLETION TIME is NP-complete.** Source: Röck
(1984); Brucker and Knust, class table "Job-shop problems with nowait"; Garey and Johnson
(1979), [SS16] and [SS18]. -/
public theorem_wanted twoProcessorNoWaitJobShopTotalCompletionTime_npComplete :
    twoProcessorNoWaitJobShopTotalCompletionTimeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoProcessorNoWaitJobShopTotalCompletionTimeDec

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorNoWaitJobShopTotalCompletionTime
