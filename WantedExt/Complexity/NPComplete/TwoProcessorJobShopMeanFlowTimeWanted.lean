/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR JOB-SHOP MEAN FLOW TIME (J2||ΣC_i) is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import WantedExt.Complexity.NPComplete.JobShopSchedulingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorJobShopMeanFlowTime

open JobShopScheduling (JobShopSchedulingInstance taskLength taskProcessor)

/-!
# TWO-PROCESSOR JOB-SHOP MEAN FLOW TIME (J2||ΣC_i) is NP-complete

INSTANCE: `m = 2` processors, a set `J` of jobs, each job `j ∈ J` consisting of an ordered
collection of tasks `t_k[j]`, `1 ≤ k ≤ n_j`, for each such task `t` a length `l(t) ∈ ℤ₀⁺` and a
processor `p(t) ∈ {1, 2}`, where `p(t_k[j]) ≠ p(t_{k+1}[j])` for all `j ∈ J` and
`1 ≤ k < n_j`, and a bound `K ∈ ℤ⁺`. QUESTION: is there a job-shop schedule for `J` whose total
completion time `∑_{j ∈ J} C_j` is at most `K`, `C_j = σ(t_{n_j}[j]) + l(t_{n_j}[j])` being the
time the last task of `j` finishes? (The mean flow time is that sum divided by `|J|`.)

This is `J2||ΣC_i` in the Brucker-Knust classification: JOB-SHOP SCHEDULING ([SS18],
`JobShopSchedulingWanted`) with `m = 2` and the deadline replaced by a bound `K` on the sum of
the completion times. The instance type `JobShopScheduling.JobShopSchedulingInstance`,
`JobShopScheduling.WellFormed` (which includes `n_j ≥ 1`), the tasks and their lengths and
processors are the parent's; the last component of the instance is the bound `K ∈ ℤ⁺` in place
of the deadline `D ∈ ℤ⁺`, and `WellFormed` adds `m = 2`. The schedule conditions are the
parent's (start times one-to-one on the tasks of each processor, one task at a time on each
processor, the tasks of a job in order), with the parent's deadline condition replaced by the
bound on `∑ C_j`, where `C j` is pinned to the finishing time of the last task of `j`. Task
positions are numbered from `0`. Binary encoding of all numbers.

The number `n_j` of tasks of a job is not bounded, as in [SS18] and in Brucker and Knust's
job-shop class `J`: a job alternates between the two processors and may visit each several
times. (In both, `J2||C_max` is NP-hard in the strong sense, while its restriction to jobs with
at most one task per processor, `n_j ≤ 2`, is solvable in polynomial time by Jackson's rule.)

TWO-PROCESSOR FLOW-SHOP MEAN FLOW TIME (`TwoProcessorFlowShopMeanFlowTimeWanted`; Garey,
Johnson and Sethi 1976) is the special case in which every job has exactly two tasks, the
first on processor `1` and the second on processor `2`; its schedule conditions are then the
ones stated here. Brucker and Knust record `J2||ΣC_i` as NP-hard in the strong sense with that
citation.

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

/-- **TWO-PROCESSOR JOB-SHOP MEAN FLOW TIME (`J2||ΣC_i`) is NP-complete.** Source: Garey and
Johnson (1979), [SS18] and [SS15], comment; Garey, Johnson and Sethi (1976); Brucker and
Knust's classification. -/
public theorem_wanted twoProcessorJobShopMeanFlowTime_npComplete :
    twoProcessorJobShopMeanFlowTimeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoProcessorJobShopMeanFlowTimeDec

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorJobShopMeanFlowTime
