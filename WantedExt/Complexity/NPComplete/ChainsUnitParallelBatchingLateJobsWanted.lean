/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARALLEL BATCHING `1|chains;p_i=1;p-batch;b<n|ΣU_i` is NP-complete

Source:
P. Brucker, A. Gladky, H. Hoogeveen, M. Y. Kovalyov, C. N. Potts, T. Tautenhahn and
S. L. van de Velde, "Scheduling a batching machine", Journal of Scheduling 1 (1998), 31-54,
doi:10.1002/(SICI)1099-1425(199806)1:1<31::AID-JOS4>3.0.CO;2-R (the parallel batching model);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class "Parallel batching problems"
(`1|chains;p_i=1;p-batch;b<n|ΣU_i`, minimal NP-hard in the strong sense,
by reduction from the single machine problem `1|chains;p_i=1|ΣU_i`);
J. K. Lenstra and A. H. G. Rinnooy Kan, "Complexity results for scheduling chains on a single
machine", European Journal of Operational Research 4 (1980), 270-275,
doi:10.1016/0377-2217(80)90111-3, Theorem 1 (`1|chains, p_j = 1|ΣU_j`; Garey and Johnson,
[SS2], comment).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.TardyTasksUnitChainsWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChainsUnitParallelBatchingLateJobs

open MetaMathlibExt.Complexity.NPComplete.TardyTasksUnitChains
  (TardyTasksUnitChainsInstance Task deadline Prec)

/-!
# PARALLEL BATCHING `1|chains;p_i=1;p-batch;b<n|ΣU_i` is NP-complete

INSTANCE: `n` jobs, each with unit processing time `p_i = 1` and a due date `d_i`, to be
processed in batches on a single machine; a batch capacity `b ∈ ℤ⁺` with `b < n`; a precedence
relation on the jobs consisting of chains (every job has at most one immediate predecessor and
at most one immediate successor): if `i` precedes `j`, then `j` cannot start before `i` is
completed; and a bound `K`. QUESTION: is there a feasible schedule with at most `K` late jobs
(`ΣU_i ≤ K`, where job `i` is late when its completion time `C_i` exceeds `d_i`)?

Parallel batching (Brucker et al. 1998; Brucker and Knust): the jobs are processed on a single
machine in batches of at most `b` jobs, one batch after another; all jobs of a batch start and
complete at the same time, and the processing time of a batch is the largest processing time of
its jobs, here `1`. A schedule is given by the start time `σ(t)` of the batch of each job `t`:
the jobs with the same start time form one batch, which occupies `[σ(t), σ(t) + 1)`, so batches
with different integral start times do not overlap, and a batch holds at most `b` jobs. For a
fixed sequence of batches the earliest start times are integral and no later than any other
start times, so integral start times lose no generality. The bounded case `b < n` (`n` jobs) is
part of the instance class.

The instance extends that of SEQUENCING TO MINIMIZE TARDY TASKS with unit lengths and chains
(`TardyTasksUnitChainsWanted`, the case of a single job per time slot, `b = 1`) by the batch
capacity `b`; that module's due dates, precedence relation (the listed pairs `(t, t')` with `t`
preceding `t'`) and well-formedness (positive due dates, `0 < K ≤ n` as in Garey and Johnson's
[SS2], a strict partial order consisting of chains) are reused unchanged, and `WellFormed` adds
`0 < b < n`. Binary encoding of all numbers (the problem is NP-complete in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: an instance of SEQUENCING TO MINIMIZE TARDY TASKS with unit lengths and chains
(due dates, the pairs `(t, t')` with `t` preceding `t'`, the bound `K`) and the batch capacity
`b`. -/
abbrev ChainsUnitParallelBatchingLateJobsInstance := TardyTasksUnitChainsInstance × ℕ

/-- Well-formedness of an instance: it is well-formed for SEQUENCING TO MINIMIZE TARDY TASKS with
unit lengths and chains (positive due dates, `0 < K ≤ n`, a strict partial order consisting of
chains), and `0 < b < n`. -/
def WellFormed (i : ChainsUnitParallelBatchingLateJobsInstance) : Prop :=
  TardyTasksUnitChains.WellFormed i.1 ∧ 0 < i.2 ∧ i.2 < i.1.1.length

/-- Some batch schedule `σ` (batch start time of each job) puts at most `b` jobs in each batch,
obeys the precedence constraints and has at most `K` late jobs, those with `σ(t) + 1 > d(t)`. -/
def ChainsUnitParallelBatchingLateJobsFeasible
    (i : ChainsUnitParallelBatchingLateJobsInstance) : Prop :=
  ∃ σ : Task i.1 → ℕ, (∀ u, (Finset.univ.filter fun t => σ t = u).card ≤ i.2) ∧
    (∀ t t', Prec i.1 t t' → σ t + 1 ≤ σ t') ∧
    (Finset.univ.filter fun t => deadline i.1 t < σ t + 1).card ≤ i.1.2.2

open Classical in
/-- `1|chains;p_i=1;p-batch;b<n|ΣU_i` as a decision problem over bitstrings. -/
noncomputable def chainsUnitParallelBatchingLateJobsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ChainsUnitParallelBatchingLateJobsInstance) x with
  | some i => decide (WellFormed i ∧ ChainsUnitParallelBatchingLateJobsFeasible i)
  | none => false

/-- **PARALLEL BATCHING `1|chains;p_i=1;p-batch;b<n|ΣU_i` is NP-complete.** Source: Brucker and
Knust's classification (reduction from `1|chains;p_i=1|ΣU_i`, Lenstra and Rinnooy Kan 1980). -/
public theorem_wanted chainsUnitParallelBatchingLateJobs_npComplete :
    chainsUnitParallelBatchingLateJobsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L chainsUnitParallelBatchingLateJobsDec

end MetaMathlibExt.Complexity.NPComplete.ChainsUnitParallelBatchingLateJobs
