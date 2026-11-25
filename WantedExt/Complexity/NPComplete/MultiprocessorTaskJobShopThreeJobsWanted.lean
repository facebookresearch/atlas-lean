/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPROCESSOR-TASK JOB SHOP JMPT3|n=3|Cmax is NP-complete

Source:
P. Brucker, *Scheduling Algorithms*, 4th ed., Springer (2004), Chapter 11 (shop problems with
multiprocessor tasks: the MPT job-shop model);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multiprocessor
tasks", entry `JMPT3|n=3|C_max` (minimal NP-hard in the ordinary sense, citing Sotskov and
Shakhlevich 1995);
Yu. N. Sotskov and N. V. Shakhlevich, "NP-hardness of shop-scheduling problems with three
jobs", Discrete Applied Mathematics 59 (1995), 237-266, doi:10.1016/0166-218X(95)80004-N
(`J3|n=3|C_max` is NP-hard).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MultiPurposeJobShopThreeJobsWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskJobShopThreeJobs

open MetaMathlibExt.Complexity.NPComplete.MultiPurposeJobShopThreeJobs
  (MPMJobShopInstance Operation opLength eligible MPMWellFormed)

/-!
# MULTIPROCESSOR-TASK JOB SHOP JMPT3|n=3|Cmax is NP-complete

INSTANCE: machines `M_1, M_2, M_3`; exactly three jobs, job `j` a chain of tasks
`O_j1, …, O_jn_j`, where task `O_jk` has a processing time `p_jk ∈ ℕ` and a nonempty set
`μ_jk ⊆ {M_1, M_2, M_3}` of machines, all of which it occupies simultaneously during its
processing, and `O_j,k+1` cannot start before `O_jk` is completed; tasks whose machine sets
intersect cannot be processed at the same time; and a bound `K`. QUESTION: is there a feasible
schedule with makespan `max_j C_j ≤ K`, where `C_j` is the completion time of job `j` (that of its
last task)?

The MPT model is Brucker's (Chapter 11): in the general shop with multiprocessor tasks every task
`O_jk` has a processing time and a processor set `μ_jk`, all of whose processors it occupies, and
tasks needing a common processor cannot run at the same time; the job shop with multiprocessor
tasks is the case where every job is a chain of tasks. Brucker and Knust list `JMPT3|n=3|C_max`
as minimal NP-hard in the ordinary sense, citing Sotskov and Shakhlevich, who prove
`J3|n=3|C_max` NP-hard: a classical job-shop task on machine `M` is the multiprocessor task with
`μ_jk = {M}`.

The instance data are those of the multipurpose-machine job shop of
`MultiPurposeJobShopThreeJobsWanted` (`MultiPurposeJobShopThreeJobs.MPMJobShopInstance`: the
machine count, the jobs as lists of tasks `(p_jk, μ_jk)` with machines numbered `1, …, m`, and the
bound), with its operations `Operation`, processing times `opLength` and machine lists `eligible`,
here read as the sets `μ_jk` of machines a task occupies; `MPMWellFormed 3` gives `m = 3`, jobs
with at least one task, and nonempty machine sets within `{1, 2, 3}`. A schedule gives every task
a start time `σ`; two different tasks of positive length whose machine sets share a machine do not
overlap (a task of length `0` occupies no machine time, as in the MPM module), and each task of a
job starts no earlier than the previous one completes (`IsMPTJobShopSchedule`). Lengths and the
bound use the canonical binary encoding; the problem is NP-hard in the ordinary sense.
Membership in NP: some optimal schedule has start times that are sums of processing times, a
certificate of polynomial size.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- `σ` is an MPT job shop schedule: task `t` occupies every machine of `μ_t` during
`[σ t, σ t + p_t)`; two different tasks of positive length whose machine sets share a machine do
not overlap; and every task of a job starts no earlier than the previous task of the job
completes. -/
def IsMPTJobShopSchedule (i : MPMJobShopInstance) (σ : Operation i → ℕ) : Prop :=
  (∀ t t', t ≠ t' → (∃ M ∈ eligible i t, M ∈ eligible i t') → 0 < opLength i t →
      0 < opLength i t' → σ t + opLength i t ≤ σ t' ∨ σ t' + opLength i t' ≤ σ t) ∧
    ∀ j (k k' : Fin (i.2.1.get j).length), k'.1 = k.1 + 1 →
      σ ⟨j, k⟩ + opLength i ⟨j, k⟩ ≤ σ ⟨j, k'⟩

/-- Well-formedness of an instance: a well-formed instance with `m = 3` machines (jobs with at
least one task, nonempty machine sets within `{1, 2, 3}`) and exactly three jobs. -/
def WellFormed (i : MPMJobShopInstance) : Prop :=
  MPMWellFormed 3 i ∧ i.2.1.length = 3

/-- Some MPT job shop schedule has makespan at most `K`: the last task of every job, which
completes after the job's other tasks, completes by `K`. -/
def MultiprocessorTaskJobShopThreeJobsFeasible (i : MPMJobShopInstance) : Prop :=
  ∃ σ : Operation i → ℕ, IsMPTJobShopSchedule i σ ∧
    ∀ j (k : Fin (i.2.1.get j).length), k.1 + 1 = (i.2.1.get j).length →
      σ ⟨j, k⟩ + opLength i ⟨j, k⟩ ≤ i.2.2

open Classical in
/-- MULTIPROCESSOR-TASK JOB SHOP JMPT3|n=3|Cmax as a decision problem over bitstrings. -/
noncomputable def multiprocessorTaskJobShopThreeJobsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MPMJobShopInstance) x with
  | some i => decide (WellFormed i ∧ MultiprocessorTaskJobShopThreeJobsFeasible i)
  | none => false

/-- **MULTIPROCESSOR-TASK JOB SHOP JMPT3|n=3|Cmax is NP-complete.** Source: Brucker and Knust's
classification, citing Sotskov and Shakhlevich (1995); Brucker (2004), Chapter 11 (the model). -/
public theorem_wanted multiprocessorTaskJobShopThreeJobs_npComplete :
    multiprocessorTaskJobShopThreeJobsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multiprocessorTaskJobShopThreeJobsDec

end MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskJobShopThreeJobs
