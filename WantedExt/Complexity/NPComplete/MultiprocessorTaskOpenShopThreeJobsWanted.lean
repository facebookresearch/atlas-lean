/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


/-
# MULTIPROCESSOR-TASK OPEN SHOP OMPT|n=3|Cmax is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SS14] OPEN-SHOP SCHEDULING, comment: remains
NP-complete if `m = 3`; T. Gonzalez and S. Sahni, "Open shop scheduling to minimize finish time",
Journal of the ACM 23 (1976), 665-679, doi:10.1145/321978.321985; P. Brucker, *Scheduling
Algorithms*, 4th ed., Springer (2004), Chapter 11 (shop problems with multiprocessor tasks); P.
Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multiprocessor
tasks", entry `OMPT|n=3|C_max` (minimal NP-hard in the ordinary sense, citing Gonzalez and Sahni
1976).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MultiPurposeJobShopThreeJobsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopThreeJobs

open MetaMathlibExt.Complexity.NPComplete.MultiPurposeJobShopThreeJobs
  (MPMJobShopInstance Operation opLength eligible MPMWellFormed)

/-!
# MULTIPROCESSOR-TASK OPEN SHOP OMPT|n=3|Cmax is NP-complete

INSTANCE: machines `M_1, …, M_m` (`m` part of the input); exactly three jobs, job `j` consisting of
tasks `O_j1, …, O_jn_j`, where task `O_jk` has a processing time `p_jk ∈ ℕ` and a nonempty set
`μ_jk ⊆ {M_1, …, M_m}` of machines, all of which it occupies simultaneously during its processing;
the tasks of a job are processed in any order but no two of them at the same time; tasks whose
machine sets intersect cannot be processed at the same time; and a bound `K`. QUESTION: is there a
feasible schedule with makespan `max_j C_j ≤ K`, where `C_j` is the completion time of job `j` (that
of its last task)?

The MPT model is Brucker's (Chapter 11): every task `O_jk` has a processing time and a processor set
`μ_jk`, all of whose processors it occupies, and tasks needing a common processor cannot run at the
same time; in the open shop with multiprocessor tasks the tasks of a job have no prescribed order,
but, as in every open shop, two tasks of one job are not processed at the same time. The instance
data are those of the multiprocessor-task job shop `JMPT3|n=3|C_max`
(`MultiprocessorTaskJobShopThreeJobsWanted`), i.e. of the multipurpose-machine job shop of
`MultiPurposeJobShopThreeJobsDefs` (`MultiPurposeJobShopThreeJobs.MPMJobShopInstance`: the machine
count `m`, the jobs as lists of tasks `(p_jk, μ_jk)` with machines numbered `1, …, m`, and the
bound), with its tasks `Operation`, processing times `opLength` and machine lists `eligible`, read
as the sets `μ_jk` a task occupies; `MPMWellFormed m` with the instance's own machine count gives
jobs with at least one task and nonempty machine sets within `{1, …, m}`, and well-formedness adds
exactly three jobs. A schedule gives every task a start time `σ`; two different tasks of positive
length that share a machine, or that belong to the same job, do not overlap (a task of length `0`
occupies no machine time, as in the job-shop modules) (`IsMPTOpenShopSchedule`).

The classical open shop with three jobs, `O|n=3|C_max`, is the special case in which every job has
one task on each machine with `μ_jk = {M_k}`; exchanging the roles of jobs and machines maps it to
`O3||C_max`, which Gonzalez and Sahni prove NP-hard (Garey and Johnson [SS14]: NP-complete for
`m = 3`), and Brucker and Knust list `OMPT|n=3|C_max` as minimal NP-hard in the ordinary sense on
that basis. Processing times and the bound use the binary encoding. Membership in NP: some optimal
schedule has start times that are sums of processing times, a certificate of polynomial size.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- `σ` is an MPT open-shop schedule: task `t` occupies every machine of `μ_t` during
`[σ t, σ t + p_t)`; two different tasks of positive length that share a machine, or that belong to
the same job, do not overlap. -/
def IsMPTOpenShopSchedule (i : MPMJobShopInstance) (σ : Operation i → ℕ) : Prop :=
  ∀ t t', t ≠ t' → ((∃ M ∈ eligible i t, M ∈ eligible i t') ∨ t.1 = t'.1) →
    0 < opLength i t → 0 < opLength i t' →
      σ t + opLength i t ≤ σ t' ∨ σ t' + opLength i t' ≤ σ t

/-- Well-formedness of an instance: a well-formed instance with its own machine count `m` (jobs with
at least one task, nonempty machine sets within `{1, …, m}`) and exactly three jobs. -/
def WellFormed (i : MPMJobShopInstance) : Prop :=
  MPMWellFormed i.1 i ∧ i.2.1.length = 3

/-- Some MPT open-shop schedule completes every task by `K`. -/
def MultiprocessorTaskOpenShopThreeJobsFeasible (i : MPMJobShopInstance) : Prop :=
  ∃ σ : Operation i → ℕ, IsMPTOpenShopSchedule i σ ∧ ∀ t, σ t + opLength i t ≤ i.2.2

open Classical in
/-- MULTIPROCESSOR-TASK OPEN SHOP OMPT|n=3|Cmax as a decision problem over bitstrings. -/
noncomputable def multiprocessorTaskOpenShopThreeJobsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := MPMJobShopInstance) x with
  | some i => decide (WellFormed i ∧ MultiprocessorTaskOpenShopThreeJobsFeasible i)
  | none => false

/-- **MULTIPROCESSOR-TASK OPEN SHOP OMPT|n=3|Cmax is NP-complete.** Source: Garey and Johnson
(1979), [SS14]; Gonzalez and Sahni (1976); Brucker and Knust's classification; Brucker (2004),
Chapter 11 (model). -/
public theorem_wanted multiprocessorTaskOpenShopThreeJobs_npComplete :
    multiprocessorTaskOpenShopThreeJobsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multiprocessorTaskOpenShopThreeJobsDec

end MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopThreeJobs
