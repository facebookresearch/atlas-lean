/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPT OPEN SHOP WITH THREE PROCESSORS (OMPT3||C_max) is NP-complete

Source:
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 11 (multiprocessor
tasks: the MPT open-shop model);
T. Gonzalez and S. Sahni, "Open shop scheduling to minimize finish time", Journal of the ACM
23(4) (1976), 665-679, doi:10.1145/321978.321985;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multiprocessor
tasks", which lists `OMPT3||C_max` as minimal NP-hard (in the ordinary sense) with the
attribution to Gonzalez and Sahni (1976).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MultipurposeFlowShopThreeJobsWanted
public import WantedExt.Complexity.NPComplete.MultiprocessorTaskOpenShopPrecedenceMakespanWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopThreeMachines

open MultipurposeFlowShopPrecedenceMakespan (StagesWellFormed completionTime)
open MultipurposeFlowShopThreeJobs (MultipurposeFlowShopThreeJobsInstance Job Stage
  processingTime)
open MultiprocessorTaskOpenShopPrecedenceMakespan (IsMPTOpenShopSchedule)

/-!
# MPT OPEN SHOP WITH THREE PROCESSORS (OMPT3||C_max) is NP-complete

INSTANCE: three processors `M_1, M_2, M_3`; an open shop with multiprocessor tasks (MPT) with
`r ≥ 1` stages and processor sets `μ_1, …, μ_r ⊆ {M_1, M_2, M_3}`, pairwise different; jobs
`1, …, n`, each consisting of `r` tasks `O_i1, …, O_ir` with processing times `p_ij ∈ ℤ₀⁺`,
where `O_ij` requires every processor of `μ_j` during its processing; and a bound `K`. Tasks
requiring a common processor cannot be processed simultaneously, and no two tasks of the same
job can be processed simultaneously; the tasks of a job may be processed in any order.
QUESTION: is there a feasible schedule with makespan `max_i C_i ≤ K`, where `C_i` is the
completion time of job `i` (that of its last task)?

The MPT model is Brucker's (*Scheduling Algorithms*, 5th ed., Chapter 11): in the flow shop
with MPT every job consists of `r` tasks, the processor set depends only on the stage,
`μ_ij = μ_j`, with pairwise different `μ_j`, and the tasks of a job form a chain; "open shop
problems with MPT are defined as flow shop problems with MPT but without precedence constraints
between tasks. However, no pair of tasks of the same job can be processed simultaneously." In
`OMPT3`, the number of processors is fixed to `3`. The classical three-processor open shop
`O3||C_max` of Gonzalez and Sahni is the case `r = 3`, `μ_j = {M_j}`, so `OMPT3||C_max` is
NP-hard; Brucker and Knust record it as a minimal NP-hard problem of the MPT shop class.
NP membership: a schedule is given by start times, each at most `K` in a yes-instance, so it is
a certificate of polynomial size in the binary input, checked in polynomial time.

Encoding. The MPT open-shop schedule `IsMPTOpenShopSchedule` (task `(i, s)` gets a start time
`σ i s` and occupies the half-open interval `[σ i s, σ i s + p_is)` on every processor of `μ_s`;
two different tasks of the same job, or two different tasks whose processor sets share a
processor, occupy disjoint intervals) is that of `OMPT|prec; p_ij = 1|C_max`
(`MultiprocessorTaskOpenShopPrecedenceMakespanWanted`), which takes arbitrary processing times; a
task with `p_is = 0` occupies no time, as in the classical open shop. The instance shape and its
accessors (`Job`, `Stage`, `processingTime`) are those of `FMPM|n = 3|C_max`
(`MultipurposeFlowShopThreeJobsWanted`): the number of processors `m`, the stage processor sets,
one list of `r` processing times per job (jobs listed one by one), and the bound `K`; here
`m = 3` and the number of jobs is arbitrary. Processors are `0, 1, 2`, stages `Fin r`, jobs
`Fin n` for `n` listed jobs. The well-formedness of the stages (`StagesWellFormed`: at least one
stage, processor indices below `m`, pairwise different sets compared as `Finset`s) and the
completion time `completionTime` (the latest completion of a job's tasks) are those of the MPM
flow-shop module `MultipurposeFlowShopPrecedenceMakespanWanted`. A processor set may be empty,
as `μ_j ⊆ {M_1, M_2, M_3}` allows; tasks of such a stage conflict only with the other tasks of
their job. With integer data, integer start times lose no generality. Binary encoding of all
numbers (the problem is NP-hard in the ordinary sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: there are three processors (`m = 3`), the stage processor
sets are well formed (`StagesWellFormed`), and every job lists one processing time per stage. -/
def WellFormed (i : MultipurposeFlowShopThreeJobsInstance) : Prop :=
  i.1 = 3 ∧ StagesWellFormed i.1 i.2.1 ∧ ∀ job ∈ i.2.2.1, job.length = i.2.1.length

/-- Some MPT open-shop schedule of the jobs has makespan at most `K`. -/
def MultiprocessorTaskOpenShopThreeMachinesFeasible
    (i : MultipurposeFlowShopThreeJobsInstance) : Prop :=
  ∃ σ : Job i → Stage i → ℕ, IsMPTOpenShopSchedule i.2.1 (processingTime i) σ ∧
    ∀ j, completionTime (processingTime i) σ j ≤ i.2.2.2

open Classical in
/-- `OMPT3||C_max` as a decision problem over bitstrings. -/
noncomputable def multiprocessorTaskOpenShopThreeMachinesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipurposeFlowShopThreeJobsInstance) x with
  | some i => decide (WellFormed i ∧ MultiprocessorTaskOpenShopThreeMachinesFeasible i)
  | none => false

/-- **`OMPT3||C_max` is NP-complete.** Source: Brucker (2007), Chapter 11; Gonzalez and Sahni
(1976); Brucker and Knust, *Complexity results for scheduling problems*. -/
public theorem_wanted multiprocessorTaskOpenShopThreeMachines_npComplete :
    multiprocessorTaskOpenShopThreeMachinesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multiprocessorTaskOpenShopThreeMachinesDec

end MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopThreeMachines
