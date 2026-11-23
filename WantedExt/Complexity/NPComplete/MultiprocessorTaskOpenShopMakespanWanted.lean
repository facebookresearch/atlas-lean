/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPT OPEN SHOP (OMPT||C_max) is NP-complete

Source:
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 11 (multiprocessor
tasks: the MPT open-shop model);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS14] OPEN-SHOP SCHEDULING, p. 241
(comment: "NP-complete in the strong sense for m arbitrary [Lenstra, 1977]", a private
communication; the original was not available);
D. P. Williamson, L. A. Hall, J. A. Hoogeveen, C. A. J. Hurkens, J. K. Lenstra,
S. V. Sevast'janov and D. B. Shmoys, "Short shop schedules", Operations Research 45 (1997),
288-294, doi:10.1287/opre.45.2.288;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multiprocessor
tasks", which lists `OMPT||C_max` as minimal NP-hard (strongly), crediting an unpublished
result of J. K. Lenstra.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MultiprocessorTaskOpenShopThreeMachinesWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopMakespan

open MultipurposeFlowShopPrecedenceMakespan (StagesWellFormed)
open MultipurposeFlowShopThreeJobs (MultipurposeFlowShopThreeJobsInstance)
open MultiprocessorTaskOpenShopThreeMachines (MultiprocessorTaskOpenShopThreeMachinesFeasible)

/-!
# MPT OPEN SHOP (OMPT||C_max) is NP-complete

INSTANCE: processors `M_1, …, M_m` (`m ≥ 1` part of the input); an open shop with
multiprocessor tasks (MPT) with `r ≥ 1` stages and processor sets
`μ_1, …, μ_r ⊆ {M_1, …, M_m}`, pairwise different; jobs `1, …, n`, each consisting of `r` tasks
`O_i1, …, O_ir` with processing times `p_ij ∈ ℤ₀⁺`, where `O_ij` requires every processor of
`μ_j` during its processing; and a bound `K`. Tasks requiring a common processor cannot be
processed simultaneously, and no two tasks of the same job can be processed simultaneously; the
tasks of a job may be processed in any order. QUESTION: is there a feasible schedule with
makespan `max_i C_i ≤ K`, where `C_i` is the completion time of job `i` (that of its last task)?

The MPT model is Brucker's (*Scheduling Algorithms*, 5th ed., Chapter 11): in the flow shop
with MPT every job consists of `r` tasks, the processor set depends only on the stage,
`μ_ij = μ_j`, with pairwise different `μ_j`, and the tasks of a job form a chain; "open shop
problems with MPT are defined as flow shop problems with MPT but without precedence constraints
between tasks. However, no pair of tasks of the same job can be processed simultaneously." Here
the number `m` of processors is part of the input. The classical open shop OPEN-SHOP SCHEDULING
([SS14], `OpenShopSchedulingWanted`, `m` arbitrary) is the case `r = m`, `μ_j = {M_j}`; Garey
and Johnson record it as NP-complete in the strong sense for `m` arbitrary (Lenstra), and
Williamson et al. (1997) prove that deciding whether an open shop with integral processing times
has a schedule of length at most 4 is NP-complete. Brucker and Knust list `OMPT||C_max` as a
minimal strongly NP-hard problem of the MPT shop class.

NP membership: a schedule is given by start times, each at most `K` in a yes-instance, so it is
a certificate of polynomial size in the binary input, checked in polynomial time.

Encoding. The instance, its schedules and the question are those of `OMPT3||C_max`
(`MultiprocessorTaskOpenShopThreeMachinesWanted`) without its restriction `m = 3`: the instance
is the number of processors `m`, the stage processor sets (lists of processor indices), one list
of `r` processing times per job (jobs listed one by one), and the bound `K`; the feasibility
predicate `MultiprocessorTaskOpenShopThreeMachinesFeasible` does not depend on `m` (an
MPT open-shop schedule `IsMPTOpenShopSchedule`, task `(i, s)` occupying the half-open interval
`[σ i s, σ i s + p_is)` on every processor of `μ_s`, two different tasks of the same job, or two
different tasks whose processor sets share a processor, occupying disjoint intervals; makespan
by the completion time `completionTime`, the latest completion of a job's tasks). A task with
`p_is = 0` occupies no time, as in the classical open shop. Well-formedness: `m ≥ 1`, the stages
are well formed (`StagesWellFormed`: at least one stage, processor indices below `m`, pairwise
different sets compared as `Finset`s), and every job lists one processing time per stage. A
processor set may be empty, as `μ_j ⊆ {M_1, …, M_m}` allows; tasks of such a stage conflict only
with the other tasks of their job. With integer data, integer start times lose no generality.
Processors are `0, …, m - 1`, stages `Fin r`, jobs `Fin n` for `n` listed jobs. Binary encoding
of all numbers (the problem is NP-hard in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: at least one processor (`m ≥ 1`), well-formed stage
processor sets (`StagesWellFormed`), and one processing time per stage for every job. -/
def WellFormed (i : MultipurposeFlowShopThreeJobsInstance) : Prop :=
  0 < i.1 ∧ StagesWellFormed i.1 i.2.1 ∧ ∀ job ∈ i.2.2.1, job.length = i.2.1.length

open Classical in
/-- `OMPT||C_max` as a decision problem over bitstrings. -/
noncomputable def multiprocessorTaskOpenShopMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipurposeFlowShopThreeJobsInstance) x with
  | some i => decide (WellFormed i ∧ MultiprocessorTaskOpenShopThreeMachinesFeasible i)
  | none => false

/-- **`OMPT||C_max` is NP-complete.** Source: Brucker (2007), Chapter 11; Garey and Johnson
(1979), [SS14] (Lenstra, 1977), and Williamson et al. (1997), via the classical open shop;
Brucker and Knust, *Complexity results for scheduling problems*. -/
public theorem_wanted multiprocessorTaskOpenShopMakespan_npComplete :
    multiprocessorTaskOpenShopMakespanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multiprocessorTaskOpenShopMakespanDec

end MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopMakespan
