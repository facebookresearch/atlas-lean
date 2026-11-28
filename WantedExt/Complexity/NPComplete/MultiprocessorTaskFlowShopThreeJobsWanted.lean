/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPT FLOW SHOP WITH THREE JOBS (FMPT|n = 3|C_max) is NP-complete

Source:
A. Krämer, *Scheduling Multiprocessor Tasks on Dedicated Processors*, PhD thesis, Universität
Osnabrück, Fachbereich Mathematik/Informatik (1995);
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), doi:10.1007/978-3-540-69516-5,
Chapter 11 (the MPT flow-shop model);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multiprocessor
tasks", which lists `FMPT|n = 3|C_max` as minimal NP-hard (in the ordinary sense), citing Krämer
(1995).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MultiprocessorTaskFlowShopThreeJobsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskFlowShopThreeJobs

open MultipurposeFlowShopThreeJobs
  (MultipurposeFlowShopThreeJobsInstance Job Stage processingTime)
open MultipurposeFlowShopPrecedenceMakespan (completionTime)
open MultiprocessorTaskFlowShopPrecedenceMakespan (IsMPTFlowShopSchedule)

/-!
# MPT FLOW SHOP WITH THREE JOBS (FMPT|n = 3|C_max) is NP-complete

INSTANCE: machines `M_1, …, M_m`; an MPT flow shop with `r ≥ 1` stages and nonempty machine sets
`μ_1, …, μ_r ⊆ {M_1, …, M_m}`, pairwise different; exactly three jobs `J_1, J_2, J_3`, each
consisting of `r` operations `O_i1, …, O_ir` with processing times `p_ij ∈ ℤ₀⁺`, where `O_ij`
needs all machines of `μ_j` simultaneously and `O_i,j+1` cannot start before `O_ij` is completed;
and a bound `K`. Each machine processes at most one operation at a time. QUESTION: is there a
feasible schedule with makespan `max_i C_i ≤ K`, where `C_i` is the completion time of job `i`
(that of its last operation)?

The MPT flow shop is Brucker's (*Scheduling Algorithms*, Chapter 11): each job has exactly `r`
operations, the `j`-th operation of every job requires all machines of the same set `μ_j`, the
machine sets are different, and the operations of a job are processed in the order of the stages.
The instance, its base well-formedness and the processing times are those of the MPM flow shop
with three jobs `FMPM|n = 3|C_max` (`MultipurposeFlowShopThreeJobsWanted`:
`MultipurposeFlowShopThreeJobs.MultipurposeFlowShopThreeJobsInstance`, the number `m` of machines,
the stage machine sets `[μ_1, …, μ_r]` as lists of machine indices, one list `[p_i1, …, p_ir]` of
processing times per job, and `K`; `MultipurposeFlowShopThreeJobs.WellFormed`, at least one stage,
machine indices below `m`, pairwise different sets, exactly three jobs, one processing time per
stage; `MultipurposeFlowShopThreeJobs.processingTime`); `WellFormed` adds that every machine set
is nonempty, as for the tasks of `MultiprocessorTaskJobShopThreeJobsWanted` (a multiprocessor task
occupies at least one processor). The number of machines `m` and the number of stages `r` are part
of the instance. The schedule predicate is the MPT flow-shop schedule
`MultiprocessorTaskFlowShopPrecedenceMakespan.IsMPTFlowShopSchedule`: start times `σ j s`,
operation `(j, s + 1)` starting no earlier than operation `(j, s)` is completed, and two different
operations whose machine sets share a machine occupying disjoint intervals
`[σ j s, σ j s + p_js)`; `C_j` is `MultipurposeFlowShopPrecedenceMakespan.completionTime`, the
latest completion time of a job's operations. With integer data, integer start times lose no
generality. Brucker and Knust list the problem as minimal NP-hard in the ordinary sense,
crediting Krämer (1995), whose full text was not available. Binary encoding of all numbers.
Membership in NP: the start times are a certificate; removing a time slot in which no operation
runs keeps every constraint and increases no completion time, so a schedule meeting `K` can be
taken with all start times below `K`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MPT FLOW SHOP WITH THREE JOBS (`FMPT|n = 3|C_max`) is NP-complete.** Source: Krämer (1995),
as recorded in the Brucker-Knust classification; Brucker (2007), Chapter 11 (model). -/
public theorem_wanted multiprocessorTaskFlowShopThreeJobs_npComplete :
    multiprocessorTaskFlowShopThreeJobsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multiprocessorTaskFlowShopThreeJobsDec

end MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskFlowShopThreeJobs
