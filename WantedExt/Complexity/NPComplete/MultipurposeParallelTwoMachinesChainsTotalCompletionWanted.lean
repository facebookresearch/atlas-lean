/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-MACHINE MULTIPURPOSE-MACHINE SCHEDULING WITH CHAINS (PMPM2|chains|ΣC_i) is NP-complete

Source:
J. Du, J. Y.-T. Leung and G. H. Young, "Scheduling chain-structured tasks to minimize makespan
and mean flow time", Information and Computation 92 (1991), 219-236,
doi:10.1016/0890-5401(91)90009-Q;
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 10 (multi-purpose
machines);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, class "Multipurpose
machine problems" (`PMPM2|chains|ΣC_i`, minimal NP-hard in the strong sense, credited to Du et
al. (1991)).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MultipurposeParallelPrecedenceTotalCompletionWanted
public import WantedExt.Complexity.NPComplete.MultipurposeParallelTwoMachinesChainsMakespanWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelTwoMachinesChainsTotalCompletion

open MultipurposeParallelTwoMachinesChainsMakespan
  (MultipurposeParallelTwoMachinesChainsMakespanInstance WellFormed)
open MultipurposeParallelPrecedenceTotalCompletion
  (MultipurposeParallelPrecedenceTotalCompletionFeasible)

/-!
# TWO-MACHINE MULTIPURPOSE-MACHINE SCHEDULING WITH CHAINS (PMPM2|chains|ΣC_i) is NP-complete

INSTANCE: `m = 2` identical parallel machines; jobs `1, …, n`, each with a processing time
`pᵢ ∈ ℤ⁺` and a nonempty set `μᵢ ⊆ {M₁, M₂}` of eligible machines; precedence constraints that
form a set of chains (every job has at most one immediate predecessor and at most one immediate
successor), where `i` preceding `j` means that `j` cannot start before `i` is completed; and an
integer `K`. QUESTION: is there a nonpreemptive schedule, every job on one machine of its set,
whose total completion time `Σᵢ Cᵢ` is at most `K`, where `Cᵢ` is the completion time of job
`i`?

With every `μᵢ = {M₁, M₂}` the problem is `P2|chains|ΣC_i`
(`TwoProcessorChainsTotalCompletionTimeWanted`): Du, Leung and Young prove that minimizing the
mean flow time `(Σᵢ Cᵢ) / n` of a set of chains on `m` identical processors is NP-hard in the
strong sense for every fixed `m > 1`. Brucker and Knust list `PMPM2|chains|ΣC_i` as minimal
NP-hard in the strong sense, citing Du et al.

The machines, jobs, machine sets and chains are those of `PMPM2|chains|C_max`
(`MultipurposeParallelTwoMachinesChainsMakespanWanted`, Brucker's multi-purpose machine model of
*Scheduling Algorithms*, Chapter 10): its instance (an MPM job-shop instance with `m = 2` in which
every job is one operation `(pᵢ, μᵢ)`, its bound component being `K`, together with the
precedence arcs, job `i` preceding job `k` when `k` is reachable from `i` along arcs) and its
well-formedness (nonempty machine sets in `{1, 2}`, single-operation jobs of positive processing
time, acyclic arcs naming jobs that form chains) are reused unchanged. The question is that of
`PMPM|prec; pᵢ = 1|ΣCᵢ` (`MultipurposeParallelPrecedenceTotalCompletionWanted`), whose instance
type is the same and whose feasibility predicate reads no unit-time condition (that restriction
lives in its `WellFormed`): some MPM schedule
(`MultiPurposeJobShopThreeJobs.IsMPMJobShopSchedule`) obeys the arcs and has total completion
time `Σ (σ t + pₜ)` at most `K`, with `Cᵢ = σᵢ + pᵢ`. Every job has exactly one operation, so the
sum over operations is the sum over jobs. The bound `K` is a natural number (a negative `K` gives
only no-instances), and start times below `K` form a certificate of polynomial size. Binary
encoding of all numbers (the problem is NP-complete in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

open Classical in
/-- `PMPM2|chains|ΣC_i` as a decision problem over bitstrings. -/
noncomputable def multipurposeParallelTwoMachinesChainsTotalCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipurposeParallelTwoMachinesChainsMakespanInstance) x with
  | some i =>
    decide (WellFormed i ∧ MultipurposeParallelPrecedenceTotalCompletionFeasible i)
  | none => false

/-- **`PMPM2|chains|ΣC_i` is NP-complete.** Source: Du, Leung and Young (1991), via the case
`μᵢ = {M₁, M₂}`; Brucker and Knust's classification; Brucker (2007), Chapter 10. -/
public theorem_wanted multipurposeParallelTwoMachinesChainsTotalCompletion_npComplete :
    multipurposeParallelTwoMachinesChainsTotalCompletionDec ∈
        MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multipurposeParallelTwoMachinesChainsTotalCompletionDec

end MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelTwoMachinesChainsTotalCompletion
