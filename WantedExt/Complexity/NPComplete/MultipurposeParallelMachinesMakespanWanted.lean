/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPURPOSE-MACHINE SCHEDULING (PMPM||Cmax) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS8] MULTIPROCESSOR SCHEDULING
(comment: "NP-complete in the strong sense for `m` arbitrary (3-PARTITION is a special case)");
M. R. Garey and D. S. Johnson, ""Strong" NP-completeness results: motivation, examples, and
implications", Journal of the ACM 25 (1978), 499-508, doi:10.1145/322077.322090;
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 10 (multi-purpose
machines);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, class "Multipurpose
machine problems" (`PMPM||C_max`, minimal NP-hard in the strong sense, credited to Garey and
Johnson (1978)).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MultipurposeParallelTwoMachinesMakespanWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelMachinesMakespan

open MultiPurposeJobShopThreeJobs (MPMJobShopInstance MPMWellFormed)
open MultipurposeParallelTwoMachinesMakespan (MultipurposeParallelTwoMachinesMakespanFeasible)

/-!
# MULTIPURPOSE-MACHINE SCHEDULING (PMPM||Cmax) is NP-complete

INSTANCE: identical parallel machines `M₁, …, M_m` (`m ≥ 1` part of the input); jobs
`1, …, n`, each with a processing time `pᵢ ∈ ℤ₀⁺` and a nonempty set `μᵢ ⊆ {M₁, …, M_m}` of
eligible machines; and a bound `K ∈ ℤ₀⁺`. QUESTION: is there a nonpreemptive schedule, every
job processed on exactly one machine of its set and each machine processing at most one job at
a time, whose makespan `maxᵢ Cᵢ` is at most `K`, where `Cᵢ` is the completion time of job `i`?

This is `PMPM||C_max` in Brucker's multi-purpose machine model (*Scheduling Algorithms*,
Chapter 10). With every `μᵢ = {M₁, …, M_m}` the problem is `P||C_max`, MULTIPROCESSOR
SCHEDULING ([SS8], NP-complete in the strong sense for arbitrary `m`, Garey and Johnson 1978);
Brucker and Knust list `PMPM||C_max` as minimal NP-hard in the strong sense, citing Garey and
Johnson (1978).

The instances and schedules are those of `MultipurposeParallelTwoMachinesMakespanWanted`
(`PMPM2||C_max`) with the number `m` of machines taken from the instance instead of fixed to
`2`: an MPM job-shop instance (`MPMJobShopInstance` and `MPMWellFormed` of
`WantedExt.Complexity.NPComplete.MultiPurposeJobShopThreeJobsWanted`: `m`, the jobs as lists of
operations `(pᵢ, μᵢ)` with nonempty machine sets in `{1, …, m}`, and the bound `K`) in which
every job has exactly one operation, and the feasibility predicate
`MultipurposeParallelTwoMachinesMakespanFeasible` (an MPM schedule, every job on a machine of
`μᵢ` during `[σᵢ, σᵢ + pᵢ)`, two jobs of positive length on one machine not overlapping, with
every `σᵢ + pᵢ ≤ K`), which does not depend on `m`. Membership in NP: the machines, each an
entry of a listed set `μᵢ`, and the start times, each at most `K`, are a certificate of
polynomial size. Binary encoding of all numbers (the problem is NP-complete in the strong
sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed MPM job-shop instance whose number `m` of
machines is positive (nonempty machine sets in `{1, …, m}`) and in which every job has exactly
one operation. -/
def WellFormed (i : MPMJobShopInstance) : Prop :=
  MPMWellFormed i.1 i ∧ 0 < i.1 ∧ ∀ job ∈ i.2.1, job.length = 1

open Classical in
/-- `PMPM||C_max` as a decision problem over bitstrings. -/
noncomputable def multipurposeParallelMachinesMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := MPMJobShopInstance) x with
  | some i => decide (WellFormed i ∧ MultipurposeParallelTwoMachinesMakespanFeasible i)
  | none => false

/-- **`PMPM||C_max` is NP-complete.** Source: Garey and Johnson (1979), [SS8], and Garey and
Johnson (1978), via the case `μᵢ = {M₁, …, M_m}`; Brucker (2007), Chapter 10; Brucker and
Knust, class "Multipurpose machine problems". -/
public theorem_wanted multipurposeParallelMachinesMakespan_npComplete :
    multipurposeParallelMachinesMakespanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multipurposeParallelMachinesMakespanDec

end MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelMachinesMakespan
