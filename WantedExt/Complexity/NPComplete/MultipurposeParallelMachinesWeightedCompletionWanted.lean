/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPURPOSE-MACHINE SCHEDULING (PMPM||Σw_iC_i) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS13] SCHEDULING TO MINIMIZE
WEIGHTED COMPLETION TIME, p. 240 (comment: "NP-complete in the strong sense for m arbitrary
[Lageweg and Lenstra, 1977]", a private communication; the original was not available);
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 10 (multi-purpose
machines);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Multipurpose machine problems",
which lists `PMPM||Σw_iC_i` as minimal NP-hard (strongly), crediting an unpublished result of
J. K. Lenstra.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MultipurposeParallelMachinesMakespanWanted
public import WantedExt.Complexity.NPComplete.MultipurposeParallelTwoMachinesWeightedCompletionWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelMachinesWeightedCompletion

open MultipurposeParallelTwoMachinesWeightedCompletion
  (MultipurposeParallelTwoMachinesWeightedCompletionInstance
    MultipurposeParallelTwoMachinesWeightedCompletionFeasible)

/-!
# MULTIPURPOSE-MACHINE SCHEDULING (PMPM||Σw_iC_i) is NP-complete

INSTANCE: identical parallel machines `M₁, …, M_m` (`m ≥ 1` part of the input); jobs
`1, …, n`, each with a processing time `pᵢ ∈ ℤ₀⁺`, a nonempty set `μᵢ ⊆ {M₁, …, M_m}` of
eligible machines and a weight `wᵢ ∈ ℤ₀⁺`; and a bound `K ∈ ℤ₀⁺`. QUESTION: is there a
nonpreemptive schedule, every job processed on exactly one machine of its set and each machine
processing at most one job at a time, whose total weighted completion time `Σᵢ wᵢCᵢ` is at most
`K`, where `Cᵢ` is the completion time of job `i`?

With every `μᵢ = {M₁, …, M_m}` the problem is `P||Σw_iC_i`, SCHEDULING TO MINIMIZE WEIGHTED
COMPLETION TIME ([SS13], `SchedulingToMinimizeWeightedCompletionTimeWanted`), which Garey and
Johnson record as "NP-complete in the strong sense for m arbitrary" (Lageweg and Lenstra).
Brucker and Knust list `PMPM||Σw_iC_i` as minimal NP-hard in the strong sense.

The instance, its schedules and the question are those of `PMPM2||Σw_iC_i`
(`MultipurposeParallelTwoMachinesWeightedCompletionWanted`) with `m` arbitrary, as
`PMPM||C_max` (`MultipurposeParallelMachinesMakespanWanted`) is `PMPM2||C_max` with `m`
arbitrary: an instance is an MPM job-shop instance in which every job is one operation
`(pᵢ, μᵢ)`, its bound component being `K`, together with the weights, one per job, listed in job
order; `WellFormed` is the well-formedness of `PMPM||C_max` (`m ≥ 1`, machine sets nonempty and
in `{1, …, m}`, single-operation jobs) plus one weight per job. The feasibility predicate
`MultipurposeParallelTwoMachinesWeightedCompletionFeasible` does not depend on `m`: an MPM
schedule (`MultiPurposeJobShopThreeJobs.IsMPMJobShopSchedule`, Brucker's multi-purpose machine
model of *Scheduling Algorithms*, Chapter 10) with `Cᵢ = σᵢ + pᵢ` and total weighted completion
time the sum over the operations `t` of `w_j · (σ t + p_t)` for the job `j` of `t`. Processing
times and weights are nonnegative; the positive lengths and weights of [SS13] are a special case.
Integral start times lose no generality, since the data are integers.

Membership in NP: the machines and the start times are a certificate; shifting the jobs on each
machine left to remove idle time keeps the machine assignment and increases no completion time,
so some optimal schedule has every start time at most `Σᵢ pᵢ`, and the certificate has polynomial
size. Binary encoding of all numbers (the problem is NP-hard in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed `PMPM||C_max` instance (`m ≥ 1`, nonempty
machine sets in `{1, …, m}`, single-operation jobs) and one weight per job. -/
def WellFormed (i : MultipurposeParallelTwoMachinesWeightedCompletionInstance) : Prop :=
  MultipurposeParallelMachinesMakespan.WellFormed i.1 ∧ i.2.length = i.1.2.1.length

open Classical in
/-- `PMPM||Σw_iC_i` as a decision problem over bitstrings. -/
noncomputable def multipurposeParallelMachinesWeightedCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipurposeParallelTwoMachinesWeightedCompletionInstance) x with
  | some i =>
    decide (WellFormed i ∧ MultipurposeParallelTwoMachinesWeightedCompletionFeasible i)
  | none => false

/-- **`PMPM||Σw_iC_i` is NP-complete.** Source: Garey and Johnson (1979), [SS13] (Lageweg and
Lenstra, 1977), via the case `μᵢ = {M₁, …, M_m}`; Brucker (2007), Chapter 10; Brucker and Knust,
*Complexity results for scheduling problems*. -/
public theorem_wanted multipurposeParallelMachinesWeightedCompletion_npComplete :
    multipurposeParallelMachinesWeightedCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multipurposeParallelMachinesWeightedCompletionDec

end MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelMachinesWeightedCompletion
