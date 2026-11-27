/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-MACHINE MULTIPURPOSE-MACHINE SCHEDULING (PMPM2||Cmax) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS8] MULTIPROCESSOR SCHEDULING
(comment: remains NP-complete for `m = 2`);
J. K. Lenstra, A. H. G. Rinnooy Kan and P. Brucker, "Complexity of machine scheduling
problems", Annals of Discrete Mathematics 1 (1977), 343-362,
doi:10.1016/S0167-5060(08)70743-X;
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 10 (multi-purpose
machines);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, class "Multipurpose
machine problems" (`PMPM2||C_max`, minimal NP-hard, credited to Lenstra et al. (1977)).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MultiPurposeJobShopThreeJobsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelTwoMachinesMakespan

open MultiPurposeJobShopThreeJobs
  (MPMJobShopInstance Operation opLength IsMPMJobShopSchedule MPMWellFormed)

/-!
# TWO-MACHINE MULTIPURPOSE-MACHINE SCHEDULING (PMPM2||Cmax) is NP-complete

INSTANCE: `m = 2` identical parallel machines `M₁, M₂`; jobs `1, …, n`, each with a processing
time `pᵢ ∈ ℤ₀⁺` and a nonempty set `μᵢ ⊆ {M₁, M₂}` of eligible machines; and a bound
`K ∈ ℤ₀⁺`. QUESTION: is there a nonpreemptive schedule, every job processed on exactly one
machine of its set and each machine processing at most one job at a time, whose makespan
`maxᵢ Cᵢ` is at most `K`, where `Cᵢ` is the completion time of job `i`?

Brucker's multi-purpose machine model (*Scheduling Algorithms*, Chapter 10): there are machines
`M₁, …, M_m`; every job `i` has a set `μᵢ ⊆ {M₁, …, M_m}` and is processed by exactly one
machine of `μᵢ`. With single-operation jobs and identical machines this is `PMPM`, and `P` is
the special case of `PMPM` in which every `μᵢ` contains all `m` machines. With every
`μᵢ = {M₁, M₂}` the problem is `P2||C_max`, MULTIPROCESSOR SCHEDULING with two processors
([SS8], which "remains NP-complete for `m = 2`"; Lenstra, Rinnooy Kan and Brucker); Brucker and
Knust list `PMPM2||C_max` as minimal NP-hard (in the ordinary sense), citing Lenstra et al.

As in the other `PMPM` modules (e.g. `MultipurposeParallelTwoMachinesChainsMakespanWanted`), an
instance is an MPM job-shop instance (`MPMJobShopInstance` and `MPMWellFormed` of
`CSLibExt.Complexity.NPComplete.MultiPurposeJobShopThreeJobsDefs`: the number `m` of
machines, numbered `1, …, m`, the jobs as lists of operations `(pᵢ, μᵢ)` with nonempty machine
sets, and the bound `K`) in which every job has exactly one operation. A schedule is an MPM
job-shop schedule (`IsMPMJobShopSchedule`: every job on a machine `a i ∈ μᵢ` during
`[σᵢ, σᵢ + pᵢ)`, two jobs of positive length on the same machine do not overlap, and a job of
length `0` occupies no machine time; the order condition between the operations of a job is
vacuous here), and `Cᵢ = σᵢ + pᵢ`. Processing times are nonnegative as in that model; the
positive lengths of [SS8] are a special case. Integral start times lose no generality, since
the data are integers. Membership in NP: the machines, in `{1, 2}`, and the start times, each
at most `K`, are a certificate of polynomial size. Binary encoding of all numbers (for fixed `m`
the problem is solvable in pseudo-polynomial time, so it is NP-complete only in the ordinary
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

/-- Well-formedness of an instance: a well-formed MPM job-shop instance with `m = 2` machines
(nonempty machine sets in `{1, 2}`) in which every job has exactly one operation. -/
def WellFormed (i : MPMJobShopInstance) : Prop :=
  MPMWellFormed 2 i ∧ ∀ job ∈ i.2.1, job.length = 1

/-- Some MPM schedule of the jobs completes every job by `K`. -/
def MultipurposeParallelTwoMachinesMakespanFeasible (i : MPMJobShopInstance) : Prop :=
  ∃ a σ : Operation i → ℕ, IsMPMJobShopSchedule i a σ ∧ ∀ t, σ t + opLength i t ≤ i.2.2

open Classical in
/-- `PMPM2||C_max` as a decision problem over bitstrings. -/
noncomputable def multipurposeParallelTwoMachinesMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := MPMJobShopInstance) x with
  | some i => decide (WellFormed i ∧ MultipurposeParallelTwoMachinesMakespanFeasible i)
  | none => false

/-- **`PMPM2||C_max` is NP-complete.** Source: Garey and Johnson (1979), [SS8] (`m = 2`), and
Lenstra, Rinnooy Kan and Brucker (1977), via the case `μᵢ = {M₁, M₂}`; Brucker (2007),
Chapter 10. -/
public theorem_wanted multipurposeParallelTwoMachinesMakespan_npComplete :
    multipurposeParallelTwoMachinesMakespanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multipurposeParallelTwoMachinesMakespanDec

end MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelTwoMachinesMakespan
