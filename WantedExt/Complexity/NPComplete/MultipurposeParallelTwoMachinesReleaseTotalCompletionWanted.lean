/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-MACHINE MULTIPURPOSE-MACHINE SCHEDULING WITH RELEASE DATES, total completion time
(`PMPM2|rᵢ|ΣCᵢ`) is NP-complete

Source:
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), doi:10.1007/978-3-540-69516-5,
Chapter 10 (multi-purpose machines);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Parallel machine problems with
multi-purpose machines", which lists `PMPM2|r_i|ΣC_i` as minimal NP-hard in the strong sense
("Single-machine problem");
J. K. Lenstra, A. H. G. Rinnooy Kan and P. Brucker, "Complexity of machine scheduling problems",
Annals of Discrete Mathematics 1 (1977), 343-362, doi:10.1016/S0167-5060(08)70743-X (the
single-machine problem `1|r_j|ΣC_j`).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MultipurposeParallelTwoMachinesReleaseTotalCompletionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelTwoMachinesReleaseTotalCompletion

open MultiPurposeJobShopThreeJobs (MPMJobShopInstance Operation opLength MPMWellFormed
  IsMPMJobShopSchedule)

/-!
# TWO-MACHINE MULTIPURPOSE-MACHINE SCHEDULING WITH RELEASE DATES, total completion time

INSTANCE: `m = 2` identical parallel machines; jobs `1, …, n`, each with a processing time
`pᵢ ∈ ℤ₀⁺`, a nonempty set `μᵢ ⊆ {M₁, M₂}` of eligible machines and a release date `rᵢ ∈ ℤ₀⁺`; and
an integer `K`. QUESTION: is there a schedule, every job on one machine of its set and starting no
earlier than its release date, whose total completion time `Σᵢ Cᵢ` is at most `K`, where `Cᵢ` is the
completion time of job `i`?

Brucker's multi-purpose machine model (*Scheduling Algorithms*, Chapter 10): every job `i` has a set
`μᵢ ⊆ {M₁, …, M_m}` and is processed by exactly one machine of `μᵢ`, each machine processing at most
one job at a time; with single-operation jobs and identical machines this is `PMPM`. An instance is
an MPM job-shop instance (`MPMJobShopInstance` and `MPMWellFormed` of
`MultiPurposeJobShopThreeJobsDefs`: the number `m = 2` of machines, numbered `1, 2`, the jobs as
lists of operations `(pᵢ, μᵢ)` with nonempty machine sets, and the bound `K`) in which every job has
exactly one operation, as in `MultipurposeParallelTwoMachinesUnitChainsMakespanWanted`
(`PMPM2|chains; pᵢ = 1|C_max`), together with the list of release dates, one per job. A schedule is
an MPM job-shop schedule (`IsMPMJobShopSchedule`: every job on a machine of `μᵢ` during
`[σᵢ, σᵢ + pᵢ)`, two jobs of positive length on the same machine do not overlap, and a job of length
`0` occupies no machine time) in which every job starts no earlier than its release date;
`Cᵢ = σᵢ + pᵢ`. Every job has exactly one operation, so the operations are the jobs. Integral start
times lose no generality, since the data are integers.

The single-machine problem `1|r_i|ΣC_i`, strongly NP-hard by Lenstra, Rinnooy Kan and Brucker
(1977), is the special case in which every `μᵢ` is `{M₁}`; Brucker and Knust list `PMPM2|r_i|ΣC_i`
as minimal NP-hard in the strong sense on that basis ("Single-machine problem"). Binary encoding of
all numbers. Membership in NP: the machines and start times are a certificate; every start time is
at most `Cᵢ ≤ Σᵢ Cᵢ ≤ K`, so the certificate has polynomial size.

Encoding: the instance is decoded from a bitstring with the repository's canonical
`MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and bitstrings decoding to malformed
instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in `MetaMathlibExt.ComplexityTheory.NP`, plus a
polynomial-time many-one reduction from every language in `NP` (`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MPM PARALLEL MACHINES `PMPM2|rᵢ|ΣCᵢ` is NP-complete.** Source: Brucker and Knust's
classification ("Single-machine problem": Lenstra, Rinnooy Kan and Brucker (1977), `1|r_i|ΣC_i`);
Brucker (2007), Chapter 10 (model). -/
public theorem_wanted multipurposeParallelTwoMachinesReleaseTotalCompletion_npComplete :
    multipurposeParallelTwoMachinesReleaseTotalCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multipurposeParallelTwoMachinesReleaseTotalCompletionDec

end MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelTwoMachinesReleaseTotalCompletion
