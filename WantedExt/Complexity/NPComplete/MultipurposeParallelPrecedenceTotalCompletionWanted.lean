/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPURPOSE-MACHINE PARALLEL SCHEDULING WITH PRECEDENCE AND UNIT TIMES TO MINIMIZE TOTAL
COMPLETION TIME is NP-complete

Source:
J. K. Lenstra and A. H. G. Rinnooy Kan, "Complexity of scheduling under precedence constraints",
Operations Research 26 (1978), 22-35, doi:10.1287/opre.26.1.22;
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 10 (multi-purpose
machines) and Table 5.3 (`P|pᵢ = 1; prec|∑Cᵢ`, NP-hard in
the strong sense, Lenstra and Rinnooy Kan).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MultipurposeParallelPrecedenceTotalCompletionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelPrecedenceTotalCompletion

open MultiPurposeJobShopThreeJobs
  (MPMJobShopInstance Operation opLength IsMPMJobShopSchedule MPMWellFormed)
open UnitFlowShopPrecedenceMakespan (Prec PrecWellFormed)

/-!
# MULTIPURPOSE-MACHINE PARALLEL SCHEDULING WITH PRECEDENCE AND UNIT TIMES TO MINIMIZE TOTAL
COMPLETION TIME is NP-complete

INSTANCE: `m` identical parallel machines (`m` part of the input); jobs `1, …, n`, each with
processing time `pᵢ = 1` and a nonempty set `μᵢ` of eligible machines; a precedence relation
given by an acyclic digraph on the jobs, where `i` preceding `j` means that `j` cannot start
before `i` is completed; and an integer `K`. QUESTION: is there a schedule, every job on one
machine of its set, whose total completion time `∑ᵢ Cᵢ` is at most `K`?

With every `μᵢ` equal to all `m` machines the problem is `P|prec; pᵢ = 1|∑Cᵢ`, which Brucker's
Table 5.3 lists as NP-hard in the strong sense, citing Lenstra and Rinnooy Kan; Brucker and Knust
classify `PMPM|prec; pᵢ = 1|∑Cᵢ` the same way.

Brucker's multi-purpose machine model (*Scheduling Algorithms*, Chapter 10): there are machines
`M₁, …, M_m`; every job `i` has a set `μᵢ ⊆ {M₁, …, M_m}` and is processed by exactly one
machine of `μᵢ`, each machine processing at most one job at a time. With single-operation jobs
and identical machines this is `PMPM`, and `P` is the special case of `PMPM` in which every
`μᵢ` contains all `m` machines. An instance is therefore an MPM job-shop instance
(`MPMJobShopInstance` and `MPMWellFormed` of
`CSLibExt.Complexity.NPComplete.MultiPurposeJobShopThreeJobsDefs`: the number `m` of
machines, numbered `1, …, m`, the jobs as lists of operations `(pᵢ, μᵢ)` with nonempty machine
sets, and a bound) in which every job has exactly one operation, together with the list of
precedence arcs, which must name jobs and form an acyclic digraph (`Prec` and `PrecWellFormed`
of `WantedExt.Complexity.NPComplete.UnitFlowShopPrecedenceMakespanWanted`); job `i` precedes
job `k` when `k` is reachable from `i` along arcs. A schedule is an MPM job-shop schedule
(`IsMPMJobShopSchedule`: every job on a machine of `μᵢ` during `[σᵢ, σᵢ + pᵢ)`, and two jobs on
the same machine do not overlap; the order condition between the operations of a job is vacuous
here) in which `σᵢ + pᵢ ≤ σ_k` for every arc `(i, k)`. Integral start times lose no generality,
since the data are integers.

Every job has exactly one operation, so the sum over operations is the sum over jobs.
The bound `K` is a natural number (a negative `K` gives only no-instances), and start times
below `K` form a certificate of polynomial size. Binary encoding of all numbers (the problem is
NP-complete in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **`PMPM|prec; pᵢ = 1|∑Cᵢ` is NP-complete.**
Source: Lenstra and Rinnooy Kan (1978), via the case
`μᵢ = {M₁, …, M_m}`; Brucker (2007), Table 5.3. -/
public theorem_wanted multipurposeParallelPrecedenceTotalCompletion_npComplete :
    multipurposeParallelPrecedenceTotalCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multipurposeParallelPrecedenceTotalCompletionDec

end MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelPrecedenceTotalCompletion
