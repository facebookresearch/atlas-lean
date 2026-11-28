/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-MACHINE MULTIPURPOSE-MACHINE SCHEDULING WITH CHAINS is NP-complete

Source:
J. Du, J. Y.-T. Leung and G. H. Young, "Scheduling chain-structured tasks to minimize makespan
and mean flow time", Information and Computation 92 (1991), 219-236,
doi:10.1016/0890-5401(91)90009-Q;
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 10 (multi-purpose
machines) and Table 5.3 (`P2|chains|C_max`, NP-hard in the
strong sense, Du et al.).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MultipurposeParallelTwoMachinesChainsMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelTwoMachinesChainsMakespan

open MultiPurposeJobShopThreeJobs
  (MPMJobShopInstance Operation opLength IsMPMJobShopSchedule MPMWellFormed)
open UnitFlowShopPrecedenceMakespan (Prec PrecWellFormed)
open MultiprocessorTaskFlowShopTreeLateness (ImmediatePredecessor)

/-!
# TWO-MACHINE MULTIPURPOSE-MACHINE SCHEDULING WITH CHAINS is NP-complete

INSTANCE: `m = 2` identical parallel machines; jobs `1, …, n`, each with a processing time
`pᵢ ∈ ℤ⁺` and a nonempty set `μᵢ ⊆ {M₁, M₂}` of eligible machines; precedence constraints that
form a set of chains (every job has at most one immediate predecessor and at most one immediate
successor), where `i` preceding `j` means that `j` cannot start before `i` is completed; and an
integer `K`. QUESTION: is there a nonpreemptive schedule, every job on one machine of its set,
whose makespan `maxᵢ Cᵢ` is at most `K`?

With every `μᵢ = {M₁, M₂}` the problem is `P2|chains|C_max`, which Du, Leung and Young prove NP-hard
in the strong sense (abstract: finding a nonpreemptive schedule of chains with minimum makespan "is
strongly NP-hard for each fixed m > 1"); Brucker's Table 5.3 lists it the same way.

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

Job `j` is an immediate predecessor of `k` when it precedes `k` and no job lies
between them (`ImmediatePredecessor` of
`WantedExt.Complexity.NPComplete.MultiprocessorTaskFlowShopTreeLatenessWanted`, on the same
arcs). The bound `K` is a natural number (a negative `K` gives only no-instances), and start
times below `K` form a certificate of polynomial size. Binary encoding of all numbers (the
problem is NP-complete in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **`PMPM2|chains|C_max` is NP-complete.**
Source: Du, Leung and Young (1991), via the case
`μᵢ = {M₁, M₂}`; Brucker (2007), Table 5.3. -/
public theorem_wanted multipurposeParallelTwoMachinesChainsMakespan_npComplete :
    multipurposeParallelTwoMachinesChainsMakespanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multipurposeParallelTwoMachinesChainsMakespanDec

end MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelTwoMachinesChainsMakespan
