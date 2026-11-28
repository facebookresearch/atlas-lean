/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPURPOSE-MACHINE PARALLEL SCHEDULING WITH PRECEDENCE AND UNIT TIMES is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS9] PRECEDENCE CONSTRAINED
SCHEDULING (the special case in which every machine set contains all machines);
J. D. Ullman, "NP-complete scheduling problems", Journal of Computer and System Sciences 10
(1975), 384-393, doi:10.1016/S0022-0000(75)80008-0;
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 10 (multi-purpose
machines).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MultipurposeParallelPrecedenceMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelPrecedenceMakespan

open MultiPurposeJobShopThreeJobs
  (MPMJobShopInstance Operation opLength IsMPMJobShopSchedule MPMWellFormed)
open UnitFlowShopPrecedenceMakespan (Prec PrecWellFormed)

/-!
# MULTIPURPOSE-MACHINE PARALLEL SCHEDULING WITH PRECEDENCE AND UNIT TIMES is NP-complete

INSTANCE: `m` identical parallel machines (`m` part of the input); jobs `1, …, n`, each with
processing time `pᵢ = 1` and a nonempty set `μᵢ` of eligible machines; a precedence relation
given by an acyclic digraph on the jobs, where `i` preceding `j` means that `j` cannot start
before `i` is completed; and an integer `K`. QUESTION: is there a schedule, every job on one
machine of its set, whose makespan `maxᵢ Cᵢ` is at most `K`?

With every `μᵢ` equal to all `m` machines the problem is `P|prec; pᵢ = 1|C_max`, PRECEDENCE
CONSTRAINED SCHEDULING ([SS9]; its partial order is the digraph of all its pairs), which Ullman
proves NP-complete; Brucker and Knust classify `PMPM|prec; pᵢ = 1|C_max` as NP-hard in the
strong sense, citing Ullman.

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

The bound `K` is a natural number (a negative `K` gives only
no-instances), and start times below `K` form a certificate of polynomial size. Binary encoding
of all numbers (the problem is NP-complete in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **`PMPM|prec; pᵢ = 1|C_max` is NP-complete.**
Source: Garey and Johnson (1979), [SS9], and
Ullman (1975), via the case `μᵢ = {M₁, …, M_m}`. -/
public theorem_wanted multipurposeParallelPrecedenceMakespan_npComplete :
    multipurposeParallelPrecedenceMakespanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multipurposeParallelPrecedenceMakespanDec

end MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelPrecedenceMakespan
