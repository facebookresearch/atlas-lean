/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPURPOSE-MACHINE PARALLEL SCHEDULING WITH OUT-TREE PRECEDENCE AND UNIT TIMES TO MINIMIZE
MAXIMUM LATENESS is NP-complete

Source:
P. Brucker, M. R. Garey and D. S. Johnson, "Scheduling equal-length tasks under treelike
precedence constraints to minimize maximum lateness", Mathematics of Operations Research 2
(1977), 275-284, doi:10.1287/moor.2.3.275;
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 10 (multi-purpose
machines) and Table 5.3 (`P|pᵢ = 1; outtree|L_max`, NP-hard in
the strong sense, Brucker et al.).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MultipurposeParallelOutTreeMaxLatenessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelOutTreeMaxLateness

open MultiPurposeJobShopThreeJobs
  (MPMJobShopInstance Operation opLength IsMPMJobShopSchedule MPMWellFormed)
open UnitFlowShopPrecedenceMakespan (Prec PrecWellFormed)
open MultiprocessorTaskFlowShopTreeLateness (ImmediatePredecessor)

/-!
# MULTIPURPOSE-MACHINE PARALLEL SCHEDULING WITH OUT-TREE PRECEDENCE AND UNIT TIMES TO MINIMIZE
MAXIMUM LATENESS is NP-complete

INSTANCE: `m` identical parallel machines (`m` part of the input); jobs `1, …, n`, each with
processing time `pᵢ = 1`, a nonempty set `μᵢ` of eligible machines and a due date `dᵢ`; a
precedence relation that is an out-forest (every job has at most one immediate predecessor),
where `i` preceding `j` means that `j` cannot start before `i` is completed; and an integer `y`.
QUESTION: is there a schedule, every job on one machine of its set, whose maximum lateness
`L_max = maxᵢ (Cᵢ - dᵢ)` is at most `y`?

With every `μᵢ` equal to all `m` machines the problem is `P|outtree; pᵢ = 1|L_max`, which
Brucker, Garey and Johnson prove NP-complete (abstract: with "out-tree" precedence, minimizing
maximum lateness of equal-length tasks on identical processors "is NP-complete"); Brucker's
Table 5.3 lists it as NP-hard in the strong sense.

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
arcs). Due dates are natural numbers: adding a constant `c` to every due date and subtracting
`c` from `y` changes no lateness comparison `Cᵢ - dᵢ ≤ y`, so integer due dates reduce to
natural ones. The bound `y` is an integer, encoded as a pair `(y⁺, y⁻)` of naturals representing
`y⁺ - y⁻`, and `Cᵢ - dᵢ ≤ y` is stated over `ℕ` as `Cᵢ + y⁻ ≤ dᵢ + y⁺`; the bound slot of the
MPM job-shop instance is unused and must be `0`. There is at least one job, so that `L_max` is
defined. Start times at most `maxᵢ dᵢ + y⁺` form a certificate of polynomial size. Binary
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

/-- **`PMPM|outtree; pᵢ = 1|L_max` is NP-complete.**
Source: Brucker, Garey and Johnson (1977),
via the case `μᵢ = {M₁, …, M_m}`; Brucker (2007), Table 5.3. -/
public theorem_wanted multipurposeParallelOutTreeMaxLateness_npComplete :
    multipurposeParallelOutTreeMaxLatenessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multipurposeParallelOutTreeMaxLatenessDec

end MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelOutTreeMaxLateness
