/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-MACHINE MULTIPURPOSE-MACHINE SCHEDULING WITH CHAINS AND UNIT TIMES is NP-complete

Source:
J. A. Hoogeveen, S. L. van de Velde and B. Veltman, "Complexity of scheduling multiprocessor
tasks with prespecified processor allocations", Discrete Applied Mathematics 55 (1994), 259-272,
doi:10.1016/0166-218X(94)90012-4, Theorem 2.7;
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 10 (multi-purpose
machines), Section 10.1 (`PMPM2|pᵢ = 1; chains|C_max`).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MultiprocessorTaskFlowShopTreeLatenessWanted
public import CSLibExt.Complexity.NPComplete.MultiPurposeJobShopThreeJobsDefs
public import WantedExt.Complexity.NPComplete.UnitFlowShopPrecedenceMakespanWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelTwoMachinesUnitChainsMakespan

open MultiPurposeJobShopThreeJobs
  (MPMJobShopInstance Operation opLength IsMPMJobShopSchedule MPMWellFormed)
open UnitFlowShopPrecedenceMakespan (Prec PrecWellFormed)
open MultiprocessorTaskFlowShopTreeLateness (ImmediatePredecessor)

/-!
# TWO-MACHINE MULTIPURPOSE-MACHINE SCHEDULING WITH CHAINS AND UNIT TIMES is NP-complete

INSTANCE: `m = 2` identical parallel machines; jobs `1, …, n`, each with processing time
`pᵢ = 1` and a nonempty set `μᵢ ⊆ {M₁, M₂}` of eligible machines; precedence constraints that
form a set of chains (every job has at most one immediate predecessor and at most one immediate
successor), where `i` preceding `j` means that `j` cannot start before `i` is completed; and an
integer `K`. QUESTION: is there a schedule, every job on one machine of its set, whose makespan
`maxᵢ Cᵢ` is at most `K`?

Brucker (Section 10.1) states that `PMPM2|pᵢ = 1; chains|C_max` is NP-hard, following from the
proof of Hoogeveen, van de Velde and Veltman for `P2|chain, fixⱼ, pⱼ = 1|C_max` (Theorem 2.7,
NP-hard in the strong sense, by a reduction from 3-PARTITION). That proof uses only single-processor
tasks, each to be executed by a given one of the two processors, and such a task is a job whose
machine set has one machine. Without machine sets, `P2|chains; pᵢ = 1|C_max` is solvable in
polynomial time.

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
arcs). Every job is listed explicitly. The bound `K` is a natural number (a negative `K` gives
only no-instances), and start times below `K` form a certificate of polynomial size. Binary
encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: an MPM job-shop instance (`m`, the jobs as lists of operations `(pᵢ, μᵢ)`, the
bound `K`) and the precedence arcs `(i, k)`. -/
abbrev MultipurposeParallelTwoMachinesUnitChainsMakespanInstance :=
  MPMJobShopInstance × List (ℕ × ℕ)

/-- The precedence relation of the arcs is a set of chains: every job has at most one immediate
successor and at most one immediate predecessor. -/
def IsChains (i : MultipurposeParallelTwoMachinesUnitChainsMakespanInstance) : Prop :=
  (∀ j a b : Fin i.1.2.1.length, ImmediatePredecessor i.2 j a → ImmediatePredecessor i.2 j b →
    a = b) ∧
    ∀ j a b : Fin i.1.2.1.length, ImmediatePredecessor i.2 a j → ImmediatePredecessor i.2 b j →
      a = b

/-- Well-formedness of an instance: a well-formed MPM job-shop instance with `m = 2` machines
(nonempty machine sets in `{1, 2}`) in which every job has exactly one operation, of processing
time `1`, and the arcs name jobs, form an acyclic digraph, and describe a set of chains. -/
def WellFormed (i : MultipurposeParallelTwoMachinesUnitChainsMakespanInstance) : Prop :=
  MPMWellFormed 2 i.1 ∧ (∀ job ∈ i.1.2.1, job.length = 1 ∧ ∀ o ∈ job, o.1 = 1) ∧
    PrecWellFormed i.1.2.1.length i.2 ∧ IsChains i

/-- Some MPM schedule of the jobs obeys the precedence arcs and completes every job by `K`. -/
def MultipurposeParallelTwoMachinesUnitChainsMakespanFeasible
    (i : MultipurposeParallelTwoMachinesUnitChainsMakespanInstance) : Prop :=
  ∃ a σ : Operation i.1 → ℕ, IsMPMJobShopSchedule i.1 a σ ∧
    (∀ t t' : Operation i.1, Prec i.2 t.1 t'.1 → σ t + opLength i.1 t ≤ σ t') ∧
    ∀ t, σ t + opLength i.1 t ≤ i.1.2.2

open Classical in
/-- `PMPM2|chains; pᵢ = 1|C_max` as a decision problem over bitstrings. -/
noncomputable def multipurposeParallelTwoMachinesUnitChainsMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipurposeParallelTwoMachinesUnitChainsMakespanInstance) x with
  | some i => decide (WellFormed i ∧ MultipurposeParallelTwoMachinesUnitChainsMakespanFeasible i)
  | none => false

/-- **`PMPM2|chains; pᵢ = 1|C_max` is NP-complete.**
Source: Hoogeveen, van de Velde and Veltman
(1994), Theorem 2.7, with one-machine sets; Brucker (2007), Section 10.1. -/
public theorem_wanted multipurposeParallelTwoMachinesUnitChainsMakespan_npComplete :
    multipurposeParallelTwoMachinesUnitChainsMakespanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multipurposeParallelTwoMachinesUnitChainsMakespanDec

end MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelTwoMachinesUnitChainsMakespan
