/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARALLEL BATCHING `1|outtree;p_i=1;p-batch;b<n|L_max` is NP-complete

Source:
P. Brucker, M. R. Garey and D. S. Johnson, "Scheduling equal-length tasks under treelike
precedence constraints to minimize maximum lateness", Mathematics of Operations Research 2
(1977), 275-284, doi:10.1287/moor.2.3.275 (`P|outtree;p_i=1|L_max`);
P. Brucker, A. Gladky, H. Hoogeveen, M. Y. Kovalyov, C. N. Potts, T. Tautenhahn and
S. L. van de Velde, "Scheduling a batching machine", Journal of Scheduling 1 (1998), 31-54,
doi:10.1002/(SICI)1099-1425(199806)1:1<31::AID-JOS4>3.0.CO;2-R (the parallel batching model);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, class "Parallel batching
problems" (`1|outtree;p_i=1;p-batch;b<n|L_max`, minimal NP-hard in the strong sense, by
reduction from the parallel machine problem).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MultiprocessorTaskFlowShopTreeLatenessWanted
public import WantedExt.Complexity.NPComplete.UnitFlowShopOutTreeMaxLatenessWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OutTreeUnitParallelBatchingMaxLateness

open UnitFlowShopPrecedenceMakespan (Prec PrecWellFormed)
open UnitFlowShopOutTreeMaxLateness (toInt)
open MultiprocessorTaskFlowShopTreeLateness (ImmediatePredecessor)

/-!
# PARALLEL BATCHING `1|outtree;p_i=1;p-batch;b<n|L_max` is NP-complete

INSTANCE: `n` jobs, each with unit processing time `p_i = 1` and a due date `d_i ∈ ℤ`, to be
processed in batches on a single machine; a batch capacity `b ∈ ℤ⁺` with `b < n`; a precedence
relation on the jobs that is an out-tree (out-forest: every job has at most one immediate
predecessor), where `i` preceding `j` means that `j` cannot start before `i` is completed; and a
bound `K ∈ ℤ`. QUESTION: is there a feasible schedule whose maximum lateness `max_i (C_i - d_i)`
is at most `K`, where `C_i` is the completion time of job `i`?

Parallel batching (Brucker et al. 1998; Brucker and Knust): the jobs are processed on a single
machine in batches of at most `b` jobs, one batch after another; all jobs of a batch start and
complete at the same time, and the processing time of a batch is the largest processing time of
its jobs, here `1`. A schedule is given by the start time `σ(t)` of the batch of each job `t`: the
jobs with the same start time form one batch, which occupies `[σ(t), σ(t) + 1)`, so batches with
different integral start times do not overlap, and a batch holds at most `b` jobs; `C_t =
σ(t) + 1`. For a fixed sequence of batches the earliest start times are integral and no later
than any other start times, so integral start times lose no generality (the same schedule model
as `ChainsUnitParallelBatchingLateJobsWanted`). The bounded case `b < n` is part of the instance
class.

With unit processing times such a schedule is exactly a schedule of the unit jobs on `b`
identical parallel machines, so the problem is `P|outtree;p_i=1|L_max` with `m = b < n`; Brucker
and Knust list it as minimal NP-hard in the strong sense on that basis ("Parallel machine
problem"). Brucker, Garey and Johnson prove `P|outtree;p_i=1|L_max` NP-complete (their abstract:
for equal-length tasks on `m` identical processors under out-tree precedence constraints,
minimizing the maximum lateness "is NP-complete"); `L_max ≤ K` holds iff every job meets the
deadline `d_i + K`, the form stated in `SchedulingWithIndividualDeadlinesOutTreeWanted`. The
restriction `m < n` keeps the hardness: when `m ≥ n`, starting every job as early as the
precedence constraints allow is feasible and minimizes every completion time at once.

The jobs are `Fin n`, one per listed due date; the precedence relation is given by a list of arcs,
which must name jobs and form an acyclic digraph (`Prec` and `PrecWellFormed` of
`UnitFlowShopPrecedenceMakespanWanted`), job `i` preceding job `k` when `k` is reachable from `i`
along arcs; the out-tree condition uses `ImmediatePredecessor` of
`MultiprocessorTaskFlowShopTreeLatenessWanted` on the same arcs. Due dates and the bound are
integers, each encoded as a pair `(a, b)` standing for `a - b` (`toInt` of
`UnitFlowShopOutTreeMaxLatenessWanted`). Membership in NP: the batch start times are a
certificate; removing a time slot in which no batch runs keeps every constraint and increases no
completion time, so some optimal schedule has all start times below `n`. Binary encoding of all
numbers (the problem is NP-complete in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the batch capacity `b`, the precedence arcs `(i, k)`, the due dates
`d_0, …, d_{n-1}` (jobs `Fin n`), and the bound `K`; due dates and bound as pairs `(a, b)`
standing for `a - b`. -/
abbrev OutTreeUnitParallelBatchingMaxLatenessInstance :=
  ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) × (ℕ × ℕ)

/-- Well-formedness of an instance: `0 < b < n`, the arcs name jobs and form an acyclic digraph,
and every job has at most one immediate predecessor (an out-tree). -/
def WellFormed (i : OutTreeUnitParallelBatchingMaxLatenessInstance) : Prop :=
  0 < i.1 ∧ i.1 < i.2.2.1.length ∧ PrecWellFormed i.2.2.1.length i.2.1 ∧
    ∀ k a b : Fin i.2.2.1.length, ImmediatePredecessor i.2.1 a k →
      ImmediatePredecessor i.2.1 b k → a = b

/-- Some batch schedule `σ` (batch start time of each job) puts at most `b` jobs in each batch,
obeys the precedence arcs, and has maximum lateness at most `K`:
`(σ(t) + 1) - d_t ≤ K` for every job `t`. -/
def OutTreeUnitParallelBatchingMaxLatenessFeasible
    (i : OutTreeUnitParallelBatchingMaxLatenessInstance) : Prop :=
  ∃ σ : Fin i.2.2.1.length → ℕ, (∀ u, (Finset.univ.filter fun t => σ t = u).card ≤ i.1) ∧
    (∀ t t', Prec i.2.1 t t' → σ t + 1 ≤ σ t') ∧
    ∀ t, ((σ t + 1 : ℕ) : ℤ) - toInt (i.2.2.1.get t) ≤ toInt i.2.2.2

open Classical in
/-- `1|outtree;p_i=1;p-batch;b<n|L_max` as a decision problem over bitstrings. -/
noncomputable def outTreeUnitParallelBatchingMaxLatenessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := OutTreeUnitParallelBatchingMaxLatenessInstance) x with
  | some i => decide (WellFormed i ∧ OutTreeUnitParallelBatchingMaxLatenessFeasible i)
  | none => false

/-- **PARALLEL BATCHING `1|outtree;p_i=1;p-batch;b<n|L_max` is NP-complete.** Source: Brucker
and Knust's classification (reduction from `P|outtree;p_i=1|L_max`, Brucker, Garey and Johnson
1977). -/
public theorem_wanted outTreeUnitParallelBatchingMaxLateness_npComplete :
    outTreeUnitParallelBatchingMaxLatenessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L outTreeUnitParallelBatchingMaxLatenessDec

end MetaMathlibExt.Complexity.NPComplete.OutTreeUnitParallelBatchingMaxLateness
