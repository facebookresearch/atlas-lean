/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPT FLOW SHOP WITH PRECEDENCE AND UNIT TIMES (FMPT|prec; p_ij = 1|C_max) is NP-complete

Source:
P. Brucker, *Scheduling Algorithms*, 4th ed., Springer (2004), Chapter 11 (shop problems with
multiprocessor tasks: the MPT flow-shop model) and Section 1.3 (precedence relations);
V. G. Timkovsky, "Identical parallel machines vs. unit-time shops and preemptions vs. chains in
scheduling complexity", European Journal of Operational Research 149(2) (2003), 355-376,
doi:10.1016/S0377-2217(02)00767-1;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multiprocessor
tasks", which lists `FMPT|prec; p_ij = 1|C_max` as minimal NP-hard in the strong sense with the
attribution to Timkovsky (2003).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.Interval.Finset.Nat
public import WantedExt.Complexity.NPComplete.MultipurposeFlowShopPrecedenceMakespanWanted
public import WantedExt.Complexity.NPComplete.UnitFlowShopPrecedenceMakespanWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskFlowShopPrecedenceMakespan

open MultipurposeFlowShopPrecedenceMakespan (StagesWellFormed completionTime)
open UnitFlowShopPrecedenceMakespan (Prec PrecWellFormed UnitJobs)

/-!
# MPT FLOW SHOP WITH PRECEDENCE AND UNIT TIMES (FMPT|prec; p_ij = 1|C_max) is NP-complete

INSTANCE: machines `M_1, …, M_m`; a flow shop with multiprocessor tasks (MPT) with `r ≥ 1`
stages and machine sets `μ_1, …, μ_r ⊆ {M_1, …, M_m}`, pairwise different; jobs `1, …, n`, each
consisting of `r` operations `O_i1, …, O_ir` with processing times `p_ij = 1`, where `O_ij`
requires every machine of `μ_j` during its processing and `O_i,j+1` cannot start before `O_ij`
is completed; a precedence relation `→` on the jobs given by an acyclic digraph; and a bound
`K`. Operations requiring a common machine cannot be processed simultaneously. QUESTION: is
there a feasible schedule with makespan `max_i C_i ≤ K`, where `C_i` is the completion time of
job `i` (that of its last operation)?

The MPT model is Brucker's (*Scheduling Algorithms*, 4th ed., Chapter 11). In the general shop
with multiprocessor tasks every task `O_ij` has a processing time `p_ij` and a processor set
`μ_ij ⊆ {M_1, …, M_m}`, all of whose processors it occupies while it is processed, and tasks
needing a common processor cannot run at the same time. The job shop with MPT is the case where
every job is a chain of tasks; the flow shop with MPT is the job-shop case where every job has
the same number `r` of tasks (stages) and the processor set depends only on the stage,
`μ_ij = μ_j`, with pairwise different `μ_j`. Precedence (`prec`, Section 1.3): `i → k` means
that job `i` must be completed before job `k` starts, for an arbitrary acyclic digraph. The
classical flow shop `F|p_ij = 1; prec|C_max` is the case `r = m`, `μ_j = {M_j}`.

Encoding. Machines are `0, …, m - 1`, stages `Fin r`, jobs `Fin n` for `n` listed jobs. Each job
is listed with its processing times `(p_i1, …, p_ir)`, all equal to `1`, so the jobs are given
one by one (`UnitJobs`). The stage machine sets and the well-formedness of the stages
(`StagesWellFormed`: at least one stage, machine indices below `m`, pairwise different sets
compared as `Finset`s) and the completion time `completionTime` (the latest completion of a
job's operations) are those of the MPM flow-shop module
`MultipurposeFlowShopPrecedenceMakespanWanted`; the unit-job condition `UnitJobs`, the arc
relation `Prec` (job `i` precedes job `k` when the arc `(i, k)` is listed) and the acyclicity
condition `PrecWellFormed` (every arc names two jobs and no job precedes itself through a chain
of arcs, `Relation.TransGen`) are those of the classical unit-time flow-shop module
`UnitFlowShopPrecedenceMakespanWanted` (`F|p_ij = 1; prec|C_max`). The precedence digraph may be
any acyclic digraph; arcs implied by transitivity may be listed or omitted, since a job completes
after it starts. Operation `(i, s)`
gets a start time `σ i s` and occupies the half-open interval `[σ i s, σ i s + p_is)` on every
machine of `μ_s`. A machine set may be empty, as `μ_j ⊆ {M_1, …, M_m}` allows; operations of
such a stage conflict with no operation. With integer data, integer start times lose no
generality. Binary encoding of all numbers (the problem is NP-complete in the strong sense).

`IsMPTFlowShopSchedule` takes arbitrary processing times, and `IsMPTPrecedenceSchedule` takes
the instance data as arguments, so that the other MPT flow-shop problems of Brucker and Knust's
class can state their questions with them.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- `σ` (start times) is an MPT flow-shop schedule of `n` jobs with processing times `p i s`
and stage machine sets `μ`: operation `(i, s + 1)` starts no earlier than operation `(i, s)` is
completed, and two different operations whose machine sets share a machine occupy disjoint time
intervals `[σ i s, σ i s + p i s)`. -/
def IsMPTFlowShopSchedule {n : ℕ} (μ : List (List ℕ)) (p σ : Fin n → Fin μ.length → ℕ) :
    Prop :=
  (∀ i (s : Fin μ.length) (hs : s.1 + 1 < μ.length), σ i s + p i s ≤ σ i ⟨s.1 + 1, hs⟩) ∧
    ∀ i s i' s', (i, s) ≠ (i', s') → (∃ k, k ∈ μ.get s ∧ k ∈ μ.get s') →
      Disjoint (Finset.Ico (σ i s) (σ i s + p i s)) (Finset.Ico (σ i' s') (σ i' s' + p i' s'))

/-- `σ` is an MPT flow-shop schedule of `n` unit-time jobs (`p_ij = 1`) with stage machine sets
`μ` that obeys the precedence constraints of the listed arcs: if `i → k`, then no operation of
`k` starts before `C_i`. -/
def IsMPTPrecedenceSchedule {n : ℕ} (μ : List (List ℕ)) (prs : List (ℕ × ℕ))
    (σ : Fin n → Fin μ.length → ℕ) : Prop :=
  IsMPTFlowShopSchedule μ (fun _ _ => 1) σ ∧
    ∀ i k, Prec prs i k → ∀ s, completionTime (fun _ _ => 1) σ i ≤ σ k s

/-- An instance: the number of machines `m`, the stage machine sets `[μ_1, …, μ_r]`, the jobs
(job `i` listed by its processing times `(p_i1, …, p_ir)`), the arcs `(i, k)` with `i → k`, and
the bound `K`. -/
abbrev MultiprocessorTaskFlowShopPrecedenceMakespanInstance :=
  ℕ × List (List ℕ) × List (List ℕ) × List (ℕ × ℕ) × ℕ

/-- Well-formedness of an instance: the machine environment is well formed
(`StagesWellFormed`), every job has `r` unit processing times (`UnitJobs`), and the listed arcs
describe an acyclic precedence digraph on the jobs (`PrecWellFormed`). -/
def WellFormed (i : MultiprocessorTaskFlowShopPrecedenceMakespanInstance) : Prop :=
  StagesWellFormed i.1 i.2.1 ∧ UnitJobs i.2.1.length i.2.2.1 ∧
    PrecWellFormed i.2.2.1.length i.2.2.2.1

/-- Some MPT flow-shop schedule of the unit-time jobs obeys the precedence constraints and has
makespan at most `K`. -/
def MultiprocessorTaskFlowShopPrecedenceMakespanFeasible
    (i : MultiprocessorTaskFlowShopPrecedenceMakespanInstance) : Prop :=
  ∃ σ : Fin i.2.2.1.length → Fin i.2.1.length → ℕ,
    IsMPTPrecedenceSchedule i.2.1 i.2.2.2.1 σ ∧
      ∀ j, completionTime (fun _ _ => 1) σ j ≤ i.2.2.2.2

open Classical in
/-- `FMPT|prec; p_ij = 1|C_max` as a decision problem over bitstrings. -/
noncomputable def multiprocessorTaskFlowShopPrecedenceMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultiprocessorTaskFlowShopPrecedenceMakespanInstance) x with
  | some i => decide (WellFormed i ∧ MultiprocessorTaskFlowShopPrecedenceMakespanFeasible i)
  | none => false

/-- **`FMPT|prec; p_ij = 1|C_max` is NP-complete.** Source: Brucker (2004), Chapter 11;
Timkovsky (2003); Brucker and Knust, *Complexity results for scheduling problems*. -/
public theorem_wanted multiprocessorTaskFlowShopPrecedenceMakespan_npComplete :
    multiprocessorTaskFlowShopPrecedenceMakespanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multiprocessorTaskFlowShopPrecedenceMakespanDec

end MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskFlowShopPrecedenceMakespan
