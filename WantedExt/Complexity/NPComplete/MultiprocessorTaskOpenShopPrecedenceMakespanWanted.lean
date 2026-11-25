/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPT OPEN SHOP WITH PRECEDENCE AND UNIT TIMES (OMPT|prec; p_ij = 1|C_max) is NP-complete

Source:
P. Brucker, *Scheduling Algorithms*, 4th ed., Springer (2004), Chapter 11 (shop problems with
multiprocessor tasks: the MPT open-shop model) and Section 1.3 (precedence relations);
V. G. Timkovsky, "Identical parallel machines vs. unit-time shops and preemptions vs. chains in
scheduling complexity", European Journal of Operational Research 149 (2003), 355-376,
doi:10.1016/S0377-2217(02)00767-1;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multiprocessor
tasks", which lists `OMPT|prec; p_ij = 1|C_max` as minimal NP-hard in the strong sense with the
attribution to Timkovsky (2003).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Order.Interval.Finset.Nat
public import WantedExt.Complexity.NPComplete.MultiprocessorTaskFlowShopPrecedenceMakespanWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopPrecedenceMakespan

open MultipurposeFlowShopPrecedenceMakespan (completionTime)
open UnitFlowShopPrecedenceMakespan (Prec)
open MultiprocessorTaskFlowShopPrecedenceMakespan
  (MultiprocessorTaskFlowShopPrecedenceMakespanInstance WellFormed)

/-!
# MPT OPEN SHOP WITH PRECEDENCE AND UNIT TIMES (OMPT|prec; p_ij = 1|C_max) is NP-complete

INSTANCE: machines `M_1, …, M_m`; an open shop with multiprocessor tasks (MPT) with `r ≥ 1`
stages and machine sets `μ_1, …, μ_r ⊆ {M_1, …, M_m}`, pairwise different; jobs `1, …, n`, each
consisting of `r` operations `O_i1, …, O_ir` with processing times `p_ij = 1`, where `O_ij`
requires every machine of `μ_j` during its processing and the operations of a job may be
processed in any order, but no two of them at the same time; a precedence relation `→` on the
jobs given by an acyclic digraph; and a bound `K`. Operations requiring a common machine cannot
be processed simultaneously. QUESTION: is there a feasible schedule with makespan
`max_i C_i ≤ K`, where `C_i` is the completion time of job `i` (that of its last operation)?

The MPT model is Brucker's (*Scheduling Algorithms*, 4th ed., Chapter 11): every task `O_ij` has
a processing time `p_ij` and a processor set `μ_ij`, all of whose processors it occupies while it
is processed, and tasks needing a common processor cannot run at the same time. The flow shop
with MPT (`FMPT`, `MultiprocessorTaskFlowShopPrecedenceMakespanWanted`) gives every job the same
`r` tasks (stages) with stage-dependent processor sets `μ_ij = μ_j`, processed in stage order;
in the open shop with MPT (`OMPT`) the tasks of a job may be processed in an arbitrary order.
Precedence (`prec`, Section 1.3): `i → k` means that job `i` must be completed before job `k`
starts. The classical open shop `O|p_ij = 1; prec|C_max` is the case `r = m`, `μ_j = {M_j}`;
Brucker and Knust list `OMPT|prec; p_ij = 1|C_max` as strongly NP-hard with Timkovsky's
attribution for that classical case (Timkovsky's paper was not available to this formalization).

The instance and its well-formedness are those of the MPT flow shop `FMPT|prec; p_ij = 1|C_max`
(`MultiprocessorTaskFlowShopPrecedenceMakespanWanted`): the number `m` of machines, the stage
machine sets (at least one stage, machine indices below `m`, pairwise different sets compared as
`Finset`s), the jobs, each listed with its processing times `(p_i1, …, p_ir)`, all equal to `1`,
the arcs `(i, k)` of an acyclic precedence digraph (arcs implied by transitivity may be listed or
omitted), and `K`; so are the arc relation `Prec` and the completion time `completionTime` (the
latest completion of a job's operations). Only the schedule differs: operation `(i, s)` gets a
start time `σ i s` and occupies the half-open interval `[σ i s, σ i s + p_is)` on every machine
of `μ_s`, with no stage order (`IsMPTOpenShopSchedule`). A machine set may be empty, as
`μ_j ⊆ {M_1, …, M_m}` allows; operations of such a stage conflict only with the other operations
of their job. With integer data, integer start times lose no generality. Binary encoding of all
numbers (the problem is NP-complete in the strong sense). `IsMPTOpenShopSchedule` takes
arbitrary processing times, and `IsMPTOpenShopPrecedenceSchedule` takes the instance data as
arguments, so that the other MPT open-shop problems of Brucker and Knust's class can state their
questions with them.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- `σ` (start times) is an MPT open-shop schedule of `n` jobs with processing times `p i s`
and stage machine sets `μ`: two different operations of one job occupy disjoint time intervals
`[σ i s, σ i s + p i s)`, and so do two different operations whose machine sets share a
machine. -/
def IsMPTOpenShopSchedule {n : ℕ} (μ : List (List ℕ)) (p σ : Fin n → Fin μ.length → ℕ) :
    Prop :=
  (∀ i s s', s ≠ s' →
      Disjoint (Finset.Ico (σ i s) (σ i s + p i s)) (Finset.Ico (σ i s') (σ i s' + p i s'))) ∧
    ∀ i s i' s', (i, s) ≠ (i', s') → (∃ k, k ∈ μ.get s ∧ k ∈ μ.get s') →
      Disjoint (Finset.Ico (σ i s) (σ i s + p i s)) (Finset.Ico (σ i' s') (σ i' s' + p i' s'))

/-- `σ` is an MPT open-shop schedule of `n` unit-time jobs (`p_ij = 1`) with stage machine sets
`μ` that obeys the precedence constraints of the listed arcs: if `i → k`, then no operation of
`k` starts before `C_i`. -/
def IsMPTOpenShopPrecedenceSchedule {n : ℕ} (μ : List (List ℕ)) (prs : List (ℕ × ℕ))
    (σ : Fin n → Fin μ.length → ℕ) : Prop :=
  IsMPTOpenShopSchedule μ (fun _ _ => 1) σ ∧
    ∀ i k, Prec prs i k → ∀ s, completionTime (fun _ _ => 1) σ i ≤ σ k s

/-- Some MPT open-shop schedule of the unit-time jobs obeys the precedence constraints and has
makespan at most `K`. -/
def MultiprocessorTaskOpenShopPrecedenceMakespanFeasible
    (i : MultiprocessorTaskFlowShopPrecedenceMakespanInstance) : Prop :=
  ∃ σ : Fin i.2.2.1.length → Fin i.2.1.length → ℕ,
    IsMPTOpenShopPrecedenceSchedule i.2.1 i.2.2.2.1 σ ∧
      ∀ j, completionTime (fun _ _ => 1) σ j ≤ i.2.2.2.2

open Classical in
/-- `OMPT|prec; p_ij = 1|C_max` as a decision problem over bitstrings. -/
noncomputable def multiprocessorTaskOpenShopPrecedenceMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultiprocessorTaskFlowShopPrecedenceMakespanInstance) x with
  | some i => decide (WellFormed i ∧ MultiprocessorTaskOpenShopPrecedenceMakespanFeasible i)
  | none => false

/-- **`OMPT|prec; p_ij = 1|C_max` is NP-complete.** Source: Brucker (2004), Chapter 11;
Timkovsky (2003); Brucker and Knust, *Complexity results for scheduling problems*. -/
public theorem_wanted multiprocessorTaskOpenShopPrecedenceMakespan_npComplete :
    multiprocessorTaskOpenShopPrecedenceMakespanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multiprocessorTaskOpenShopPrecedenceMakespanDec

end MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopPrecedenceMakespan
