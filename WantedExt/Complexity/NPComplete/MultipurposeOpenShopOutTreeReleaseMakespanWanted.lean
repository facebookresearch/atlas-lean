/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPM OPEN SHOP, OUT-TREE, RELEASE DATES (OMPM|outtree; r_i; p_ij = 1|C_max) is NP-complete

Source:
V. G. Timkovsky, "Identical parallel machines vs. unit-time shops and preemptions vs. chains in
scheduling complexity", European Journal of Operational Research 149(2) (2003), 355-376,
doi:10.1016/S0377-2217(02)00767-1 (the full text was not available);
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 10 (the MPM open-shop
model);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, class "Shop problems with
multipurpose machines" (`OMPM|outtree;r_i;p_ij=1|C_max`, minimal NP-hard in the strong sense,
credited to Timkovsky (2003)) and class "Open-shop problems without preemption" (the special case
`O|p_ij=1;outtree;r_i|C_max`, minimal NP-hard in the strong sense, credited to Timkovsky (2003)).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MultipurposeFlowShopInTreeReleaseMakespanWanted
public import WantedExt.Complexity.NPComplete.MultipurposeOpenShopPrecedenceMakespanWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeOpenShopOutTreeReleaseMakespan

open MultipurposeFlowShopPrecedenceMakespan (StagesWellFormed PrecedenceWellFormed completionTime)
open MultipurposeOpenShopPrecedenceMakespan (IsMPMOpenShopPrecedenceSchedule)
open MultipurposeFlowShopInTreeReleaseMakespan
  (MultipurposeFlowShopInTreeReleaseMakespanInstance Job Stage releaseDate ImmediateSuccessor)

/-!
# MPM OPEN SHOP, OUT-TREE, RELEASE DATES (OMPM|outtree; r_i; p_ij = 1|C_max) is NP-complete

INSTANCE: machines `M_1, …, M_m` (`m` part of the input); an MPM open shop with `r ≥ 1` stages
and nonempty machine sets `μ_1, …, μ_r ⊆ {M_1, …, M_m}`, pairwise different; jobs
`J_1, …, J_n`, each consisting of `r` operations `O_i1, …, O_ir` with processing times
`p_ij = 1`, where `O_ij` is processed by one machine of `μ_j`, and the operations of a job are
processed in any order but no two of them at the same time; a release date `r_i ∈ ℤ₀⁺` for each
job (no operation of `J_i` starts before `r_i`); a precedence relation `→` on the jobs that is an
out-tree (out-forest: each job has at most one immediate predecessor), where `i → k` means that
no operation of `J_k` starts before `J_i` is completed; and a bound `K`. Each machine processes
at most one operation at a time. QUESTION: is there a feasible schedule with makespan
`max_i C_i ≤ K`, where `C_i` is the completion time of job `i` (that of its last operation)?

The MPM open shop is Brucker's (*Scheduling Algorithms*, Chapter 10): MPM open-shop problems are
defined like MPM flow-shop problems (each job has exactly `r` operations, the `j`-th operation of
every job is processed by a machine of the same set `μ_j`, and the machine sets are different),
but with no precedence constraints between the operations of a job. The data are those of
`FMPM|intree; r_i; p_ij = 1|C_max`
(`WantedExt.Complexity.NPComplete.MultipurposeFlowShopInTreeReleaseMakespanWanted`), whose
instance is reused: the number `m` of machines, the stage machine sets `[μ_1, …, μ_r]`, the
release dates `[r_1, …, r_n]` (one per job, so the jobs are `Fin n`), the pairs `(i, k)` with
`i → k` and the bound `K`, with that module's `Job`, `Stage`, `releaseDate` and
`ImmediateSuccessor` (`k` is an immediate successor of `j`, and `j` an immediate predecessor of
`k`, when `j → k` and no job `c` has `j → c → k`). Well-formedness is that module's with the tree
condition reversed: the machine environment is well formed (`StagesWellFormed`: at least one
stage, machine indices below `m`, pairwise different sets) with nonempty machine sets, there is
at least one job (the makespan `max_i C_i` is a maximum over the jobs), the pairs form a strict
partial order on the jobs (`PrecedenceWellFormed`), and every job has at most one immediate
predecessor. The schedule predicate is `IsMPMOpenShopPrecedenceSchedule` of
`MultipurposeOpenShopPrecedenceMakespanWanted` (`OMPM|prec; p_ij = 1|C_max`): unit operations
`(j, s)` with start times `σ j s` and machines `a j s ∈ μ_s`, operations of one job and operations
on one machine at different times, and, for `i → k`, every operation of `k` starting no earlier
than `C_i`; `C_j` is `MultipurposeFlowShopPrecedenceMakespan.completionTime`, the latest
completion time of a job's operations. With unit operations and integer data, integer start times
lose no generality.

The classical open shop `O|p_ij=1;outtree;r_i|C_max` (`UnitOpenShopOutTreeReleaseMakespanWanted`)
is the special case `r = m`, `μ_j = {M_j}`. Brucker and Knust list both problems as minimal
NP-hard in the strong sense, crediting Timkovsky (2003), whose full text was not available.
Membership in NP: the machines, below `m`, and the start times, each below `K`, are a
certificate of polynomial size. Binary encoding of all numbers (the problem is NP-complete in the
strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: the machine environment is well formed and every stage
machine set is nonempty, there is at least one job, the listed pairs describe a precedence
relation on the jobs, and it is an out-tree (every job has at most one immediate predecessor). -/
def WellFormed (i : MultipurposeFlowShopInTreeReleaseMakespanInstance) : Prop :=
  StagesWellFormed i.1 i.2.1 ∧ (∀ M ∈ i.2.1, M ≠ []) ∧ i.2.2.1 ≠ [] ∧
    PrecedenceWellFormed i.2.2.1.length i.2.2.2.1 ∧
    ∀ k a b, ImmediateSuccessor i a k → ImmediateSuccessor i b k → a = b

/-- Some MPM open-shop schedule of the unit-time jobs obeys the precedence constraints, starts
no operation of a job before its release date, and has makespan at most `K`. -/
def MultipurposeOpenShopOutTreeReleaseMakespanFeasible
    (i : MultipurposeFlowShopInTreeReleaseMakespanInstance) : Prop :=
  ∃ σ : Job i → Stage i → ℕ, ∃ a : Job i → Stage i → Fin i.1,
    IsMPMOpenShopPrecedenceSchedule i.1 i.2.1 i.2.2.2.1 σ a ∧
      (∀ j s, releaseDate i j ≤ σ j s) ∧ ∀ j, completionTime (fun _ _ => 1) σ j ≤ i.2.2.2.2

open Classical in
/-- `OMPM|outtree; r_i; p_ij = 1|C_max` as a decision problem over bitstrings. -/
noncomputable def multipurposeOpenShopOutTreeReleaseMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipurposeFlowShopInTreeReleaseMakespanInstance) x with
  | some i => decide (WellFormed i ∧ MultipurposeOpenShopOutTreeReleaseMakespanFeasible i)
  | none => false

/-- **`OMPM|outtree; r_i; p_ij = 1|C_max` is NP-complete.** Source: Timkovsky (2003), as
recorded in the Brucker-Knust classification (with the special case
`O|p_ij=1;outtree;r_i|C_max`); Brucker (2007), Chapter 10 (model). -/
public theorem_wanted multipurposeOpenShopOutTreeReleaseMakespan_npComplete :
    multipurposeOpenShopOutTreeReleaseMakespanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multipurposeOpenShopOutTreeReleaseMakespanDec

end MetaMathlibExt.Complexity.NPComplete.MultipurposeOpenShopOutTreeReleaseMakespan
