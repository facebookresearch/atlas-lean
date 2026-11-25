/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPM OPEN SHOP, OUT-TREE, MAXIMUM LATENESS (OMPM|outtree; p_ij = 1|L_max) is NP-complete

Source:
P. Brucker, M. R. Garey and D. S. Johnson, "Scheduling equal-length tasks under treelike
precedence constraints to minimize maximum lateness", Mathematics of Operations Research 2
(1977), 275-284, doi:10.1287/moor.2.3.275;
V. G. Timkovsky, "Identical parallel machines vs. unit-time shops and preemptions vs. chains in
scheduling complexity", European Journal of Operational Research 149(2) (2003), 355-376,
doi:10.1016/S0377-2217(02)00767-1 (the full text was not available);
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 10 (the MPM open-shop
model);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, class "Shop problems with
multipurpose machines" (`OMPM|outtree;p_ij=1|L_max`, minimal NP-hard in the strong sense,
credited to Timkovsky (2003)).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MultipurposeFlowShopOutTreeLatenessWanted
public import WantedExt.Complexity.NPComplete.MultipurposeOpenShopPrecedenceMakespanWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeOpenShopOutTreeLateness

open MultipurposeFlowShopPrecedenceMakespan (completionTime)
open MultipurposeOpenShopPrecedenceMakespan (IsMPMOpenShopPrecedenceSchedule)
open MultipurposeFlowShopOutTreeLateness
  (MultipurposeFlowShopOutTreeLatenessInstance Job Stage dueDate bound WellFormed)

/-!
# MPM OPEN SHOP, OUT-TREE, MAXIMUM LATENESS (OMPM|outtree; p_ij = 1|L_max) is NP-complete

INSTANCE: machines `M_1, …, M_m` (`m` part of the input); an MPM open shop with `r ≥ 1` stages
and machine sets `μ_1, …, μ_r ⊆ {M_1, …, M_m}`, pairwise different; jobs `J_1, …, J_n`, each
consisting of `r` operations `O_i1, …, O_ir` with processing times `p_ij = 1`, where `O_ij` is
processed by one machine of `μ_j`, and the operations of a job are processed in any order but no
two of them at the same time; a due date `d_i ∈ ℤ` for each job; a precedence relation `→` on the
jobs that is an out-tree (out-forest: each job has at most one immediate predecessor), where
`i → k` means that no operation of `J_k` starts before `J_i` is completed; and a bound `K ∈ ℤ`.
Each machine processes at most one operation at a time. QUESTION: is there a feasible schedule
whose maximum lateness `max_i (C_i - d_i)` is at most `K`, where `C_i` is the completion time of
job `i` (that of its last operation)?

The MPM open shop is Brucker's (*Scheduling Algorithms*, Chapter 10): MPM open-shop problems are
defined like MPM flow-shop problems (each job has exactly `r` operations, the `j`-th operation of
every job is processed by a machine of the same set `μ_j`, and the machine sets are different),
but with no precedence constraints between the operations of a job. The data are those of
`FMPM|outtree; p_ij = 1|L_max`
(`WantedExt.Complexity.NPComplete.MultipurposeFlowShopOutTreeLatenessWanted`), whose instance,
`Job`, `Stage`, `dueDate`, `bound` and well-formedness are reused unchanged: the number `m` of
machines, the stage machine sets, the due dates (one per job, so the jobs are `Fin n`) and the
bound as `(positive part, negative part)` pairs, and the pairs `(i, k)` with `i → k`; the machine
environment is well formed (at least one stage, machine indices below `m`, pairwise different
sets), there is at least one job (a maximum over no jobs is undefined), the pairs form a strict
partial order on the jobs, and every job has at most one immediate predecessor. That
well-formedness does not ask for nonempty machine sets; with at least one job an empty set admits
no schedule, so such instances are no-instances either way. The schedule predicate is
`IsMPMOpenShopPrecedenceSchedule` of `MultipurposeOpenShopPrecedenceMakespanWanted`
(`OMPM|prec; p_ij = 1|C_max`): unit operations `(j, s)` with start times `σ j s` and machines
`a j s ∈ μ_s`, operations of one job and operations on one machine at different times, and, for
`i → k`, every operation of `k` starting no earlier than `C_i`; `C_j` is
`MultipurposeFlowShopPrecedenceMakespan.completionTime`, the latest completion time of a job's
operations. `L_max ≤ K` is stated as `C_i - d_i ≤ K` for every job `i`. With unit operations and
integer data, integer start times lose no generality.

The case of one stage `μ_1 = {M_1, …, M_m}` is `P|outtree; p_i = 1|L_max`, which Brucker, Garey
and Johnson prove NP-complete (their abstract: for `n` equal-length tasks on `m` identical
processors under out-tree precedence constraints, minimizing the maximum lateness "is
NP-complete"). The classical open shop `O|p_ij=1;outtree|L_max`
(`UnitOpenShopOutTreeMaxLatenessWanted`) is the case `r = m`, `μ_j = {M_j}`; Brucker and Knust
list both it and `OMPM|outtree;p_ij=1|L_max` as minimal NP-hard in the strong sense, crediting
Timkovsky (2003). Membership in NP: the machines and start times are a certificate; removing a
time slot in which no operation runs keeps every constraint and increases no completion time, so
some optimal schedule has all `r n` start times below `r n`. Binary encoding of all numbers (the
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

/-- Some MPM open-shop schedule of the unit-time jobs obeys the precedence constraints and has
maximum lateness at most `K`: `C_j - d_j ≤ K` for every job `j`. -/
def MultipurposeOpenShopOutTreeLatenessFeasible
    (i : MultipurposeFlowShopOutTreeLatenessInstance) : Prop :=
  ∃ σ : Job i → Stage i → ℕ, ∃ a : Job i → Stage i → Fin i.1,
    IsMPMOpenShopPrecedenceSchedule i.1 i.2.1 i.2.2.2.1 σ a ∧
      ∀ j, (completionTime (fun _ _ => 1) σ j : ℤ) - dueDate i j ≤ bound i

open Classical in
/-- `OMPM|outtree; p_ij = 1|L_max` as a decision problem over bitstrings. -/
noncomputable def multipurposeOpenShopOutTreeLatenessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipurposeFlowShopOutTreeLatenessInstance) x with
  | some i => decide (WellFormed i ∧ MultipurposeOpenShopOutTreeLatenessFeasible i)
  | none => false

/-- **`OMPM|outtree; p_ij = 1|L_max` is NP-complete.** Source: Brucker, Garey and Johnson
(1977), via the case of one stage `{M_1, …, M_m}`; Timkovsky (2003), as recorded in the
Brucker-Knust classification; Brucker (2007), Chapter 10 (model). -/
public theorem_wanted multipurposeOpenShopOutTreeLateness_npComplete :
    multipurposeOpenShopOutTreeLatenessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multipurposeOpenShopOutTreeLatenessDec

end MetaMathlibExt.Complexity.NPComplete.MultipurposeOpenShopOutTreeLateness
