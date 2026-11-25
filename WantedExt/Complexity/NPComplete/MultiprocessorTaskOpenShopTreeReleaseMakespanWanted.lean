/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPT OPEN SHOP, TREE PRECEDENCE, RELEASE DATES (OMPT|tree; r_i; p_ij = 1|C_max) is NP-complete

Source:
V. G. Timkovsky, "Identical parallel machines vs. unit-time shops and preemptions vs. chains in
scheduling complexity", European Journal of Operational Research 149 (2003), 355-376,
doi:10.1016/S0377-2217(02)00767-1;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multiprocessor
tasks", which lists `OMPT|tree; r_i; p_ij = 1|C_max` as minimal NP-hard in the strong sense with
the attribution to Timkovsky (2003);
P. Brucker, *Scheduling Algorithms*, 4th ed., Springer (2004), Chapter 11 (the MPT open-shop
model) and Section 1.3 (precedence relations).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MultiprocessorTaskFlowShopTreeReleaseMakespanWanted
public import WantedExt.Complexity.NPComplete.MultiprocessorTaskOpenShopPrecedenceMakespanWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopTreeReleaseMakespan

open MultipurposeFlowShopPrecedenceMakespan (completionTime)
open MultiprocessorTaskOpenShopPrecedenceMakespan (IsMPTOpenShopPrecedenceSchedule)
open MultiprocessorTaskFlowShopTreeReleaseMakespan
  (MultiprocessorTaskFlowShopTreeReleaseMakespanInstance releaseDate WellFormed)

/-!
# MPT OPEN SHOP, TREE PRECEDENCE, RELEASE DATES (OMPT|tree; r_i; p_ij = 1|C_max) is NP-complete

INSTANCE: machines `M_1, …, M_m`; an open shop with multiprocessor tasks (MPT) with `r ≥ 1`
stages and machine sets `μ_1, …, μ_r ⊆ {M_1, …, M_m}`, pairwise different; jobs `1, …, n`, each
consisting of `r` operations `O_i1, …, O_ir` with processing times `p_ij = 1`, where `O_ij`
requires every machine of `μ_j` during its processing and the operations of a job may be
processed in any order, but no two of them at the same time; a release date `r_i ∈ ℤ₀⁺` for each
job `i`, before which no operation of `i` starts; a precedence relation `→` on the jobs that is a
tree (an intree or an outtree); and a bound `K`. Operations requiring a common machine cannot be
processed simultaneously. QUESTION: is there a feasible schedule with makespan `max_i C_i ≤ K`,
where `C_i` is the completion time of job `i` (that of its last operation)?

The instance, the release dates and the well-formedness are those of the MPT flow shop
`FMPT|tree; r_i; p_ij = 1|C_max` (`MultiprocessorTaskFlowShopTreeReleaseMakespanWanted`): the
stage machine sets, the unit-time jobs listed with their release dates, and the arcs `(i, k)`
with `i → k` of an acyclic digraph whose immediate-predecessor relation is an intree or an
outtree (Brucker, Section 1.3; forests included; arcs implied by transitivity may be listed or
omitted). Only the schedule differs: it is the unit-time MPT open-shop schedule with precedence
`IsMPTOpenShopPrecedenceSchedule` of `MultiprocessorTaskOpenShopPrecedenceMakespanWanted`
(`OMPT|prec; p_ij = 1|C_max`), in which the operations of a job have no prescribed order; the
release date bounds the start of every operation of the job. Binary encoding of all numbers.

Brucker and Knust's open-shop table lists `O|p_ij = 1; outtree; r_i|C_max` as strongly NP-hard
(Timkovsky 2003, whose paper was not available to this formalization); it is the special case
`r = m`, `μ_j = {M_j}` with an outtree of this problem.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Some MPT open-shop schedule of the unit-time jobs obeys the tree precedence constraints,
starts no operation of a job before its release date, and has makespan at most `K`. -/
def MultiprocessorTaskOpenShopTreeReleaseMakespanFeasible
    (i : MultiprocessorTaskFlowShopTreeReleaseMakespanInstance) : Prop :=
  ∃ σ : Fin i.2.2.1.length → Fin i.2.1.length → ℕ,
    IsMPTOpenShopPrecedenceSchedule i.2.1 i.2.2.2.1 σ ∧ (∀ j s, releaseDate i j ≤ σ j s) ∧
      ∀ j, completionTime (fun _ _ => 1) σ j ≤ i.2.2.2.2

open Classical in
/-- `OMPT|tree; r_i; p_ij = 1|C_max` as a decision problem over bitstrings. -/
noncomputable def multiprocessorTaskOpenShopTreeReleaseMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultiprocessorTaskFlowShopTreeReleaseMakespanInstance) x with
  | some i => decide (WellFormed i ∧ MultiprocessorTaskOpenShopTreeReleaseMakespanFeasible i)
  | none => false

/-- **`OMPT|tree; r_i; p_ij = 1|C_max` is NP-complete.** Source: Timkovsky (2003); Brucker and
Knust, *Complexity results for scheduling problems*; Brucker (2004), Chapter 11. -/
public theorem_wanted multiprocessorTaskOpenShopTreeReleaseMakespan_npComplete :
    multiprocessorTaskOpenShopTreeReleaseMakespanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multiprocessorTaskOpenShopTreeReleaseMakespanDec

end MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopTreeReleaseMakespan
