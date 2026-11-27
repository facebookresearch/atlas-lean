/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPURPOSE-MACHINE OPEN SHOP OMPM2||Lmax is NP-complete

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class "Shop problems with multipurpose machines" (`OMPM2||L_max`, minimal NP-hard in the strong
sense, credited to Lawler, Lenstra, and Rinnooy Kan 1981, 1982);
E. L. Lawler, J. K. Lenstra, and A. H. G. Rinnooy Kan, "Minimizing maximum lateness in a
two-machine open shop", Mathematics of Operations Research 6 (1981), 153-158,
doi:10.1287/moor.6.1.153; Erratum, Mathematics of Operations Research 7 (1982), 635,
doi:10.1287/moor.7.4.635 (the two-machine open shop, the case `μ_j = {M_j}`);
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 10 (the MPM open-shop
model).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MultipurposeOpenShopPrecedenceMakespanWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeOpenShopTwoMachinesMaximumLateness

open MultipurposeFlowShopPrecedenceMakespan (StagesWellFormed completionTime)
open MultipurposeOpenShopPrecedenceMakespan (IsMPMOpenShopSchedule)

/-!
# MULTIPURPOSE-MACHINE OPEN SHOP OMPM2||Lmax is NP-complete

INSTANCE: two machines `M_1, M_2`; an MPM open shop with `r ≥ 1` stages and nonempty machine sets
`μ_1, …, μ_r ⊆ {M_1, M_2}`, pairwise different; jobs `J_1, …, J_n`, each consisting of `r`
operations `O_i1, …, O_ir` with processing times `p_ij ∈ ℤ₀⁺`, where `O_ij` is processed by one
machine of `μ_j`, and the operations of a job are processed in any order but no two of them at
the same time; a due date `d_i ∈ ℤ₀⁺` for each job; and an integer bound `y`. Each machine
processes at most one operation at a time. QUESTION: is there a feasible schedule whose maximum
lateness `max_i (C_i - d_i)` is at most `y`, where `C_i` is the completion time of job `i` (that
of its last operation)?

This is Brucker and Knust's `OMPM2||L_max`, which they classify as NP-hard in the strong sense,
citing Lawler, Lenstra, and Rinnooy Kan (1981, with their 1982 erratum), whose two-machine open
shop `O2||L_max` is the case `r = 2`, `μ_1 = {M_1}`, `μ_2 = {M_2}`. The MPM open shop is
Brucker's (Chapter 10), as stated in `MultipurposeOpenShopPrecedenceMakespanWanted`: the schedule
is that module's `IsMPMOpenShopSchedule` (operation `(i, s)` gets a start time `σ i s` and a
machine `a i s ∈ μ_s`; two operations of one job, and two operations on one machine, occupy
disjoint intervals `[σ i s, σ i s + p_is)`), and `C_i` is `completionTime`
(`MultipurposeFlowShopPrecedenceMakespanWanted`). The instance lists the machine sets (machine
indices `0, 1`), one list `[p_i1, …, p_ir]` of processing times per job, one due date per job, and
the bound `y` as a pair `(y⁺, y⁻)` of naturals standing for `y⁺ - y⁻`; `C_i - d_i ≤ y` is stated
over `ℕ` as `C_i + y⁻ ≤ d_i + y⁺`. `WellFormed` asks for `StagesWellFormed` with `m = 2`, nonempty
machine sets, at least one job (the maximum lateness of no jobs is undefined; as in
`MultipurposeFlowShopOutTreeLatenessWanted`), `r` processing times per job and one due date per
job. Binary encoding of all
numbers. Membership in NP: the machines and start times (each at most `d_i + y⁺` for its job `i`)
are a certificate checked in polynomial time.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the stage machine sets `[μ_1, …, μ_r]` (machine indices `0, 1`), one list
`[p_i1, …, p_ir]` of processing times per job, one due date `d_i` per job, and the bound `y` as a
pair `(y⁺, y⁻)` with `y = y⁺ - y⁻`. -/
abbrev MultipurposeOpenShopTwoMachinesMaximumLatenessInstance :=
  List (List ℕ) × List (List ℕ) × List ℕ × (ℕ × ℕ)

/-- The jobs of the instance, `Fin n` for `n` listed jobs. -/
abbrev Job (i : MultipurposeOpenShopTwoMachinesMaximumLatenessInstance) : Type :=
  Fin i.2.1.length

/-- The stages of the instance, `Fin r` for `r` machine sets. -/
abbrev Stage (i : MultipurposeOpenShopTwoMachinesMaximumLatenessInstance) : Type :=
  Fin i.1.length

/-- The processing time `p_is` of the operation of job `i` in stage `s`. -/
def processingTime (i : MultipurposeOpenShopTwoMachinesMaximumLatenessInstance) (j : Job i)
    (s : Stage i) : ℕ :=
  (i.2.1.get j).getD s 0

/-- Well-formedness of an instance: a well-formed machine environment on `m = 2` machines with
nonempty machine sets, at least one job, one processing time per stage for every job, and one due
date per job. -/
def WellFormed (i : MultipurposeOpenShopTwoMachinesMaximumLatenessInstance) : Prop :=
  StagesWellFormed 2 i.1 ∧ (∀ M ∈ i.1, M ≠ []) ∧ i.2.1 ≠ [] ∧
    (∀ job ∈ i.2.1, job.length = i.1.length) ∧ i.2.2.1.length = i.2.1.length

/-- Some MPM open-shop schedule of the jobs on the two machines completes every job `i` with
lateness `C_i - d_i ≤ y⁺ - y⁻`. -/
def MultipurposeOpenShopTwoMachinesMaximumLatenessFeasible
    (i : MultipurposeOpenShopTwoMachinesMaximumLatenessInstance) : Prop :=
  ∃ σ : Job i → Stage i → ℕ, ∃ a : Job i → Stage i → Fin 2,
    IsMPMOpenShopSchedule 2 i.1 (processingTime i) σ a ∧
      ∀ j, completionTime (processingTime i) σ j + i.2.2.2.2 ≤ i.2.2.1.getD j 0 + i.2.2.2.1

open Classical in
/-- `OMPM2||L_max` as a decision problem over bitstrings. -/
noncomputable def multipurposeOpenShopTwoMachinesMaximumLatenessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipurposeOpenShopTwoMachinesMaximumLatenessInstance) x with
  | some i =>
    decide (WellFormed i ∧ MultipurposeOpenShopTwoMachinesMaximumLatenessFeasible i)
  | none => false

/-- **`OMPM2||L_max` is NP-complete.** Source: Brucker and Knust's classification; Lawler,
Lenstra, and Rinnooy Kan (1981; erratum 1982). -/
public theorem_wanted multipurposeOpenShopTwoMachinesMaximumLateness_npComplete :
    multipurposeOpenShopTwoMachinesMaximumLatenessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multipurposeOpenShopTwoMachinesMaximumLatenessDec

end MetaMathlibExt.Complexity.NPComplete.MultipurposeOpenShopTwoMachinesMaximumLateness
