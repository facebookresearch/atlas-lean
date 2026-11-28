/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPURPOSE-MACHINE OPEN SHOP OMPM2||Lmax: definitions

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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MultipurposeOpenShopPrecedenceMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeOpenShopTwoMachinesMaximumLateness

open MultipurposeFlowShopPrecedenceMakespan (StagesWellFormed completionTime)
open MultipurposeOpenShopPrecedenceMakespan (IsMPMOpenShopSchedule)

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

end MetaMathlibExt.Complexity.NPComplete.MultipurposeOpenShopTwoMachinesMaximumLateness
