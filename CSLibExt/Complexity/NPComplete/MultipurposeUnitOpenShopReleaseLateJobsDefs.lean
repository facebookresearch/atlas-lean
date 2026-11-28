/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPURPOSE-MACHINE OPEN SHOP OMPM|r_i;p_ij=1|ΣU_i: definitions

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class "Shop problems with multipurpose machines" (`OMPM|p_ij=1;r_i|ΣU_i`, minimal NP-hard in the
strong sense, credited to Kravchenko 1999);
S. A. Kravchenko, "On the complexity of minimizing the number of late jobs in unit time open
shop", Discrete Applied Mathematics 100 (2000), 127-132, doi:10.1016/S0166-218X(99)00202-4 (the
open shop `O|p_ij=1;r_i|ΣU_i`, the case `μ_j = {M_j}`; the full text was not available);
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 10 (the MPM open-shop
model).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MultipurposeOpenShopMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeUnitOpenShopReleaseLateJobs

open MultipurposeFlowShopPrecedenceMakespan (completionTime)
open MultipurposeFlowShopThreeJobs (Job Stage processingTime)
open MultipurposeOpenShopMakespan (MultipurposeOpenShopMakespanInstance)
open MultipurposeOpenShopPrecedenceMakespan (IsMPMOpenShopSchedule)

/-- An instance: an `OMPM||C_max` instance (the number `m` of machines, the stage machine sets,
one list of processing times per job, and the bound `K` on the number of late jobs) and the
pairs `(r_i, d_i)` of release date and due date, one per job. -/
abbrev MultipurposeUnitOpenShopReleaseLateJobsInstance :=
  MultipurposeOpenShopMakespanInstance × List (ℕ × ℕ)

/-- Well-formedness of an instance: a well-formed `OMPM||C_max` instance with all processing
times `1`, and one release date and due date per job. -/
def WellFormed (i : MultipurposeUnitOpenShopReleaseLateJobsInstance) : Prop :=
  MultipurposeOpenShopMakespan.WellFormed i.1 ∧ (∀ job ∈ i.1.2.2.1, ∀ p ∈ job, p = 1) ∧
    i.2.length = i.1.2.2.1.length

/-- Some MPM open-shop schedule of the unit-time jobs starts no operation of job `i` before `r_i`
and has at most `K` late jobs (jobs `i` with `d_i < C_i`). -/
def MultipurposeUnitOpenShopReleaseLateJobsFeasible
    (i : MultipurposeUnitOpenShopReleaseLateJobsInstance) : Prop :=
  ∃ σ : Job i.1 → Stage i.1 → ℕ, ∃ a : Job i.1 → Stage i.1 → Fin i.1.1,
    IsMPMOpenShopSchedule i.1.1 i.1.2.1 (processingTime i.1) σ a ∧
      (∀ (j : Job i.1) (s : Stage i.1), (i.2.getD j (0, 0)).1 ≤ σ j s) ∧
      (Finset.univ.filter fun j : Job i.1 =>
        (i.2.getD j (0, 0)).2 < completionTime (processingTime i.1) σ j).card ≤ i.1.2.2.2

open Classical in
/-- `OMPM|p_ij=1;r_i|ΣU_i` as a decision problem over bitstrings. -/
noncomputable def multipurposeUnitOpenShopReleaseLateJobsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipurposeUnitOpenShopReleaseLateJobsInstance) x with
  | some i => decide (WellFormed i ∧ MultipurposeUnitOpenShopReleaseLateJobsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MultipurposeUnitOpenShopReleaseLateJobs
