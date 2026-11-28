/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPURPOSE-MACHINE OPEN SHOP OMPM2|r_i|Cmax: definitions

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class "Shop problems with multipurpose machines" (`OMPM2|r_i|C_max`, minimal NP-hard in the strong
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
public import CSLibExt.Complexity.NPComplete.MultipurposeOpenShopMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeOpenShopTwoMachinesReleaseMakespan

open MultipurposeFlowShopPrecedenceMakespan (completionTime)
open MultipurposeFlowShopThreeJobs (Job Stage processingTime)
open MultipurposeOpenShopMakespan (MultipurposeOpenShopMakespanInstance)
open MultipurposeOpenShopPrecedenceMakespan (IsMPMOpenShopSchedule)

/-- An instance: an `OMPM||C_max` instance (the number `m` of machines, the stage machine sets,
one list of processing times per job, the bound `K`) and the release dates `r_i`, one per job. -/
abbrev MultipurposeOpenShopTwoMachinesReleaseMakespanInstance :=
  MultipurposeOpenShopMakespanInstance × List ℕ

/-- Well-formedness of an instance: a well-formed `OMPM||C_max` instance with `m = 2` machines
and one release date per job. -/
def WellFormed (i : MultipurposeOpenShopTwoMachinesReleaseMakespanInstance) : Prop :=
  MultipurposeOpenShopMakespan.WellFormed i.1 ∧ i.1.1 = 2 ∧ i.2.length = i.1.2.2.1.length

/-- Some MPM open-shop schedule of the jobs starts no operation of job `i` before `r_i` and has
makespan at most `K`. -/
def MultipurposeOpenShopTwoMachinesReleaseMakespanFeasible
    (i : MultipurposeOpenShopTwoMachinesReleaseMakespanInstance) : Prop :=
  ∃ σ : Job i.1 → Stage i.1 → ℕ, ∃ a : Job i.1 → Stage i.1 → Fin i.1.1,
    IsMPMOpenShopSchedule i.1.1 i.1.2.1 (processingTime i.1) σ a ∧
      (∀ (j : Job i.1) (s : Stage i.1), i.2.getD j 0 ≤ σ j s) ∧
      ∀ j, completionTime (processingTime i.1) σ j ≤ i.1.2.2.2

open Classical in
/-- `OMPM2|r_i|C_max` as a decision problem over bitstrings. -/
noncomputable def multipurposeOpenShopTwoMachinesReleaseMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipurposeOpenShopTwoMachinesReleaseMakespanInstance) x with
  | some i => decide (WellFormed i ∧ MultipurposeOpenShopTwoMachinesReleaseMakespanFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MultipurposeOpenShopTwoMachinesReleaseMakespan
