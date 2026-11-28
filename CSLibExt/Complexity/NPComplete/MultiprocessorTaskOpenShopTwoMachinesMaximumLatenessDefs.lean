/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPT OPEN SHOP WITH TWO PROCESSORS, MAXIMUM LATENESS (OMPT2||L_max): definitions

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multiprocessor
tasks" (`OMPT2||L_max`, minimal NP-hard in the strong sense, credited to Lawler, Lenstra, and
Rinnooy Kan 1981, 1982);
E. L. Lawler, J. K. Lenstra, and A. H. G. Rinnooy Kan, "Minimizing maximum lateness in a
two-machine open shop", Mathematics of Operations Research 6 (1981), 153-158,
doi:10.1287/moor.6.1.153; Erratum, Mathematics of Operations Research 7 (1982), 635,
doi:10.1287/moor.7.4.635 (the two-machine open shop, the case `μ_j = {M_j}`);
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 11 (the MPT open-shop
model).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MultipurposeOpenShopTwoMachinesMaximumLatenessDefs
public import CSLibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopPrecedenceMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopTwoMachinesMaximumLateness

open MultipurposeFlowShopPrecedenceMakespan (StagesWellFormed completionTime)
open MultipurposeOpenShopTwoMachinesMaximumLateness
  (MultipurposeOpenShopTwoMachinesMaximumLatenessInstance Job Stage processingTime)
open MultiprocessorTaskOpenShopPrecedenceMakespan (IsMPTOpenShopSchedule)

/-- Well-formedness of an instance: the stage processor sets are well formed for two processors
(`StagesWellFormed`), there is at least one job, every job lists one processing time per stage,
and there is one due date per job. -/
def WellFormed (i : MultipurposeOpenShopTwoMachinesMaximumLatenessInstance) : Prop :=
  StagesWellFormed 2 i.1 ∧ i.2.1 ≠ [] ∧ (∀ job ∈ i.2.1, job.length = i.1.length) ∧
    i.2.2.1.length = i.2.1.length

/-- Some MPT open-shop schedule of the jobs completes every job `j` with lateness
`C_j - d_j ≤ y⁺ - y⁻`. -/
def MultiprocessorTaskOpenShopTwoMachinesMaximumLatenessFeasible
    (i : MultipurposeOpenShopTwoMachinesMaximumLatenessInstance) : Prop :=
  ∃ σ : Job i → Stage i → ℕ, IsMPTOpenShopSchedule i.1 (processingTime i) σ ∧
    ∀ j, completionTime (processingTime i) σ j + i.2.2.2.2 ≤ i.2.2.1.getD j 0 + i.2.2.2.1

open Classical in
/-- `OMPT2||L_max` as a decision problem over bitstrings. -/
noncomputable def multiprocessorTaskOpenShopTwoMachinesMaximumLatenessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipurposeOpenShopTwoMachinesMaximumLatenessInstance) x with
  | some i =>
    decide (WellFormed i ∧ MultiprocessorTaskOpenShopTwoMachinesMaximumLatenessFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopTwoMachinesMaximumLateness
