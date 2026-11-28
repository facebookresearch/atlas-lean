/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPT OPEN SHOP WITH TWO PROCESSORS AND RELEASE DATES (OMPT2|r_i|C_max): definitions

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multiprocessor
tasks" (`OMPT2|r_i|C_max`, minimal NP-hard in the strong sense, credited to Lawler, Lenstra, and
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
public import CSLibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopTwoMachinesTotalCompletionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopTwoMachinesReleaseMakespan

open MultipurposeFlowShopPrecedenceMakespan (completionTime)
open MultipurposeFlowShopThreeJobs (MultipurposeFlowShopThreeJobsInstance Job Stage
  processingTime)
open MultiprocessorTaskOpenShopPrecedenceMakespan (IsMPTOpenShopSchedule)

/-- An instance: an `OMPT2||ΣC_i` instance (the number of processors, the stage processor sets,
one list of `r` processing times per job, the bound `K`) and the release dates, job `j` having
the `j`-th listed release date `r_j`. -/
abbrev MultiprocessorTaskOpenShopTwoMachinesReleaseMakespanInstance :=
  MultipurposeFlowShopThreeJobsInstance × List ℕ

/-- Well-formedness of an instance: a well-formed `OMPT2||ΣC_i` instance with one release date
per job. -/
def WellFormed (i : MultiprocessorTaskOpenShopTwoMachinesReleaseMakespanInstance) : Prop :=
  MultiprocessorTaskOpenShopTwoMachinesTotalCompletion.WellFormed i.1 ∧
    i.2.length = i.1.2.2.1.length

/-- Some MPT open-shop schedule of the jobs starts no task of job `j` before `r_j` and has
makespan at most `K`. -/
def MultiprocessorTaskOpenShopTwoMachinesReleaseMakespanFeasible
    (i : MultiprocessorTaskOpenShopTwoMachinesReleaseMakespanInstance) : Prop :=
  ∃ σ : Job i.1 → Stage i.1 → ℕ, IsMPTOpenShopSchedule i.1.2.1 (processingTime i.1) σ ∧
    (∀ (j : Job i.1) s, i.2.getD j 0 ≤ σ j s) ∧
      ∀ j, completionTime (processingTime i.1) σ j ≤ i.1.2.2.2

open Classical in
/-- `OMPT2|r_i|C_max` as a decision problem over bitstrings. -/
noncomputable def multiprocessorTaskOpenShopTwoMachinesReleaseMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultiprocessorTaskOpenShopTwoMachinesReleaseMakespanInstance) x with
  | some i =>
    decide (WellFormed i ∧ MultiprocessorTaskOpenShopTwoMachinesReleaseMakespanFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopTwoMachinesReleaseMakespan
