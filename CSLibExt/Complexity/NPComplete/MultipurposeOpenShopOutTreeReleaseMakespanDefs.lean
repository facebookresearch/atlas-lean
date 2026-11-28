/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPM OPEN SHOP, OUT-TREE, RELEASE DATES (OMPM|outtree; r_i; p_ij = 1|C_max): definitions

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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MultipurposeFlowShopInTreeReleaseMakespanDefs
public import CSLibExt.Complexity.NPComplete.MultipurposeOpenShopPrecedenceMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeOpenShopOutTreeReleaseMakespan

open MultipurposeFlowShopPrecedenceMakespan (StagesWellFormed PrecedenceWellFormed completionTime)
open MultipurposeOpenShopPrecedenceMakespan (IsMPMOpenShopPrecedenceSchedule)
open MultipurposeFlowShopInTreeReleaseMakespan
  (MultipurposeFlowShopInTreeReleaseMakespanInstance Job Stage releaseDate ImmediateSuccessor)

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

end MetaMathlibExt.Complexity.NPComplete.MultipurposeOpenShopOutTreeReleaseMakespan
