/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPM OPEN SHOP, OUT-TREE, MAXIMUM LATENESS (OMPM|outtree; p_ij = 1|L_max): definitions

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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MultipurposeFlowShopOutTreeLatenessDefs
public import CSLibExt.Complexity.NPComplete.MultipurposeOpenShopPrecedenceMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeOpenShopOutTreeLateness

open MultipurposeFlowShopPrecedenceMakespan (completionTime)
open MultipurposeOpenShopPrecedenceMakespan (IsMPMOpenShopPrecedenceSchedule)
open MultipurposeFlowShopOutTreeLateness
  (MultipurposeFlowShopOutTreeLatenessInstance Job Stage dueDate bound WellFormed)

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

end MetaMathlibExt.Complexity.NPComplete.MultipurposeOpenShopOutTreeLateness
