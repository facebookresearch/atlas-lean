/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPT OPEN SHOP WITH TREE PRECEDENCE AND UNIT TIMES (OMPT|tree; p_ij = 1|L_max): definitions

Source:
V. G. Timkovsky, "Identical parallel machines vs. unit-time shops and preemptions vs. chains in
scheduling complexity", European Journal of Operational Research 149 (2003), 355-376,
doi:10.1016/S0377-2217(02)00767-1;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multiprocessor
tasks", which lists `OMPT|tree; p_ij = 1|L_max` as minimal NP-hard in the strong sense with the
attribution to Timkovsky (2003);
P. Brucker, *Scheduling Algorithms*, 4th ed., Springer (2004), Chapter 11 (the MPT open-shop
model) and Section 1.3 (precedence relations).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MultiprocessorTaskFlowShopTreeLatenessDefs
public import CSLibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopPrecedenceMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopTreeLateness

open MultipurposeFlowShopPrecedenceMakespan (completionTime)
open MultiprocessorTaskOpenShopPrecedenceMakespan (IsMPTOpenShopPrecedenceSchedule)
open MultiprocessorTaskFlowShopTreeLateness
  (MultiprocessorTaskFlowShopTreeLatenessInstance dueDate bound WellFormed)

/-- Some MPT open-shop schedule of the unit-time jobs obeys the tree precedence constraints and
has `C_j - d_j ≤ K` for every job `j`. -/
def MultiprocessorTaskOpenShopTreeLatenessFeasible
    (i : MultiprocessorTaskFlowShopTreeLatenessInstance) : Prop :=
  ∃ σ : Fin i.2.2.1.length → Fin i.2.1.length → ℕ,
    IsMPTOpenShopPrecedenceSchedule i.2.1 i.2.2.2.1 σ ∧
      ∀ j, (completionTime (fun _ _ => 1) σ j : ℤ) - dueDate i j ≤ bound i

open Classical in
/-- `OMPT|tree; p_ij = 1|L_max` as a decision problem over bitstrings. -/
noncomputable def multiprocessorTaskOpenShopTreeLatenessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultiprocessorTaskFlowShopTreeLatenessInstance) x with
  | some i => decide (WellFormed i ∧ MultiprocessorTaskOpenShopTreeLatenessFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopTreeLateness
