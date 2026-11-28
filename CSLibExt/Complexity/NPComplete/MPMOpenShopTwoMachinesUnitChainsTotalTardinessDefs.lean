/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPM OPEN SHOP OMPM2|chains;p_ij=1|ΣT_i: definitions

Source:
V. G. Timkovsky, "Identical parallel machines vs. unit-time shops and preemptions vs. chains in
scheduling complexity", European Journal of Operational Research 149(2) (2003), 355-376,
doi:10.1016/S0377-2217(02)00767-1 (the full text was not available);
J. Y.-T. Leung and G. H. Young, "Minimizing total tardiness on a single machine with precedence
constraints", ORSA Journal on Computing 2 (1990), 346-352, doi:10.1287/ijoc.2.4.346
(`1|chains, p_j = 1|ΣT_j`);
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 10 (the MPM open-shop
model);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, class "Shop problems with
multipurpose machines" (`OMPM2|chains;p_ij=1|ΣT_i`, minimal NP-hard in the strong sense, credited
to Timkovsky (2003)) and class "Open-shop problems without preemption" (the special case
`O2|p_ij=1;chains|ΣT_i`, minimal NP-hard in the strong sense, credited to Timkovsky (2003)).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import CSLibExt.Complexity.NPComplete.MPMOpenShopTwoMachinesUnitChainsLateJobsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MPMOpenShopTwoMachinesUnitChainsTotalTardiness

open MultipurposeFlowShopPrecedenceMakespan (completionTime)
open MultipurposeOpenShopPrecedenceMakespan (IsMPMOpenShopPrecedenceSchedule)
open MPMOpenShopTwoMachinesUnitChainsLateJobs
  (MPMOpenShopTwoMachinesUnitChainsLateJobsInstance WellFormed)

/-- Some MPM open-shop schedule of the unit-time jobs on the two machines obeying the chain arcs
has total tardiness `Σ_j max(0, C_j - d_j) ≤ K`. -/
def MPMOpenShopTwoMachinesUnitChainsTotalTardinessFeasible
    (i : MPMOpenShopTwoMachinesUnitChainsLateJobsInstance) : Prop :=
  ∃ σ : Fin i.2.1.length → Fin i.1.length → ℕ, ∃ a : Fin i.2.1.length → Fin i.1.length → Fin 2,
    IsMPMOpenShopPrecedenceSchedule 2 i.1 i.2.2.1 σ a ∧
      (∑ j, (completionTime (fun _ _ => 1) σ j - i.2.1.get j)) ≤ i.2.2.2

open Classical in
/-- `OMPM2|chains;p_ij=1|ΣT_i` as a decision problem over bitstrings. -/
noncomputable def mpmOpenShopTwoMachinesUnitChainsTotalTardinessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MPMOpenShopTwoMachinesUnitChainsLateJobsInstance) x with
  | some i => decide (WellFormed i ∧ MPMOpenShopTwoMachinesUnitChainsTotalTardinessFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MPMOpenShopTwoMachinesUnitChainsTotalTardiness
