/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPT FLOW SHOP FMPT2|chains;p_ij=1|ΣT_i: definitions

Source:
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), doi:10.1007/978-3-540-69516-5,
Chapter 11 (the MPT flow-shop model);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multiprocessor
tasks", which lists `FMPT2|chains;p_ij=1|ΣT_i` as minimal NP-hard in the strong sense
("Single-machine problem");
J. Y.-T. Leung and G. H. Young, "Minimizing total tardiness on a single machine with precedence
constraints", ORSA Journal on Computing 2 (1990), 346-352, doi:10.1287/ijoc.2.4.346 (the
single-machine problem `1|chains;p_j=1|ΣT_j`).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import CSLibExt.Complexity.NPComplete.MPMOpenShopTwoMachinesUnitChainsLateJobsDefs
public import CSLibExt.Complexity.NPComplete.MPTFlowShopTwoMachinesUnitChainsLateJobsDefs
public import CSLibExt.Complexity.NPComplete.MultiprocessorTaskFlowShopPrecedenceMakespanDefs
public import CSLibExt.Complexity.NPComplete.MultipurposeFlowShopPrecedenceMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MPTFlowShopTwoMachinesUnitChainsTotalTardiness

open MPMOpenShopTwoMachinesUnitChainsLateJobs (MPMOpenShopTwoMachinesUnitChainsLateJobsInstance)
open MPTFlowShopTwoMachinesUnitChainsLateJobs (WellFormed)
open MultipurposeFlowShopPrecedenceMakespan (completionTime)
open MultiprocessorTaskFlowShopPrecedenceMakespan (IsMPTPrecedenceSchedule)

/-- Some MPT flow-shop schedule of the unit-time jobs on the two machines obeying the chain arcs has
total tardiness `Σ_j max(0, C_j - d_j)` at most `K` (natural-number subtraction truncates at `0`).
-/
def MPTFlowShopTwoMachinesUnitChainsTotalTardinessFeasible
    (i : MPMOpenShopTwoMachinesUnitChainsLateJobsInstance) : Prop :=
  ∃ σ : Fin i.2.1.length → Fin i.1.length → ℕ,
    IsMPTPrecedenceSchedule i.1 i.2.2.1 σ ∧
      (∑ j, (completionTime (fun _ _ => 1) σ j - i.2.1.get j)) ≤ i.2.2.2

open Classical in
/-- `FMPT2|chains;p_ij=1|ΣT_i` as a decision problem over bitstrings. -/
noncomputable def mptFlowShopTwoMachinesUnitChainsTotalTardinessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MPMOpenShopTwoMachinesUnitChainsLateJobsInstance) x with
  | some i => decide (WellFormed i ∧ MPTFlowShopTwoMachinesUnitChainsTotalTardinessFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MPTFlowShopTwoMachinesUnitChainsTotalTardiness
