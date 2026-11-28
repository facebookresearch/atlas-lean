/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPT FLOW SHOP FMPT2|chains;p_ij=1|Σw_iC_i: definitions

Source:
V. S. Tanaev, Y. N. Sotskov and V. A. Strusevich, *Scheduling Theory. Multi-Stage Systems*,
Mathematics and its Applications 285, Kluwer Academic Publishers, Dordrecht (1994),
doi:10.1007/978-94-011-1192-8;
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), doi:10.1007/978-3-540-69516-5,
Chapter 11 (the MPT flow-shop model);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multiprocessor
tasks", which lists `FMPT2|chains;p_ij=1|Σw_iC_i` as minimal NP-hard in the strong sense, citing
Tanaev et al. (1994), and class "Flow-shop problems without preemption", which lists the special
case `F2|p_ij=1;chains|Σw_iC_i` as minimal NP-hard in the strong sense, citing Tanaev et al.
(1994).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import CSLibExt.Complexity.NPComplete.MPMOpenShopTwoMachinesUnitChainsWeightedCompletionDefs
public import CSLibExt.Complexity.NPComplete.MPTFlowShopTwoMachinesUnitChainsLateJobsDefs
public import CSLibExt.Complexity.NPComplete.MultiprocessorTaskFlowShopPrecedenceMakespanDefs
public import CSLibExt.Complexity.NPComplete.MultipurposeFlowShopPrecedenceMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MPTFlowShopTwoMachinesUnitChainsWeightedCompletion

open MPMOpenShopTwoMachinesUnitChainsWeightedCompletion
  (MPMOpenShopTwoMachinesUnitChainsWeightedCompletionInstance)
open MPTFlowShopTwoMachinesUnitChainsLateJobs (WellFormed)
open MultipurposeFlowShopPrecedenceMakespan (completionTime)
open MultiprocessorTaskFlowShopPrecedenceMakespan (IsMPTPrecedenceSchedule)

/-- Some MPT flow-shop schedule of the unit-time jobs on the two machines obeying the chain arcs has
total weighted completion time `Σ_j w_j C_j ≤ K`. -/
def MPTFlowShopTwoMachinesUnitChainsWeightedCompletionFeasible
    (i : MPMOpenShopTwoMachinesUnitChainsWeightedCompletionInstance) : Prop :=
  ∃ σ : Fin i.2.1.length → Fin i.1.length → ℕ,
    IsMPTPrecedenceSchedule i.1 i.2.2.1 σ ∧
      ∑ j, i.2.1.get j * completionTime (fun _ _ => 1) σ j ≤ i.2.2.2

open Classical in
/-- `FMPT2|chains;p_ij=1|Σw_iC_i` as a decision problem over bitstrings. -/
noncomputable def mptFlowShopTwoMachinesUnitChainsWeightedCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MPMOpenShopTwoMachinesUnitChainsWeightedCompletionInstance) x with
  | some i =>
    decide (WellFormed i ∧ MPTFlowShopTwoMachinesUnitChainsWeightedCompletionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MPTFlowShopTwoMachinesUnitChainsWeightedCompletion
