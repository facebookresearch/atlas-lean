/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPEN SHOP O2|p_ij=1;chains|Σw_iC_i: definitions

Source:
V. G. Timkovsky, "Identical parallel machines vs. unit-time shops and preemptions vs. chains in
scheduling complexity", European Journal of Operational Research 149 (2003), 355-376,
doi:10.1016/S0377-2217(02)00767-1;
P. Brucker and S. Knust, *Complexity results for scheduling problems*, online classification,
class `o_nop` (open-shop problems without preemption), Universität Osnabrück (last update 2006).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import CSLibExt.Complexity.NPComplete.UnitFlowShopChainsWeightedCompletionDefs
public import CSLibExt.Complexity.NPComplete.UnitOpenShopOutTreeMaxLatenessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitOpenShopChainsWeightedCompletion

open UnitOpenShopOutTreeMaxLateness (IsUnitOpenShopSchedule)
open UnitFlowShopChainsWeightedCompletion (weight)
open TwoProcessorUnitFlowShopChainsTardiness
  (TwoProcessorUnitFlowShopChainsTardinessInstance Job WellFormed)

/-- Some unit-time two-machine open-shop schedule obeys the chains and has total weighted
completion time `∑_j w_j C_j` at most `K`, where `C_j = max (σ 0 j) (σ 1 j) + 1`. -/
def UnitOpenShopChainsWeightedCompletionFeasible
    (i : TwoProcessorUnitFlowShopChainsTardinessInstance) : Prop :=
  ∃ σ : Fin 2 → Job i → ℕ, IsUnitOpenShopSchedule 2 i.1.length i.2.1 σ ∧
    ∑ j, weight i j * (max (σ 0 j) (σ 1 j) + 1) ≤ i.2.2

open Classical in
/-- OPEN SHOP `O2|p_ij=1;chains|∑ w_i C_i` as a decision problem over bitstrings. -/
noncomputable def unitOpenShopChainsWeightedCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoProcessorUnitFlowShopChainsTardinessInstance) x with
  | some i => decide (WellFormed i ∧ UnitOpenShopChainsWeightedCompletionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UnitOpenShopChainsWeightedCompletion
