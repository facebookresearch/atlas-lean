/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FLOW SHOP F2|p_ij=1;chains|Σw_iC_i: definitions

Source:
V. S. Tanaev, Y. N. Sotskov and V. A. Strusevich, *Scheduling Theory. Multi-Stage Systems*,
Mathematics and its Applications 285, Kluwer Academic Publishers, Dordrecht (1994),
doi:10.1007/978-94-011-1192-8;
P. Brucker and S. Knust, *Complexity results for scheduling problems*, online classification,
class `f_nop` (flow-shop problems without preemption), Universität Osnabrück (last update 2006).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import CSLibExt.Complexity.NPComplete.TwoProcessorUnitFlowShopChainsTardinessDefs
public import CSLibExt.Complexity.NPComplete.UnitFlowShopTransportationDelaysDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitFlowShopChainsWeightedCompletion

open UnitFlowShopTransportationDelays (IsUnitFlowShopSchedule)
open TwoProcessorUnitFlowShopChainsTardiness
  (TwoProcessorUnitFlowShopChainsTardinessInstance Job Arc WellFormed)

/-- The weight `w_j` of job `j`: the `j`-th listed number. -/
def weight (i : TwoProcessorUnitFlowShopChainsTardinessInstance) (j : Job i) : ℕ :=
  i.1.get j

/-- Some unit-time two-machine flow-shop schedule obeys the chains (job `b` starts on `M₁` only
after its immediate predecessor `a` completes on `M₂`) and has total weighted completion time
`∑_j w_j C_j` at most `K`, where `C_j = σ 1 j + 1`. -/
def UnitFlowShopChainsWeightedCompletionFeasible
    (i : TwoProcessorUnitFlowShopChainsTardinessInstance) : Prop :=
  ∃ σ : Fin 2 → Job i → ℕ, IsUnitFlowShopSchedule (fun _ => 0) σ ∧
    (∀ a b, Arc i a b → σ 1 a + 1 ≤ σ 0 b) ∧
    ∑ j, weight i j * (σ 1 j + 1) ≤ i.2.2

open Classical in
/-- FLOW SHOP `F2|p_ij=1;chains|∑ w_i C_i` as a decision problem over bitstrings. -/
noncomputable def unitFlowShopChainsWeightedCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoProcessorUnitFlowShopChainsTardinessInstance) x with
  | some i => decide (WellFormed i ∧ UnitFlowShopChainsWeightedCompletionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UnitFlowShopChainsWeightedCompletion
