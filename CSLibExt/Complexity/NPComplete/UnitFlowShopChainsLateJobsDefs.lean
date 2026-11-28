/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FLOW SHOP F2|p_ij=1;chains|ΣU_i: definitions

Source:
P. Brucker and S. Knust, "Complexity results for single-machine problems with positive
finish-start time-lags", Computing 63 (1999), 299-316, doi:10.1007/s006070050036;
P. Brucker and S. Knust, *Complexity results for scheduling problems*, online classification,
class `f_nop` (flow-shop problems without preemption), Universität Osnabrück (last update 2006).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fintype.Card
public import CSLibExt.Complexity.NPComplete.TwoProcessorUnitFlowShopChainsTardinessDefs
public import CSLibExt.Complexity.NPComplete.UnitFlowShopTransportationDelaysDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitFlowShopChainsLateJobs

open UnitFlowShopTransportationDelays (IsUnitFlowShopSchedule)
open TwoProcessorUnitFlowShopChainsTardiness
  (TwoProcessorUnitFlowShopChainsTardinessInstance Job dueDate Arc)

/-- Some unit-time two-machine flow-shop schedule obeys the chains (job `b` starts on `M₁` only
after its immediate predecessor `a` completes on `M₂`) and has at most `K` late jobs: jobs `j`
with `d_j < C_j`, where `C_j = σ 1 j + 1`. -/
def UnitFlowShopChainsLateJobsFeasible (i : TwoProcessorUnitFlowShopChainsTardinessInstance) :
    Prop :=
  ∃ σ : Fin 2 → Job i → ℕ, IsUnitFlowShopSchedule (fun _ => 0) σ ∧
    (∀ a b, Arc i a b → σ 1 a + 1 ≤ σ 0 b) ∧
    (Finset.univ.filter fun j => dueDate i j < σ 1 j + 1).card ≤ i.2.2

open Classical in
/-- FLOW SHOP `F2|p_ij=1;chains|∑ U_i` as a decision problem over bitstrings. -/
noncomputable def unitFlowShopChainsLateJobsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoProcessorUnitFlowShopChainsTardinessInstance) x with
  | some i =>
    decide (TwoProcessorUnitFlowShopChainsTardiness.WellFormed i ∧
      UnitFlowShopChainsLateJobsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UnitFlowShopChainsLateJobs
