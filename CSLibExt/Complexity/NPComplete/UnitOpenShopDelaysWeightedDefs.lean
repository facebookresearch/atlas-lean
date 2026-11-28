/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPEN SHOP WITH TRANSPORTATION DELAYS O2|p_ij=1;t_i|Σw_iC_i: definitions

Source:
P. Brucker, T. C. E. Cheng, S. Knust and N. V. Shakhlevich, "Complexity results for flow-shop
and open-shop scheduling problems with transportation delays", Annals of Operations Research
129 (2004), 81-106, doi:10.1023/B:ANOR.0000030683.64615.c8;
P. Brucker and S. Knust, *Complexity results for scheduling problems*, online classification,
class `o_tra` (open-shop problems with transportation delays), Universität Osnabrück (last
update 2006).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import CSLibExt.Complexity.NPComplete.UnitFlowShopDelaysWeightedDefs
public import CSLibExt.Complexity.NPComplete.UnitOpenShopTransportationDelaysDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitOpenShopDelaysWeighted

open UnitOpenShopTransportationDelays (IsUnitOpenShopScheduleWithDelays)
open UnitFlowShopDelaysWeighted (UnitFlowShopDelaysWeightedInstance WellFormed)

/-- Some open-shop schedule with the job delays `t_j = (i.1.get j).1` has total weighted
completion time `∑_j w_j C_j` at most `K`, where `w_j = (i.1.get j).2` and
`C_j = max (σ 0 j) (σ 1 j) + 1`. -/
def UnitOpenShopDelaysWeightedFeasible (i : UnitFlowShopDelaysWeightedInstance) : Prop :=
  ∃ σ : Fin 2 → Fin i.1.length → ℕ,
    IsUnitOpenShopScheduleWithDelays (fun j => (i.1.get j).1) σ ∧
    ∑ j, (i.1.get j).2 * (max (σ 0 j) (σ 1 j) + 1) ≤ i.2

open Classical in
/-- OPEN SHOP WITH TRANSPORTATION DELAYS `O2|p_ij=1;t_i|∑ w_i C_i` as a decision problem over
bitstrings. -/
noncomputable def unitOpenShopDelaysWeightedDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnitFlowShopDelaysWeightedInstance) x with
  | some i => decide (WellFormed i ∧ UnitOpenShopDelaysWeightedFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UnitOpenShopDelaysWeighted
