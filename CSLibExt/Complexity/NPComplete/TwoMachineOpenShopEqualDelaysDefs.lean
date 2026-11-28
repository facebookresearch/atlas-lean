/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-MACHINE OPEN SHOP WITH EQUAL DELAYS: definitions

Source:
W. Yu, *The two-machine flow shop problem with delays and the one-machine total tardiness
problem*, PhD thesis, Technische Universiteit Eindhoven (1996), Chapter 2, Appendix "The Open
Shop Problem with Equal Delays", Theorem 5 (pp. 17-18);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück
(online tables), class "Open-shop problems with transportation delays" (records the problem
`O2|t_ikl = T|Cmax` as minimal NP-hard, citing Yu (1996)).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.TwoMachineOpenShopTwoDelayValuesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoMachineOpenShopEqualDelays

open TwoMachineFlowShopTwoDelayValues (TwoMachineFlowShopTwoDelayValuesInstance)
open TwoMachineOpenShopTwoDelayValues (TwoMachineOpenShopTwoDelayValuesFeasible)

/-- Well-formedness: the two delay values coincide (`T₁ = T₂ = T`), and every job's delay is
`T₁` or `T₂` (`TwoMachineFlowShopTwoDelayValues.WellFormed`), i.e. equals `T`. -/
def WellFormed (i : TwoMachineFlowShopTwoDelayValuesInstance) : Prop :=
  i.1 = i.2.1 ∧ TwoMachineFlowShopTwoDelayValues.WellFormed i

open Classical in
/-- TWO-MACHINE OPEN SHOP WITH EQUAL DELAYS as a decision problem over bitstrings. -/
noncomputable def twoMachineOpenShopEqualDelaysDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoMachineFlowShopTwoDelayValuesInstance) x with
  | some i => decide (WellFormed i ∧ TwoMachineOpenShopTwoDelayValuesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoMachineOpenShopEqualDelays
