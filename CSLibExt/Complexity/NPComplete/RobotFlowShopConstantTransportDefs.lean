/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# F2;R1|t_j=T|C_max (two-machine flow shop, single transport robot, constant transport times):
definitions

Source:
J. Hurink and S. Knust, "Makespan minimization for flow-shop problems with transportation
times and a single robot", Discrete Applied Mathematics 112 (2001), 199-216,
doi:10.1016/S0166-218X(00)00316-4 (Theorem 1: strongly NP-hard);
H. Kise, "On an automated two-machine flowshop scheduling problem with infinite buffer",
Journal of the Operations Research Society of Japan 34(3) (1991), 354-361,
doi:10.15807/jorsj.34.354 (NP-hard in the ordinary sense).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.FlowShopSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RobotFlowShopConstantTransport

/-- An instance: the jobs `(p₁ⱼ, p₂ⱼ)`, the transport time `T`, and the bound `K`. -/
abbrev RobotFlowShopConstantTransportInstance := List (ℕ × ℕ) × ℕ × ℕ

/-- The three-machine flow shop `M₁`, robot, `M₂`: job `j` has task lengths `[p₁ⱼ, T, p₂ⱼ]`,
and the deadline is `K`. -/
def toFlowShop (i : RobotFlowShopConstantTransportInstance) :
    FlowShopScheduling.FlowShopSchedulingInstance :=
  (3, i.1.map (fun q => [q.1, i.2.1, q.2]), i.2.2)

/-- Well-formedness: every instance (all data are non-negative integers). -/
def WellFormed (_ : RobotFlowShopConstantTransportInstance) : Prop := True

/-- Some schedule of `M₁`, the robot and `M₂` (a flow-shop schedule of `toFlowShop i`) has
makespan at most `K`. -/
def RobotFlowShopConstantTransportFeasible (i : RobotFlowShopConstantTransportInstance) :
    Prop :=
  FlowShopScheduling.FlowShopSchedulingFeasible (toFlowShop i)

open Classical in
/-- F2;R1|t_j=T|C_max as a decision
problem over bitstrings. -/
noncomputable def robotFlowShopConstantTransportDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RobotFlowShopConstantTransportInstance) x with
  | some i => decide (WellFormed i ∧ RobotFlowShopConstantTransportFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.RobotFlowShopConstantTransport
