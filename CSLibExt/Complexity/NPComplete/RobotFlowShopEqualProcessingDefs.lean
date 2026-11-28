/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# F2;R1|p_ij=p;t_j|C_max (two-machine flow shop, single transport robot, equal processing times) is: definitions
NP-complete

Source:
J. Hurink and S. Knust, "Makespan minimization for flow-shop problems with transportation
times and a single robot", Discrete Applied Mathematics 112 (2001), 199-216,
doi:10.1016/S0166-218X(00)00316-4 (Theorem 2: strongly NP-hard).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.FlowShopSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RobotFlowShopEqualProcessing

/-- An instance: the processing time `p`, the transport times `tⱼ`, and the bound `K`. -/
abbrev RobotFlowShopEqualProcessingInstance := ℕ × List ℕ × ℕ

/-- The three-machine flow shop `M₁`, robot, `M₂`: job `j` has task lengths `[p, tⱼ, p]`, and
the deadline is `K`. -/
def toFlowShop (i : RobotFlowShopEqualProcessingInstance) :
    FlowShopScheduling.FlowShopSchedulingInstance :=
  (3, i.2.1.map (fun t => [i.1, t, i.1]), i.2.2)

/-- Well-formedness: every instance (all data are non-negative integers). -/
def WellFormed (_ : RobotFlowShopEqualProcessingInstance) : Prop := True

/-- Some schedule of `M₁`, the robot and `M₂` (a flow-shop schedule of `toFlowShop i`) has
makespan at most `K`. -/
def RobotFlowShopEqualProcessingFeasible (i : RobotFlowShopEqualProcessingInstance) :
    Prop :=
  FlowShopScheduling.FlowShopSchedulingFeasible (toFlowShop i)

open Classical in
/-- F2;R1|p_ij=p;t_j|C_max as a decision
problem over bitstrings. -/
noncomputable def robotFlowShopEqualProcessingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RobotFlowShopEqualProcessingInstance) x with
  | some i => decide (WellFormed i ∧ RobotFlowShopEqualProcessingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.RobotFlowShopEqualProcessing
