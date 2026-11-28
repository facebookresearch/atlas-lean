/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ROBOT FLOW SHOP, TOTAL TARDINESS `F3;R1|p_ij=1;t_ik|ΣT_i`: definitions

Source:
S. Knust, *Shop-scheduling problems with transportation*, PhD thesis, Universität Osnabrück
(1999) (not available; the result is recorded by Brucker and Knust);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `f_1ro` (flow-shop problems with
transportation times and a single robot), entry `F3;R1|p_ij=1;t_ik|ΣT_i` (minimal NP-hard in the
ordinary sense, citing Knust 1999);
J. Hurink and S. Knust, "Makespan minimization for flow-shop problems with transportation
times and a single robot", Discrete Applied Mathematics 112 (2001), 199-216,
doi:10.1016/S0166-218X(00)00316-4 (the robot model).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.RobotFlowShopThreeMachinesWeightedTardinessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RobotFlowShopThreeMachinesTotalTardiness

open RobotFlowShopThreeMachinesWeightedTardiness
  (RobotFlowShopThreeMachinesWeightedTardinessInstance
    RobotFlowShopThreeMachinesWeightedTardinessFeasible)

/-- Well-formedness of an instance: every job has weight `1`. -/
def WellFormed (i : RobotFlowShopThreeMachinesWeightedTardinessInstance) : Prop :=
  ∀ x ∈ i.1, x.2.2.2 = 1

open Classical in
/-- `F3;R1|p_ij=1;t_ik|ΣT_i` as a decision problem over bitstrings. -/
noncomputable def robotFlowShopThreeMachinesTotalTardinessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RobotFlowShopThreeMachinesWeightedTardinessInstance) x with
  | some i => decide (WellFormed i ∧ RobotFlowShopThreeMachinesWeightedTardinessFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.RobotFlowShopThreeMachinesTotalTardiness
