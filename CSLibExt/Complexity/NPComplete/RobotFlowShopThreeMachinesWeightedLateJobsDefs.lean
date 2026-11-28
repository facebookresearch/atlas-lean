/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ROBOT FLOW SHOP, WEIGHTED NUMBER OF LATE JOBS `F3;R1|p_ij=1;t_ik|Σw_iU_i`: definitions

Source:
S. Knust, *Shop-scheduling problems with transportation*, PhD thesis, Universität Osnabrück
(1999) (not available; the result is recorded by Brucker and Knust);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `f_1ro` (flow-shop problems with
transportation times and a single robot), entry `F3;R1|p_ij=1;t_ik|Σw_iU_i` (minimal NP-hard in the
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

namespace MetaMathlibExt.Complexity.NPComplete.RobotFlowShopThreeMachinesWeightedLateJobs

open RobotFlowShopThreeMachinesWeightedTardiness
  (RobotFlowShopThreeMachinesWeightedTardinessInstance IsRobotSchedule)

/-- Some schedule has late jobs (`d_j < f j + 1`) of total weight at most `K`. -/
def RobotFlowShopThreeMachinesWeightedLateJobsFeasible
    (i : RobotFlowShopThreeMachinesWeightedTardinessInstance) : Prop :=
  ∃ a b c e f, IsRobotSchedule i a b c e f ∧
    ∑ j ∈ Finset.univ.filter (fun j => (i.1.get j).2.2.1 < f j + 1), (i.1.get j).2.2.2 ≤
      i.2

open Classical in
/-- `F3;R1|p_ij=1;t_ik|Σw_iU_i` as a decision problem over bitstrings; every decoded instance is
well formed. -/
noncomputable def robotFlowShopThreeMachinesWeightedLateJobsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RobotFlowShopThreeMachinesWeightedTardinessInstance) x with
  | some i => decide (RobotFlowShopThreeMachinesWeightedLateJobsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.RobotFlowShopThreeMachinesWeightedLateJobs
