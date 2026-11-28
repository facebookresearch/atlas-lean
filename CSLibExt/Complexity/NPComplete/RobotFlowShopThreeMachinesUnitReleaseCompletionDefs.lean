/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ROBOT FLOW SHOP, TOTAL COMPLETION TIME WITH RELEASE DATES `F3;R1|p_ij=1;t_ik;r_i|ΣC_i` is: definitions
# NP-complete

Source:
S. Knust, *Shop-scheduling problems with transportation*, PhD thesis, Universität Osnabrück
(1999) (not available; the result is recorded by Brucker and Knust);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `f_1ro` (flow-shop problems with
transportation times and a single robot), entry `F3;R1|p_ij=1;t_ik;r_i|ΣC_i` (minimal NP-hard
in the strong sense, citing Knust 1999);
J. Hurink and S. Knust, "Makespan minimization for flow-shop problems with transportation
times and a single robot", Discrete Applied Mathematics 112 (2001), 199-216,
doi:10.1016/S0166-218X(00)00316-4 (the robot model).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.RobotFlowShopThreeMachinesWeightedTardinessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RobotFlowShopThreeMachinesUnitReleaseCompletion

open RobotFlowShopThreeMachinesWeightedTardiness
  (RobotFlowShopThreeMachinesWeightedTardinessInstance Job IsRobotSchedule)

/-- The release date `r_i` of job `i`: the third entry of its tuple `(t_i1, t_i2, r_i, w_i)`. -/
def releaseDate (i : RobotFlowShopThreeMachinesWeightedTardinessInstance) (j : Job i) : ℕ :=
  (i.1.get j).2.2.1

/-- Well-formedness of an instance: every job has weight `1`. -/
def WellFormed (i : RobotFlowShopThreeMachinesWeightedTardinessInstance) : Prop :=
  ∀ x ∈ i.1, x.2.2.2 = 1

/-- Some single-robot schedule starts every job on `M_1` no earlier than its release date and
has `∑_j w_j C_j ≤ K`, where `C_j = f j + 1`. -/
def RobotFlowShopThreeMachinesUnitReleaseCompletionFeasible
    (i : RobotFlowShopThreeMachinesWeightedTardinessInstance) : Prop :=
  ∃ a b c e f, IsRobotSchedule i a b c e f ∧ (∀ j, releaseDate i j ≤ a j) ∧
    ∑ j, (i.1.get j).2.2.2 * (f j + 1) ≤ i.2

open Classical in
/-- `F3;R1|p_ij=1;t_ik;r_i|ΣC_i` as a decision problem over bitstrings. -/
noncomputable def robotFlowShopThreeMachinesUnitReleaseCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RobotFlowShopThreeMachinesWeightedTardinessInstance) x with
  | some i => decide (WellFormed i ∧ RobotFlowShopThreeMachinesUnitReleaseCompletionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.RobotFlowShopThreeMachinesUnitReleaseCompletion
