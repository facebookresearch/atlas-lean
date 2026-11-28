/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ROBOT FLOW SHOP, EQUAL PROCESSING TIMES, MAXIMUM LATENESS `F3;R1|p_ij=p;t_ik|L_max`: definitions

Source:
S. Knust, *Shop-scheduling problems with transportation*, PhD thesis, Universität Osnabrück
(1999) (not available; the result is recorded by Brucker and Knust);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `f_1ro` (flow-shop problems with
transportation times and a single robot), entry `F3;R1|p_ij=p;t_ik|L_max` (minimal NP-hard in
the strong sense, citing Knust 1999);
J. Hurink and S. Knust, "Makespan minimization for flow-shop problems with transportation
times and a single robot", Discrete Applied Mathematics 112 (2001), 199-216,
doi:10.1016/S0166-218X(00)00316-4 (the robot model).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.RobotFlowShopThreeMachinesEqualReleaseMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RobotFlowShopThreeMachinesEqualLateness

open RobotFlowShopThreeMachinesEqualReleaseMakespan (IsEqualRobotSchedule)

/-- An instance: the jobs `(t_i1, t_i2, d_i)` (transport times from `M_1` to `M_2` and from `M_2`
to `M_3`, due date), one per entry, the processing time `p`, and the bound `y` as a pair
`(y⁺, y⁻)` with `y = y⁺ - y⁻`. -/
abbrev RobotFlowShopThreeMachinesEqualLatenessInstance := List (ℕ × ℕ × ℕ) × ℕ × (ℕ × ℕ)

/-- The jobs of the instance, `Fin n` for `n` listed jobs. -/
abbrev Job (i : RobotFlowShopThreeMachinesEqualLatenessInstance) : Type := Fin i.1.length

/-- The transport time `t_i1` of job `i` from `M_1` to `M_2`. -/
def firstTransport (i : RobotFlowShopThreeMachinesEqualLatenessInstance) (j : Job i) : ℕ :=
  (i.1.get j).1

/-- The transport time `t_i2` of job `i` from `M_2` to `M_3`. -/
def secondTransport (i : RobotFlowShopThreeMachinesEqualLatenessInstance) (j : Job i) : ℕ :=
  (i.1.get j).2.1

/-- The due date `d_i` of job `i`. -/
def dueDate (i : RobotFlowShopThreeMachinesEqualLatenessInstance) (j : Job i) : ℕ :=
  (i.1.get j).2.2

/-- Well-formedness: the processing time `p` is positive, and there is at least one job, so that
`L_max` is a maximum over a nonempty set (transport times and due dates are non-negative
integers, and the bound `y⁺ - y⁻` is an arbitrary integer). -/
def WellFormed (i : RobotFlowShopThreeMachinesEqualLatenessInstance) : Prop :=
  0 < i.2.1 ∧ i.1 ≠ []

/-- Some single-robot schedule with operations of length `p` completes every job `j` with
lateness `C_j - d_j ≤ y⁺ - y⁻`, where `C_j = f j + p`. -/
def RobotFlowShopThreeMachinesEqualLatenessFeasible
    (i : RobotFlowShopThreeMachinesEqualLatenessInstance) : Prop :=
  ∃ a b c e f, IsEqualRobotSchedule i.2.1 (firstTransport i) (secondTransport i) a b c e f ∧
    ∀ j, f j + i.2.1 + i.2.2.2 ≤ dueDate i j + i.2.2.1

open Classical in
/-- `F3;R1|p_ij=p;t_ik|L_max` as a decision problem over bitstrings. -/
noncomputable def robotFlowShopThreeMachinesEqualLatenessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RobotFlowShopThreeMachinesEqualLatenessInstance) x with
  | some i => decide (WellFormed i ∧ RobotFlowShopThreeMachinesEqualLatenessFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.RobotFlowShopThreeMachinesEqualLateness
