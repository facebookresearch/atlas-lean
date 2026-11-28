/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ROBOT FLOW SHOP, MAXIMUM LATENESS WITH RELEASE DATES `F3;R1|p_ij=1;t_ik;r_i|L_max` is: definitions
# NP-complete

Source:
S. Knust, *Shop-scheduling problems with transportation*, PhD thesis, Universität Osnabrück
(1999) (not available; the result is recorded by Brucker and Knust);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `f_1ro` (flow-shop problems with
transportation times and a single robot), entry `F3;R1|p_ij=1;t_ik;r_i|L_max` (minimal NP-hard
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

namespace MetaMathlibExt.Complexity.NPComplete.RobotFlowShopThreeMachinesUnitReleaseLateness

open RobotFlowShopThreeMachinesWeightedTardiness (IsRobotSchedule)

/-- An instance: the jobs `(t_i1, t_i2, r_i, d_i)` (transport times from `M_1` to `M_2` and from
`M_2` to `M_3`, release date, due date), one per entry, and the bound `y` as a pair `(y⁺, y⁻)`
with `y = y⁺ - y⁻`. -/
abbrev RobotFlowShopThreeMachinesUnitReleaseLatenessInstance :=
  List (ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ)

/-- The jobs of the instance, `Fin n` for `n` listed jobs. -/
abbrev Job (i : RobotFlowShopThreeMachinesUnitReleaseLatenessInstance) : Type :=
  Fin i.1.length

/-- The release date `r_i` of job `i`. -/
def releaseDate (i : RobotFlowShopThreeMachinesUnitReleaseLatenessInstance) (j : Job i) : ℕ :=
  (i.1.get j).2.2.1

/-- The due date `d_i` of job `i`. -/
def dueDate (i : RobotFlowShopThreeMachinesUnitReleaseLatenessInstance) (j : Job i) : ℕ :=
  (i.1.get j).2.2.2

/-- Well-formedness: there is at least one job, so that `L_max` is a maximum over a nonempty set
(transport times, release dates and due dates are non-negative integers, and the bound
`y⁺ - y⁻` is an arbitrary integer). -/
def WellFormed (i : RobotFlowShopThreeMachinesUnitReleaseLatenessInstance) : Prop := i.1 ≠ []

/-- Some single-robot schedule starts every job on `M_1` no earlier than its release date and
completes every job `j` with lateness `C_j - d_j ≤ y⁺ - y⁻`, where `C_j = f j + 1`. -/
def RobotFlowShopThreeMachinesUnitReleaseLatenessFeasible
    (i : RobotFlowShopThreeMachinesUnitReleaseLatenessInstance) : Prop :=
  ∃ a b c e f, IsRobotSchedule (i.1, 0) a b c e f ∧ (∀ j, releaseDate i j ≤ a j) ∧
    ∀ j, f j + 1 + i.2.2 ≤ dueDate i j + i.2.1

open Classical in
/-- `F3;R1|p_ij=1;t_ik;r_i|L_max` as a decision problem over bitstrings. -/
noncomputable def robotFlowShopThreeMachinesUnitReleaseLatenessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RobotFlowShopThreeMachinesUnitReleaseLatenessInstance) x with
  | some i => decide (WellFormed i ∧ RobotFlowShopThreeMachinesUnitReleaseLatenessFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.RobotFlowShopThreeMachinesUnitReleaseLateness
