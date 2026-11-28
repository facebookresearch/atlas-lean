/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ROBOT FLOW SHOP, TOTAL WEIGHTED TARDINESS `F3;R1|p_ij=1;t_ik|Σw_iT_i`: definitions

Source:
S. Knust, *Shop-scheduling problems with transportation*, PhD thesis, Universität Osnabrück
(1999) (not available; the result is recorded by Brucker and Knust);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `f_1ro` (flow-shop problems with
transportation times and a single robot), entry `F3;R1|p_ij=1;t_ik|Σw_iT_i` (minimal NP-hard in
the strong sense, citing Knust 1999);
J. Hurink and S. Knust, "Makespan minimization for flow-shop problems with transportation
times and a single robot", Discrete Applied Mathematics 112 (2001), 199-216,
doi:10.1016/S0166-218X(00)00316-4 (the robot model).
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RobotFlowShopThreeMachinesWeightedTardiness

/-- An instance: the jobs `(t_i1, t_i2, d_i, w_i)` (transport times from `M_1` to `M_2` and from
`M_2` to `M_3`, due date, weight), one per entry, and the bound `K`. -/
abbrev RobotFlowShopThreeMachinesWeightedTardinessInstance := List (ℕ × ℕ × ℕ × ℕ) × ℕ

/-- The jobs of the instance, `Fin n` for `n` listed jobs. -/
abbrev Job (i : RobotFlowShopThreeMachinesWeightedTardinessInstance) : Type := Fin i.1.length

/-- Start times `a`, `c`, `f` (operations on `M_1`, `M_2`, `M_3`) and `b`, `e` (transports
`M_1 → M_2`, `M_2 → M_3`) form a schedule: each job's steps in order, pairwise different start
times on each machine (unit operations), and pairwise disjoint sets of time units occupied by
the transports. -/
def IsRobotSchedule (i : RobotFlowShopThreeMachinesWeightedTardinessInstance)
    (a b c e f : Job i → ℕ) : Prop :=
  (∀ j, a j + 1 ≤ b j ∧ b j + (i.1.get j).1 ≤ c j ∧ c j + 1 ≤ e j ∧
      e j + (i.1.get j).2.1 ≤ f j) ∧
    Function.Injective a ∧ Function.Injective c ∧ Function.Injective f ∧
    (∀ j j', j ≠ j' → Disjoint (Finset.Ico (b j) (b j + (i.1.get j).1))
      (Finset.Ico (b j') (b j' + (i.1.get j').1))) ∧
    (∀ j j', j ≠ j' → Disjoint (Finset.Ico (e j) (e j + (i.1.get j).2.1))
      (Finset.Ico (e j') (e j' + (i.1.get j').2.1))) ∧
    ∀ j j', Disjoint (Finset.Ico (b j) (b j + (i.1.get j).1))
      (Finset.Ico (e j') (e j' + (i.1.get j').2.1))

/-- Some schedule has total weighted tardiness `∑_j w_j (f j + 1 - d_j)` at most `K` (natural
subtraction: the tardiness `max(0, C_j - d_j)`). -/
def RobotFlowShopThreeMachinesWeightedTardinessFeasible
    (i : RobotFlowShopThreeMachinesWeightedTardinessInstance) : Prop :=
  ∃ a b c e f, IsRobotSchedule i a b c e f ∧
    ∑ j, (i.1.get j).2.2.2 * (f j + 1 - (i.1.get j).2.2.1) ≤ i.2

open Classical in
/-- `F3;R1|p_ij=1;t_ik|Σw_iT_i` as a decision problem over bitstrings; every decoded instance is
well formed. -/
noncomputable def robotFlowShopThreeMachinesWeightedTardinessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RobotFlowShopThreeMachinesWeightedTardinessInstance) x with
  | some i => decide (RobotFlowShopThreeMachinesWeightedTardinessFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.RobotFlowShopThreeMachinesWeightedTardiness
