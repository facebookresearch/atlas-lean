/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ROBOT FLOW SHOP, EQUAL PROCESSING TIMES, MAKESPAN WITH RELEASE DATES: definitions
# `F3;R1|p_ij=p;t_ik;r_i|C_max` is NP-complete

Source:
S. Knust, *Shop-scheduling problems with transportation*, PhD thesis, Universität Osnabrück
(1999) (not available; the result is recorded by Brucker and Knust);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `f_1ro` (flow-shop problems with
transportation times and a single robot), entry `F3;R1|p_ij=p;t_ik;r_i|C_max` (minimal NP-hard
in the strong sense, citing Knust 1999);
J. Hurink and S. Knust, "Makespan minimization for flow-shop problems with transportation
times and a single robot", Discrete Applied Mathematics 112 (2001), 199-216,
doi:10.1016/S0166-218X(00)00316-4 (the robot model).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RobotFlowShopThreeMachinesEqualReleaseMakespan

/-- Start times `a`, `c`, `f` (operations on `M_1`, `M_2`, `M_3`, each of length `p`) and `b`,
`e` (transports `M_1 → M_2` and `M_2 → M_3` of job `j`, of lengths `t₁ j` and `t₂ j`) form a
single-robot flow-shop schedule of the jobs `Fin n`: each job's steps in order, pairwise
disjoint sets of time units occupied by the operations on each machine, and pairwise disjoint
sets of time units occupied by the transports. -/
def IsEqualRobotSchedule (p : ℕ) {n : ℕ} (t₁ t₂ : Fin n → ℕ) (a b c e f : Fin n → ℕ) : Prop :=
  (∀ j, a j + p ≤ b j ∧ b j + t₁ j ≤ c j ∧ c j + p ≤ e j ∧ e j + t₂ j ≤ f j) ∧
    (∀ j j', j ≠ j' → Disjoint (Finset.Ico (a j) (a j + p)) (Finset.Ico (a j') (a j' + p))) ∧
    (∀ j j', j ≠ j' → Disjoint (Finset.Ico (c j) (c j + p)) (Finset.Ico (c j') (c j' + p))) ∧
    (∀ j j', j ≠ j' → Disjoint (Finset.Ico (f j) (f j + p)) (Finset.Ico (f j') (f j' + p))) ∧
    (∀ j j', j ≠ j' →
      Disjoint (Finset.Ico (b j) (b j + t₁ j)) (Finset.Ico (b j') (b j' + t₁ j'))) ∧
    (∀ j j', j ≠ j' →
      Disjoint (Finset.Ico (e j) (e j + t₂ j)) (Finset.Ico (e j') (e j' + t₂ j'))) ∧
    ∀ j j', Disjoint (Finset.Ico (b j) (b j + t₁ j)) (Finset.Ico (e j') (e j' + t₂ j'))

/-- An instance: the jobs `(t_i1, t_i2, r_i)` (transport times from `M_1` to `M_2` and from `M_2`
to `M_3`, release date), one per entry, the processing time `p` and the bound `K`. -/
abbrev RobotFlowShopThreeMachinesEqualReleaseMakespanInstance := List (ℕ × ℕ × ℕ) × ℕ × ℕ

/-- The jobs of the instance, `Fin n` for `n` listed jobs. -/
abbrev Job (i : RobotFlowShopThreeMachinesEqualReleaseMakespanInstance) : Type := Fin i.1.length

/-- The transport time `t_i1` of job `i` from `M_1` to `M_2`. -/
def firstTransport (i : RobotFlowShopThreeMachinesEqualReleaseMakespanInstance) (j : Job i) :
    ℕ :=
  (i.1.get j).1

/-- The transport time `t_i2` of job `i` from `M_2` to `M_3`. -/
def secondTransport (i : RobotFlowShopThreeMachinesEqualReleaseMakespanInstance) (j : Job i) :
    ℕ :=
  (i.1.get j).2.1

/-- The release date `r_i` of job `i`. -/
def releaseDate (i : RobotFlowShopThreeMachinesEqualReleaseMakespanInstance) (j : Job i) : ℕ :=
  (i.1.get j).2.2

/-- Well-formedness: there is at least one job, so that `C_max` is a maximum over a nonempty set,
and the processing time `p` is positive. -/
def WellFormed (i : RobotFlowShopThreeMachinesEqualReleaseMakespanInstance) : Prop :=
  i.1 ≠ [] ∧ 0 < i.2.1

/-- Some single-robot schedule with operations of length `p` starts every job on `M_1` no earlier
than its release date and completes every job by `K` (`C_j = f j + p`). -/
def RobotFlowShopThreeMachinesEqualReleaseMakespanFeasible
    (i : RobotFlowShopThreeMachinesEqualReleaseMakespanInstance) : Prop :=
  ∃ a b c e f, IsEqualRobotSchedule i.2.1 (firstTransport i) (secondTransport i) a b c e f ∧
    (∀ j, releaseDate i j ≤ a j) ∧ ∀ j, f j + i.2.1 ≤ i.2.2

open Classical in
/-- `F3;R1|p_ij=p;t_ik;r_i|C_max` as a decision problem over bitstrings. -/
noncomputable def robotFlowShopThreeMachinesEqualReleaseMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RobotFlowShopThreeMachinesEqualReleaseMakespanInstance) x with
  | some i => decide (WellFormed i ∧ RobotFlowShopThreeMachinesEqualReleaseMakespanFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.RobotFlowShopThreeMachinesEqualReleaseMakespan
