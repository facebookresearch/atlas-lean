/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# F2;R1|p_ij=1;t_i|Σw_iT_i (two-machine unit flow shop, single transport robot, total weighted
tardiness): definitions

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*, online classification,
class `f_1ro` (flow-shop problems with transportation times and a single robot), Universität
Osnabrück (last update 2004), entry `F2;R1|p_ij=1;t_i|Σw_iT_i` (minimal NP-hard, strongly),
citing S. Knust, *Shop-scheduling problems with transportation*, PhD thesis, Universität
Osnabrück, Fachbereich Mathematik/Informatik (1999) (the thesis text was not available);
robot model: J. Hurink and S. Knust, "Makespan minimization for flow-shop problems with
transportation times and a single robot", Discrete Applied Mathematics 112 (2001), 199-216,
doi:10.1016/S0166-218X(00)00316-4.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import CSLibExt.Complexity.NPComplete.UnitFlowShopTransportationDelaysDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RobotFlowShopUnitWeightedTardiness

open UnitFlowShopTransportationDelays (IsUnitFlowShopSchedule)

/-- A schedule of the two-machine flow shop with unit-time operations and a single transport
robot: `σ 0 j` and `σ 1 j` are the start times of job `j`'s operations on `M₁` and `M₂`, and
`ρ j` is the start time of its transport, which takes `t j`. The machines run a schedule of the
unit-time flow shop with delays `t`; each transport starts once the job's operation on `M₁`
completes and ends by the start of its operation on `M₂`; and the robot carries one job at a
time: the transports of distinct jobs do not overlap. -/
def IsUnitRobotFlowShopSchedule {n : ℕ} (t : Fin n → ℕ) (σ : Fin 2 → Fin n → ℕ)
    (ρ : Fin n → ℕ) : Prop :=
  IsUnitFlowShopSchedule t σ ∧
    (∀ j, σ 0 j + 1 ≤ ρ j ∧ ρ j + t j ≤ σ 1 j) ∧
    ∀ j k, j ≠ k → ρ j + t j ≤ ρ k ∨ ρ k + t k ≤ ρ j

/-- An instance: the jobs, job `j` being the `j`-th triple `(tⱼ, dⱼ, wⱼ)` of its transport
time, due date and weight, and the bound `K`. -/
abbrev RobotFlowShopUnitWeightedTardinessInstance := List (ℕ × ℕ × ℕ) × ℕ

/-- The jobs of the instance, `Fin n` for `n` listed triples. -/
abbrev Job (i : RobotFlowShopUnitWeightedTardinessInstance) : Type := Fin i.1.length

/-- The transport time `tⱼ` of job `j`. -/
def transportTime (i : RobotFlowShopUnitWeightedTardinessInstance) (j : Job i) : ℕ :=
  (i.1.get j).1

/-- The due date `dⱼ` of job `j`. -/
def dueDate (i : RobotFlowShopUnitWeightedTardinessInstance) (j : Job i) : ℕ :=
  (i.1.get j).2.1

/-- The weight `wⱼ` of job `j`. -/
def weight (i : RobotFlowShopUnitWeightedTardinessInstance) (j : Job i) : ℕ :=
  (i.1.get j).2.2

/-- Well-formedness: every instance (all data are non-negative integers). -/
def WellFormed (_ : RobotFlowShopUnitWeightedTardinessInstance) : Prop := True

/-- Some single-robot schedule has total weighted tardiness `Σⱼ wⱼ · max(0, Cⱼ - dⱼ)` at most
`K`, where `Cⱼ = σ 1 j + 1`. -/
def RobotFlowShopUnitWeightedTardinessFeasible
    (i : RobotFlowShopUnitWeightedTardinessInstance) : Prop :=
  ∃ σ : Fin 2 → Job i → ℕ, ∃ ρ : Job i → ℕ,
    IsUnitRobotFlowShopSchedule (transportTime i) σ ρ ∧
      ∑ j, weight i j * (σ 1 j + 1 - dueDate i j) ≤ i.2

open Classical in
/-- F2;R1|p_ij=1;t_i|Σw_iT_i as a decision problem over bitstrings. -/
noncomputable def robotFlowShopUnitWeightedTardinessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RobotFlowShopUnitWeightedTardinessInstance) x with
  | some i => decide (WellFormed i ∧ RobotFlowShopUnitWeightedTardinessFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.RobotFlowShopUnitWeightedTardiness
