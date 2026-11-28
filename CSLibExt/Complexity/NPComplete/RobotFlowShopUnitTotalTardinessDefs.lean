/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# F2;R1|p_ij=1;t_i|ΣT_i (two-machine unit flow shop, single transport robot, total tardiness):
definitions

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*, online classification,
class `f_1ro` (flow-shop problems with transportation times and a single robot), Universität
Osnabrück (last update 2004), entry `F2;R1|p_ij=1;t_i|ΣT_i` (minimal NP-hard, ordinary
sense), citing S. Knust, *Shop-scheduling problems with transportation*, PhD thesis, Universität
Osnabrück, Fachbereich Mathematik/Informatik (1999) (the thesis text was not available);
robot model: J. Hurink and S. Knust, "Makespan minimization for flow-shop problems with
transportation times and a single robot", Discrete Applied Mathematics 112 (2001), 199-216,
doi:10.1016/S0166-218X(00)00316-4.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import CSLibExt.Complexity.NPComplete.RobotFlowShopUnitWeightedTardinessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RobotFlowShopUnitTotalTardiness

open RobotFlowShopUnitWeightedTardiness (IsUnitRobotFlowShopSchedule)

/-- An instance: the jobs, job `j` being the `j`-th pair `(tⱼ, dⱼ)` of its transport time and
due date, and the bound `K`. -/
abbrev RobotFlowShopUnitTotalTardinessInstance := List (ℕ × ℕ) × ℕ

/-- The jobs of the instance, `Fin n` for `n` listed pairs. -/
abbrev Job (i : RobotFlowShopUnitTotalTardinessInstance) : Type := Fin i.1.length

/-- The transport time `tⱼ` of job `j`. -/
def transportTime (i : RobotFlowShopUnitTotalTardinessInstance) (j : Job i) : ℕ :=
  (i.1.get j).1

/-- The due date `dⱼ` of job `j`. -/
def dueDate (i : RobotFlowShopUnitTotalTardinessInstance) (j : Job i) : ℕ :=
  (i.1.get j).2

/-- Well-formedness: every instance (all data are non-negative integers). -/
def WellFormed (_ : RobotFlowShopUnitTotalTardinessInstance) : Prop := True

/-- Some single-robot schedule has total tardiness `Σⱼ max(0, Cⱼ - dⱼ)` at most `K`, where
`Cⱼ = σ 1 j + 1`. -/
def RobotFlowShopUnitTotalTardinessFeasible (i : RobotFlowShopUnitTotalTardinessInstance) :
    Prop :=
  ∃ σ : Fin 2 → Job i → ℕ, ∃ ρ : Job i → ℕ,
    IsUnitRobotFlowShopSchedule (transportTime i) σ ρ ∧
      ∑ j, (σ 1 j + 1 - dueDate i j) ≤ i.2

open Classical in
/-- F2;R1|p_ij=1;t_i|ΣT_i as a decision problem over bitstrings. -/
noncomputable def robotFlowShopUnitTotalTardinessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RobotFlowShopUnitTotalTardinessInstance) x with
  | some i => decide (WellFormed i ∧ RobotFlowShopUnitTotalTardinessFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.RobotFlowShopUnitTotalTardiness
