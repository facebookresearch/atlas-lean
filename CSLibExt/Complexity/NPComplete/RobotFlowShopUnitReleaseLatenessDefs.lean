/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# F2;R1|p_ij=1;t_i;r_i|L_max (two-machine unit flow shop, single transport robot, release dates,: definitions
maximum lateness) is NP-complete

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*, online classification,
class `f_1ro` (flow-shop problems with transportation times and a single robot), Universität
Osnabrück (last update 2004), entry `F2;R1|p_ij=1;t_i;r_i|L_max` (minimal NP-hard,
strongly), citing S. Knust, *Shop-scheduling problems with transportation*, PhD thesis, Universität
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

namespace MetaMathlibExt.Complexity.NPComplete.RobotFlowShopUnitReleaseLateness

open RobotFlowShopUnitWeightedTardiness (IsUnitRobotFlowShopSchedule)

/-- An instance: the jobs, job `j` being the `j`-th triple `(rⱼ, tⱼ, dⱼ)` of its release date,
transport time and due date, and the bound `y` as a pair `(y⁺, y⁻)` with `y = y⁺ - y⁻`. -/
abbrev RobotFlowShopUnitReleaseLatenessInstance := List (ℕ × ℕ × ℕ) × (ℕ × ℕ)

/-- The jobs of the instance, `Fin n` for `n` listed triples. -/
abbrev Job (i : RobotFlowShopUnitReleaseLatenessInstance) : Type := Fin i.1.length

/-- The release date `rⱼ` of job `j`. -/
def releaseDate (i : RobotFlowShopUnitReleaseLatenessInstance) (j : Job i) : ℕ :=
  (i.1.get j).1

/-- The transport time `tⱼ` of job `j`. -/
def transportTime (i : RobotFlowShopUnitReleaseLatenessInstance) (j : Job i) : ℕ :=
  (i.1.get j).2.1

/-- The due date `dⱼ` of job `j`. -/
def dueDate (i : RobotFlowShopUnitReleaseLatenessInstance) (j : Job i) : ℕ :=
  (i.1.get j).2.2

/-- Well-formedness: there is at least one job, so that `L_max` is a maximum over a nonempty set
(release dates, transport times and due dates are non-negative integers, and the bound
`y⁺ - y⁻` is an arbitrary integer). -/
def WellFormed (i : RobotFlowShopUnitReleaseLatenessInstance) : Prop := i.1 ≠ []

/-- Some single-robot schedule starts every job on `M₁` no earlier than its release date and
completes every job `j` with lateness `Cⱼ - dⱼ ≤ y⁺ - y⁻`, where `Cⱼ = σ 1 j + 1`. -/
def RobotFlowShopUnitReleaseLatenessFeasible (i : RobotFlowShopUnitReleaseLatenessInstance) :
    Prop :=
  ∃ σ : Fin 2 → Job i → ℕ, ∃ ρ : Job i → ℕ,
    IsUnitRobotFlowShopSchedule (transportTime i) σ ρ ∧
      (∀ j, releaseDate i j ≤ σ 0 j) ∧
      ∀ j, σ 1 j + 1 + i.2.2 ≤ dueDate i j + i.2.1

open Classical in
/-- F2;R1|p_ij=1;t_i;r_i|L_max as a decision problem over bitstrings. -/
noncomputable def robotFlowShopUnitReleaseLatenessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RobotFlowShopUnitReleaseLatenessInstance) x with
  | some i => decide (WellFormed i ∧ RobotFlowShopUnitReleaseLatenessFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.RobotFlowShopUnitReleaseLateness
