/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# F2;R1|p_ij=1;t_i|Σw_iU_i (two-machine unit flow shop, single transport robot, weighted number: definitions
of late jobs) is NP-complete

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*, online classification,
class `f_1ro` (flow-shop problems with transportation times and a single robot), Universität
Osnabrück (last update 2004), entry `F2;R1|p_ij=1;t_i|Σw_iU_i` (minimal NP-hard, ordinary
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

namespace MetaMathlibExt.Complexity.NPComplete.RobotFlowShopUnitWeightedLateJobs

open RobotFlowShopUnitWeightedTardiness

/-- Some single-robot schedule has total weight of late jobs, the sum of `wⱼ` over the jobs
with `dⱼ < Cⱼ = σ 1 j + 1`, at most `K`. -/
def RobotFlowShopUnitWeightedLateJobsFeasible
    (i : RobotFlowShopUnitWeightedTardinessInstance) : Prop :=
  ∃ σ : Fin 2 → Job i → ℕ, ∃ ρ : Job i → ℕ,
    IsUnitRobotFlowShopSchedule (transportTime i) σ ρ ∧
      ∑ j ∈ Finset.univ.filter (fun j => dueDate i j < σ 1 j + 1), weight i j ≤ i.2

open Classical in
/-- F2;R1|p_ij=1;t_i|Σw_iU_i as a decision problem over bitstrings. -/
noncomputable def robotFlowShopUnitWeightedLateJobsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RobotFlowShopUnitWeightedTardinessInstance) x with
  | some i => decide (WellFormed i ∧ RobotFlowShopUnitWeightedLateJobsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.RobotFlowShopUnitWeightedLateJobs
