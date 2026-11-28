/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# F2;R1|p_ij=1;t_i;r_i|ΣC_i (two-machine unit flow shop, single transport robot, release dates,
total completion time): definitions

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*, online classification,
class `f_1ro` (flow-shop problems with transportation times and a single robot), Universität
Osnabrück (last update 2004), entry `F2;R1|p_ij=1;t_i;r_i|ΣC_i` (minimal NP-hard,
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
public import CSLibExt.Complexity.NPComplete.UnitFlowShopTransportationDelaysReleaseTimesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RobotFlowShopUnitReleaseTotalCompletion

open RobotFlowShopUnitWeightedTardiness (IsUnitRobotFlowShopSchedule)
open UnitFlowShopTransportationDelaysReleaseTimes

/-- Some single-robot schedule starts every job on `M₁` no earlier than its release date and
has total completion time `Σⱼ Cⱼ` at most `K`, where `Cⱼ = σ 1 j + 1`. -/
def RobotFlowShopUnitReleaseTotalCompletionFeasible
    (i : UnitFlowShopTransportationDelaysReleaseTimesInstance) : Prop :=
  ∃ σ : Fin 2 → Job i → ℕ, ∃ ρ : Job i → ℕ,
    IsUnitRobotFlowShopSchedule (delay i) σ ρ ∧
      (∀ j, releaseDate i j ≤ σ 0 j) ∧
      ∑ j, (σ 1 j + 1) ≤ i.2

open Classical in
/-- F2;R1|p_ij=1;t_i;r_i|ΣC_i as a decision problem over bitstrings. -/
noncomputable def robotFlowShopUnitReleaseTotalCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnitFlowShopTransportationDelaysReleaseTimesInstance) x with
  | some i => decide (WellFormed i ∧ RobotFlowShopUnitReleaseTotalCompletionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.RobotFlowShopUnitReleaseTotalCompletion
