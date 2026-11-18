/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.DCMotorEnergyBridge
import Mathlib.Tactic.NormNum

@[expose] public section

open Matrix
open PhyslibExt.Circuits.DCMotorEnergyBridge
open PhyslibExt.Circuits.NetworkStorageBalance

namespace PhyslibExtTest.Circuits.DCMotorEnergyBridge

/-- Motor incidence actions: KVL branch voltages and KCL with the
same current in every branch, at `u = 10`, `R = 2`, `i = 3`,
`ke = 1` and `ω = 4`. -/
example : motorIncidenceᵀ *ᵥ motorPotentials 10 2 3 1 4
    = ![-10, 6, 0, 4] := by
  rw [motorIncidence_transpose_mulVec]
  ext e
  fin_cases e <;> norm_num

example : motorIncidence *ᵥ (fun _ => (5 : ℝ)) = 0 :=
  motorIncidence_mulVec_const 5

example : IsBranchPartition 4 {1} {2} ∅ {0, 3} :=
  motor_isBranchPartition

/-- Chained incidence and potentials test: the branch voltages from
the incidence transpose are fed into the source and resistive
quantities, and the same current satisfies the node-injection
identity. Perturbing the incidence matrix or the potentials changes
the branch-voltage components and breaks this test. -/
example : (motorIncidenceᵀ *ᵥ motorPotentials 10 2 3 1 4) 0 = -10 ∧
    (motorIncidenceᵀ *ᵥ motorPotentials 10 2 3 1 4) 1 = 6 ∧
    (motorIncidenceᵀ *ᵥ motorPotentials 10 2 3 1 4) 2 = 0 ∧
    (motorIncidenceᵀ *ᵥ motorPotentials 10 2 3 1 4) 3 = 4 ∧
    motorIncidence *ᵥ (fun _ => (3 : ℝ)) = 0 ∧
    sourceAbsorbedPower 4 {0, 3}
        (motorIncidenceᵀ *ᵥ motorPotentials 10 2 3 1 4) (fun _ => 3) +
      resistiveLoss 4 {1} (fun _ => (2 : ℝ)) (fun _ => 3) = 0 := by
  have hv := motorIncidence_transpose_mulVec 10 2 3 1 4
  refine ⟨?_, ?_, ?_, ?_, motorIncidence_mulVec_const 3, ?_⟩
  · have h := congrFun hv 0
    rw [h]
    simp
  · have h := congrFun hv 1
    rw [h]
    norm_num
  · have h := congrFun hv 2
    rw [h]
    norm_num
  · have h := congrFun hv 3
    rw [h]
    simp
  · rw [motor_sourceAbsorbedPower, motor_resistiveLoss]
    norm_num

/-- The network storage derivative on `i s = s`, `ω s = s` at
`t = 1`, with `R = 1`, `L = 2`, `ke = 1` and constant voltage `4`:
the rate is `4 * 1 - 1 * 1 ^ 2 - 1 * 1 * 1 = 2`. -/
example : deriv (fun s => storedEnergy 4 ∅ {2} (fun _ => (7 : ℝ))
    (fun _ => 2) (motorIncidenceᵀ *ᵥ motorPotentials 4 1 s 1 s)
    (fun _ => s)) 1 = 2 := by
  have h := deriv_motorNetwork_storedEnergy (R := 1) (L := 2) (ke := 1)
    (by norm_num) (by norm_num) (fun _ => (7 : ℝ)) (u := fun _ => 4)
    (i := fun s => s) (ω := fun s => s) (t := 1) differentiableAt_id
    (by norm_num [deriv_id''])
  convert h using 1
  norm_num

/-- Source, resistive and storage quantities of the embedding at
the same concrete values. -/
example : sourceAbsorbedPower 4 {0, 3}
    (motorIncidenceᵀ *ᵥ motorPotentials 10 2 3 1 4) (fun _ => 3) = -18 := by
  rw [motor_sourceAbsorbedPower]
  norm_num

example : resistiveLoss 4 {1} (fun _ => (2 : ℝ)) (fun _ => 3) = 18 := by
  rw [motor_resistiveLoss]
  norm_num

example : storedEnergy 4 ∅ {2} (fun _ => (7 : ℝ)) (fun _ => 2)
    (fun _ => (0 : ℝ)) (fun _ => 3) = 9 := by
  rw [motor_storedEnergy]
  norm_num

/-- Stored energy: `motorEnergy 2 4 3 1 = 2 * 3 ^ 2 / 2 + 4 / 2 = 11`,
and its nonnegativity. -/
example : motorEnergy 2 4 3 1 = 11 := by
  norm_num [motorEnergy]

example : 0 ≤ motorEnergy 2 4 3 1 :=
  motorEnergy_nonneg (by norm_num) (by norm_num) 3 1

/-- The inductor branch law at concrete values is equivalent to
the armature equation `10 = 2 * 3 + 2 * 0 + 1 * 4`. -/
example : (motorIncidenceᵀ *ᵥ motorPotentials 10 2 3 1 4) 2 = 2 * 0 ↔
    (10 : ℝ) = 2 * 3 + 2 * 0 + 1 * 4 :=
  motor_inductor_law_iff 10 2 2 3 0 1 4

/-- The general energy identity, through `hasDerivAt_motorEnergy`,
on `i s = s` and `ω s = s` at `t = 1`, with `R = 1`, `L = 2`,
`J = 3`, `b = 1`, `ke = 1`, `kt = 2`, constant voltage `4` and
constant load torque `-2`: the derivative includes the residual
cross term `(2 - 1) * 1 * 1`. -/
example : HasDerivAt (fun s => motorEnergy 2 3 s s) 5 1 := by
  have h := hasDerivAt_motorEnergy (R := 1) (L := 2) (J := 3) (b := 1)
    (ke := 1) (kt := 2) (u := fun _ => 4) (i := fun s => s)
    (ω := fun s => s) (τL := fun _ => -2) (t := 1)
    differentiableAt_id differentiableAt_id (by norm_num [deriv_id''])
    (by norm_num [deriv_id''])
  convert h using 1
  norm_num

/-- The equal-coupling energy derivative identity on the concrete
trajectories `i s = s` and `ω s = s` at `t = 1`, with
`R = 1`, `L = 2`, `J = 3`, `b = 1`, `ke = kt = 2`, constant
terminal voltage `5` and constant load torque `-2`. Both motor
equations hold at `t = 1`, and the stored energy has derivative
`5 * 1 - 1 - 1 - (-2) * 1 = 5`. -/
example : HasDerivAt (fun s => motorEnergy 2 3 s s) 5 1 := by
  have h := hasDerivAt_motorEnergy_of_ke_eq_kt (R := 1) (L := 2)
    (J := 3) (b := 1) (ke := 2) (kt := 2) (u := fun _ => 5)
    (i := fun s => s) (ω := fun s => s) (τL := fun _ => -2) (t := 1)
    rfl differentiableAt_id differentiableAt_id (by norm_num [deriv_id''])
    (by norm_num [deriv_id''])
  convert h using 1
  norm_num

/-- The unequal-coupling fixture at `t = 0`: its motor equations,
zero stored-energy derivative, and reciprocal balance `-1`. -/
example : (2 : ℝ) = 1 * 1 + 1 * deriv (fun _ : ℝ => (1 : ℝ)) 0 + 1 * 1 ∧
    deriv (fun _ : ℝ => motorEnergy 1 1 1 1) 0 = 0 ∧
    (2 : ℝ) * 1 - 1 * 1 ^ 2 - 1 * 1 ^ 2 - 1 * 1 = -1 := by
  obtain ⟨h1, -, h3, h4, -⟩ := unequalCoupling_fixture 0
  exact ⟨h1, h3, h4⟩

end PhyslibExtTest.Circuits.DCMotorEnergyBridge
