/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import PhyslibExt.Circuits.NetworkStorageBalance

/-!
# DC motor energy bridge

## i. Overview

A DC motor with armature resistance `R`, inductance `L`, back-EMF
constant `ke`, torque constant `kt`, rotor inertia `J` and viscous
friction `b`. The terminal voltage `u`, armature current `i`, rotor
speed `ω` and load torque `τL` are functions of time. The load
torque sign convention is that a positive load torque opposes
positive rotation, so the load absorbs `τL * ω`. All
coefficients are in coherent SI units, in which the reciprocity
premise `ke = kt` may be imposed; it is not a consequence of algebra
alone. The electrical side is embedded in the network storage
carrier of `PhyslibExt.Circuits.NetworkStorageBalance`: a
four-branch series loop on three non-ground nodes, with ground
deleted, branch `0` the supply source, branch `1` the armature
resistance, branch `2` the armature inductance, and branch `3` the
back-EMF source. The electrical storage rate is derived by
instantiating the network storage balance of that carrier with
the motor partition, incidence matrix, node potentials and branch
laws; the rotor energy rate is computed directly, via the
derivative of a scaled square.

## ii. Key results

- `hasDerivAt_motorEnergy`: the DC motor energy identity, with
  derivative `u i - R i² - b ω² - τL ω + (kt - ke) i ω`.
- `hasDerivAt_motorEnergy_of_ke_eq_kt` and
  `deriv_motorEnergy_le_of_ke_eq_kt`: the reciprocal balance and its
  dissipation inequality when `ke = kt`.
- `deriv_motorNetwork_storedEnergy`: the network storage balance
  of the electrical embedding.
- `hasDerivAt_rotorKineticEnergy`: the rotor kinetic-energy
  derivative.
- `deriv_motorEnergy_ne_of_cross_ne_zero`: unequal coupling retains
  the residual cross term.

## iii. Table of contents

- A. Stored energy
- B. Electrical embedding
- C. Mechanical kinetic-energy derivative
- D. Electromechanical energy balance
- E. Validation: unequal coupling constants

## iv. References

- A. E. Fitzgerald, C. Kingsley Jr. and S. D. Umans, *Electric
  Machinery*, sixth edition, McGraw-Hill, 2003: DC machine
  voltage and torque equations, electromechanical energy
  conversion, and stored magnetic and kinetic energy.
-/

@[expose] public section

namespace PhyslibExt.Circuits.DCMotorEnergyBridge

open Matrix
open PhyslibExt.Circuits.NetworkStorageBalance

private lemma hasDerivAt_scaled_sq (c : ℝ) {f : ℝ → ℝ} {t : ℝ}
    (hf : DifferentiableAt ℝ f t) :
    HasDerivAt (fun s => c * f s ^ 2 / 2) (c * f t * deriv f t) t := by
  have hmul := hf.hasDerivAt.fun_mul hf.hasDerivAt
  have hcm : HasDerivAt (fun y => c * (f y * f y))
      (c * (deriv f t * f t + f t * deriv f t)) t :=
    hmul.const_mul c
  have hdiv : HasDerivAt (fun x => c * (f x * f x) / 2)
      (c * (deriv f t * f t + f t * deriv f t) / 2) t :=
    hcm.div_const 2
  have hval : c * (deriv f t * f t + f t * deriv f t) / 2 = c * f t * deriv f t := by
    ring
  rw [hval] at hdiv
  have hfun : (fun x => c * (f x * f x) / 2) = (fun s => c * f s ^ 2 / 2) := by
    funext x
    ring
  rw [hfun] at hdiv
  exact hdiv

/-! ## A. Stored energy -/

/-- Stored energy of a DC motor: armature magnetic energy `L i² / 2` plus rotor kinetic energy
`J ω² / 2`. -/
noncomputable def motorEnergy (L J i ω : ℝ) : ℝ :=
  L * i ^ 2 / 2 + J * ω ^ 2 / 2

/-- The motor stored energy is nonnegative for nonnegative inductance and inertia. -/
lemma motorEnergy_nonneg {L J : ℝ} (hL : 0 ≤ L) (hJ : 0 ≤ J) (i ω : ℝ) :
    0 ≤ motorEnergy L J i ω := by
  unfold motorEnergy
  positivity

/-! ## B. Electrical embedding -/

/-- Ground-deleted, head-positive incidence matrix of the series motor loop. Nodes: `0` supply
terminal, `1` internal resistance/inductance junction, `2` inductance/back-EMF junction.
Branches (head, tail): `0` supply source (ground, node `0`), `1` armature resistance (node `0`,
node `1`), `2` armature inductance (node `1`, node `2`), `3` back-EMF source (node `2`,
ground). -/
def motorIncidence : Matrix (Fin 3) (Fin 4) ℝ :=
  !![-1, 1, 0, 0; 0, -1, 1, 0; 0, 0, -1, 1]

/-- Node potentials of the motor loop for terminal voltage `u`, resistance `R`, current `i`,
back-EMF constant `ke` and speed `ω`: `u` at the supply terminal, `u - R i` at the internal node,
`ke ω` at the back-EMF terminal (ground is `0`). -/
def motorPotentials (u R i ke ω : ℝ) : Fin 3 → ℝ :=
  ![u, u - R * i, ke * ω]

/-- The motor loop branches form a branch partition: resistance `{1}`, inductance `{2}`, no
capacitor, sources `{0, 3}`. -/
lemma motor_isBranchPartition : IsBranchPartition 4 {1} {2} ∅ {0, 3} := by
  unfold IsBranchPartition
  decide

/-- KVL branch voltages of the motor loop: supply branch `-u`, resistance `R i`, inductance
`u - R i - ke ω`, back-EMF `ke ω`. -/
lemma motorIncidence_transpose_mulVec (u R i ke ω : ℝ) :
    motorIncidenceᵀ *ᵥ motorPotentials u R i ke ω = ![-u, R * i, u - R * i - ke * ω, ke * ω] := by
  ext e
  fin_cases e <;> simp [motorIncidence, motorPotentials, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three, Matrix.transpose_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]
  ring

/-- KCL with zero node injection: the same current `i` flows in every branch of the loop, in
particular in both the resistance and inductance branches. -/
lemma motorIncidence_mulVec_const (i : ℝ) : motorIncidence *ᵥ (fun _ => i) = 0 := by
  ext n
  fin_cases n <;> simp [motorIncidence, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]

/-- Source absorbed power of the loop: the supply delivers `u i` (absorbs `-(u i)`) and the
back-EMF source absorbs `ke ω i`. -/
lemma motor_sourceAbsorbedPower (u R i ke ω : ℝ) :
    sourceAbsorbedPower 4 {0, 3} (motorIncidenceᵀ *ᵥ motorPotentials u R i ke ω) (fun _ => i) =
      -(u * i) + ke * ω * i := by
  rw [motorIncidence_transpose_mulVec]
  unfold sourceAbsorbedPower
  rw [Finset.sum_pair (show (0 : Fin 4) ≠ 3 by decide)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]
  ring

/-- Resistive loss of the loop is `R i²`. -/
lemma motor_resistiveLoss (R i : ℝ) :
    resistiveLoss 4 {1} (fun _ => R) (fun _ => i) = R * i ^ 2 := by
  unfold resistiveLoss
  rw [Finset.sum_singleton]

/-- Network stored energy of the loop is the armature energy `L i² / 2`. -/
lemma motor_storedEnergy (Cval : Fin 4 → ℝ) (L : ℝ) (v : Fin 4 → ℝ) (i : ℝ) :
    storedEnergy 4 ∅ {2} Cval (fun _ => L) v (fun _ => i) = L * i ^ 2 / 2 := by
  unfold storedEnergy
  rw [Finset.sum_empty, Finset.sum_singleton, zero_add]

/-- The inductance branch law `v₂ = L i'` holds iff the armature equation
`u = R i + L i' + ke ω` holds. -/
lemma motor_inductor_law_iff (u R L i di ke ω : ℝ) :
    (motorIncidenceᵀ *ᵥ motorPotentials u R i ke ω) 2 = L * di ↔
      u = R * i + L * di + ke * ω := by
  rw [motorIncidence_transpose_mulVec]
  have h2 : (![-u, R * i, u - R * i - ke * ω, ke * ω] : Fin 4 → ℝ) 2 = u - R * i - ke * ω := rfl
  rw [h2]
  constructor <;> intro h <;> linarith

/-- **Electrical network storage balance of the embedding.** Under the armature equation at `t`,
with `L > 0`, `R ≥ 0` and `i` differentiable at `t`, the network stored energy of the motor loop
changes at rate `u i - R i² - ke ω i`: supplied power minus resistive loss minus the power
absorbed by the back-EMF source. -/
theorem deriv_motorNetwork_storedEnergy {R L ke : ℝ} (hR : 0 ≤ R) (hL : 0 < L)
    (Cval : Fin 4 → ℝ) {u i ω : ℝ → ℝ} {t : ℝ} (hi : DifferentiableAt ℝ i t)
    (helec : u t = R * i t + L * deriv i t + ke * ω t) :
    deriv (fun s => storedEnergy 4 ∅ {2} Cval (fun _ => L)
        (motorIncidenceᵀ *ᵥ motorPotentials (u s) R (i s) ke (ω s)) (fun _ => i s)) t =
      u t * i t - R * i t ^ 2 - ke * ω t * i t := by
  have hRlaw : ∀ e ∈ ({1} : Finset (Fin 4)),
      (motorIncidenceᵀ *ᵥ motorPotentials (u t) R (i t) ke (ω t)) e =
        (fun _ => R) e * (fun _ => i t) e := by
    intro e he
    have he1 : e = 1 := by simpa using he
    subst he1
    rw [motorIncidence_transpose_mulVec]
    simp
  have hLlaw : ∀ e ∈ ({2} : Finset (Fin 4)),
      (motorIncidenceᵀ *ᵥ motorPotentials (u t) R (i t) ke (ω t)) e =
        (fun _ => L) e * deriv (fun s => (fun _ => i s) e) t := by
    intro e he
    have he2 : e = 2 := by simpa using he
    subst he2
    rw [motorIncidence_transpose_mulVec]
    have h2 : (![-u t, R * i t, u t - R * i t - ke * ω t, ke * ω t] : Fin 4 → ℝ) 2 =
        u t - R * i t - ke * ω t := rfl
    rw [h2]
    have hder : (fun s => (fun _ => i s) (2 : Fin 4)) = i := rfl
    rw [hder]
    linarith
  have hbal := network_storage_deriv_eq_supplied_minus_losses 3 4 motorIncidence
    {1} {2} ∅ {0, 3} motor_isBranchPartition (fun _ => R) (fun _ => L) Cval
    (by intro e _; exact hR) (by intro e _; exact hL)
    (by intro e he; simp at he)
    (fun s => motorPotentials (u s) R (i s) ke (ω s)) (fun _ => 0)
    (fun s => motorIncidenceᵀ *ᵥ motorPotentials (u s) R (i s) ke (ω s))
    (fun s _ => i s) t rfl (motorIncidence_mulVec_const (i t)) hRlaw
    (by intro e he; simp at he) hLlaw (by intro e he; simp at he)
    (by intro e _; exact hi)
  rw [hbal, motor_sourceAbsorbedPower, motor_resistiveLoss]
  simp only [dotProduct, Finset.sum_const_zero, Pi.zero_apply, mul_zero]
  ring

/-! ## C. Mechanical kinetic-energy derivative -/

/-- **Rotor kinetic-energy derivative.** If `J ω' = kt i - b ω - τL` at `t` and `ω` is
differentiable at `t`, then `J ω² / 2` has derivative `kt i ω - b ω² - τL ω` at `t`. -/
theorem hasDerivAt_rotorKineticEnergy {J kt b : ℝ} {i ω τL : ℝ → ℝ} {t : ℝ}
    (hω : DifferentiableAt ℝ ω t) (hmech : J * deriv ω t = kt * i t - b * ω t - τL t) :
    HasDerivAt (fun s => J * ω s ^ 2 / 2) (kt * i t * ω t - b * ω t ^ 2 - τL t * ω t) t := by
  have h := hasDerivAt_scaled_sq J hω
  have hval : J * ω t * deriv ω t = kt * i t * ω t - b * ω t ^ 2 - τL t * ω t := by
    have h2 := congrArg (fun x => x * ω t) hmech
    linarith
  rw [hval] at h
  exact h

/-! ## D. Electromechanical energy balance -/

/-- **DC motor energy identity.** If `i` and `ω` are differentiable at `t` and satisfy the
armature equation `u = R i + L i' + ke ω` and the rotor equation `J ω' = kt i - b ω - τL` at `t`,
the stored energy `E = L i²/2 + J ω²/2` has derivative
`u i - R i² - b ω² - τL ω + (kt - ke) i ω` at `t`. No sign condition on the parameters is used. -/
theorem hasDerivAt_motorEnergy {R L J b ke kt : ℝ} {u i ω τL : ℝ → ℝ} {t : ℝ}
    (hi : DifferentiableAt ℝ i t) (hω : DifferentiableAt ℝ ω t)
    (helec : u t = R * i t + L * deriv i t + ke * ω t)
    (hmech : J * deriv ω t = kt * i t - b * ω t - τL t) :
    HasDerivAt (fun s => motorEnergy L J (i s) (ω s))
      (u t * i t - R * i t ^ 2 - b * ω t ^ 2 - τL t * ω t + (kt - ke) * i t * ω t) t := by
  have h := (hasDerivAt_scaled_sq L hi).fun_add (hasDerivAt_scaled_sq J hω)
  have hE : HasDerivAt (fun s => motorEnergy L J (i s) (ω s))
      (L * i t * deriv i t + J * ω t * deriv ω t) t := h
  have hval : L * i t * deriv i t + J * ω t * deriv ω t =
      u t * i t - R * i t ^ 2 - b * ω t ^ 2 - τL t * ω t + (kt - ke) * i t * ω t := by
    have h1 := congrArg (fun x => x * i t) helec
    have h2 := congrArg (fun x => x * ω t) hmech
    linarith
  rw [hval] at hE
  exact hE

/-- **Reciprocal coupling.** Under the motor equations and the coherent-unit reciprocity premise
`ke = kt`, `E' = u i - R i² - b ω² - τL ω`. -/
theorem hasDerivAt_motorEnergy_of_ke_eq_kt {R L J b ke kt : ℝ} (hk : ke = kt)
    {u i ω τL : ℝ → ℝ} {t : ℝ}
    (hi : DifferentiableAt ℝ i t) (hω : DifferentiableAt ℝ ω t)
    (helec : u t = R * i t + L * deriv i t + ke * ω t)
    (hmech : J * deriv ω t = kt * i t - b * ω t - τL t) :
    HasDerivAt (fun s => motorEnergy L J (i s) (ω s))
      (u t * i t - R * i t ^ 2 - b * ω t ^ 2 - τL t * ω t) t := by
  have h := hasDerivAt_motorEnergy hi hω helec hmech
  have hval : u t * i t - R * i t ^ 2 - b * ω t ^ 2 - τL t * ω t + (kt - ke) * i t * ω t =
      u t * i t - R * i t ^ 2 - b * ω t ^ 2 - τL t * ω t := by
    rw [hk]
    ring
  rw [hval] at h
  exact h

/-- **Dissipation inequality.** Under the motor equations, `R, b ≥ 0` and `ke = kt`, the stored
energy grows at most at the supplied electrical power minus the power delivered to the load. -/
theorem deriv_motorEnergy_le_of_ke_eq_kt {R L J b ke kt : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hk : ke = kt) {u i ω τL : ℝ → ℝ} {t : ℝ}
    (hi : DifferentiableAt ℝ i t) (hω : DifferentiableAt ℝ ω t)
    (helec : u t = R * i t + L * deriv i t + ke * ω t)
    (hmech : J * deriv ω t = kt * i t - b * ω t - τL t) :
    deriv (fun s => motorEnergy L J (i s) (ω s)) t ≤ u t * i t - τL t * ω t := by
  have h := hasDerivAt_motorEnergy_of_ke_eq_kt hk hi hω helec hmech
  rw [h.deriv]
  have hR2 : 0 ≤ R * i t ^ 2 := mul_nonneg hR (sq_nonneg _)
  have hb2 : 0 ≤ b * ω t ^ 2 := mul_nonneg hb (sq_nonneg _)
  linarith

/-! ## E. Validation: unequal coupling constants -/

/-- **Unequal coupling retains the cross term.** Under the motor equations, if
`(kt - ke) i ω ≠ 0` at `t`, the stored-energy derivative differs from the reciprocal balance
`u i - R i² - b ω² - τL ω`. -/
theorem deriv_motorEnergy_ne_of_cross_ne_zero {R L J b ke kt : ℝ} {u i ω τL : ℝ → ℝ} {t : ℝ}
    (hi : DifferentiableAt ℝ i t)
    (hω : DifferentiableAt ℝ ω t) (helec : u t = R * i t + L * deriv i t + ke * ω t)
    (hmech : J * deriv ω t = kt * i t - b * ω t - τL t)
    (hcross : (kt - ke) * i t * ω t ≠ 0) :
    deriv (fun s => motorEnergy L J (i s) (ω s)) t ≠
      u t * i t - R * i t ^ 2 - b * ω t ^ 2 - τL t * ω t := by
  have h := hasDerivAt_motorEnergy hi hω helec hmech
  rw [h.deriv]
  intro hcon
  apply hcross
  linarith

/-- **Concrete `ke ≠ kt` fixture.** `R = L = J = b = ke = 1`, `kt = 2`, constant `i = ω = 1`,
`u = 2`, `τL = 1`: both motor equations hold at every `t` (first two conjuncts), `E` is constant
so `E' = 0`, the reciprocal balance `u i - R i² - b ω² - τL ω` evaluates to `-1 ≠ 0`, and the
headline right-hand side, with residual `(kt - ke) i ω = 1`, evaluates to `0`. -/
lemma unequalCoupling_fixture (t : ℝ) :
    (2 : ℝ) = 1 * 1 + 1 * deriv (fun _ : ℝ => (1 : ℝ)) t + 1 * 1 ∧
      (1 : ℝ) * deriv (fun _ : ℝ => (1 : ℝ)) t = 2 * 1 - 1 * 1 - 1 ∧
      deriv (fun _ : ℝ => motorEnergy 1 1 1 1) t = 0 ∧
      (2 : ℝ) * 1 - 1 * 1 ^ 2 - 1 * 1 ^ 2 - 1 * 1 = -1 ∧
      (0 : ℝ) = 2 * 1 - 1 * 1 ^ 2 - 1 * 1 ^ 2 - 1 * 1 + (2 - 1) * 1 * 1 := by
  have hd : deriv (fun _ : ℝ => (1 : ℝ)) t = 0 := deriv_const t 1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hd]
    norm_num
  · rw [hd]
    norm_num
  · exact deriv_const t (motorEnergy 1 1 1 1)
  · norm_num
  · norm_num

end PhyslibExt.Circuits.DCMotorEnergyBridge
