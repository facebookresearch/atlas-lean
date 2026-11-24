/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import PhyslibExt.Mechanics.OrbitalPerturbations
public import PhyslibExt.Mechanics.RigidMotionPorts
import PhyslibExt.EarthScience.PointMassGradient
import PhyslibExt.EarthScience.NewtonianEnergy
import PhyslibExt.Mechanics.HarmonicMechanics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Particle force and power ports on actual trajectories, and the planar rigid-body port

A particle of constant mass `m > 0` in a real inner product space `E` under a constant force
`F` follows the actual trajectory `x t = x₀ + t • v₀ + (t ^ 2 / (2 * m)) • F` with velocity
`v t = v₀ + (t / m) • F`. On it the force port agrees with Newton's law, the power port is the
kinetic-energy derivative, and integrating gives the work and impulse identities with both
endpoint terms. A spring example reuses the existing harmonic-oscillator trajectory, and
inverse-square work is stated only along paths that avoid the centre. A planar rigid body adds a
torque port: its kinetic energy `m ‖V‖² / 2 + J θ'² / 2` has the rate `⟪F, V⟫ + τ θ'`, linked to
Physlib's kinetic-energy split and to Euler's equations.

## i. Overview

The trajectory starts at `x₀` with velocity `v₀` and satisfies `m • x'' = F`. The kinetic
energy `m * ‖v t‖ ^ 2 / 2` has derivative `⟪F, v t⟫`, an instance of
`EarthScience.hasDerivAt_kinetic_energy`; the fundamental theorem of calculus turns this into
work `= K(t₁) - K(t₀) = ⟪F, x t₁ - x t₀⟫`, and the momentum gives the impulse
`∫ F = m • v t₁ - m • v t₀`. The spring force `-k x` on the trajectory `A * cos (ω t)`,
`ω = √(k / m)`, from `PhyslibExt.Mechanics.HarmonicMechanics.oscillator_explicit_solution` has
power `⟪-k x, v⟫`, and its work is the change of kinetic energy and the decrease of the
potential `k x ^ 2 / 2 + C` for every constant `C`. The inverse-square force is
`-OrbitalPerturbations.inverseSquareField μ`, minus the gradient of the potential `-μ / ‖y‖`
away from the centre; that potential has no limit at the centre, so the work identity carries a
collision-exclusion hypothesis. Mass is
constant throughout; nothing here applies to variable-mass motion. Forces, initial data and
time intervals are model inputs.

A rigid body of mass `m > 0` moves in a plane and turns about a fixed axis normal to the plane,
with constant moment of inertia `J > 0` about the axis through its centre of mass; its state is the
centre-of-mass velocity `V` (`C¹`) and the actual rotation angle `θ` (`C²`). The balances
`m V' = F` and `J θ'' = τ` are stated model laws: the torque balance is not a theorem of the mass
functional alone. Under them the kinetic energy `m ‖V‖² / 2 + J θ'² / 2` has the rate
`⟪F, V⟫ + τ θ'`, the power at the force port plus the power at the torque port, and a wrong torque
sign breaks the balance. For a Physlib rigid motion of positive mass with the body frame centered
at the centre of mass and body angular velocity `(0, 0, ω)` (rotation about the third body axis),
Physlib's kinetic-energy split is `m ‖V‖² / 2 + J ω² / 2` with `J = (I_B)₃₃`, and the declared
torque balance is the axial component `J ω' = (Rᵀ τ_I)₃` of the rotational balance law
`dL_COM/dt = τ_I` of `PhyslibExt.Mechanics.RigidMotionPorts`. Variable inertia, constraint torques
for axes that are not principal and attitude reconstruction are not treated.

## ii. Key results

- `constForce_actual_trajectory`: initial data `x₀`, `v₀` and `m • x'' = F`.
- `constForce_power_port`: the kinetic energy has derivative `⟪F, v t⟫`.
- `constForce_work`, `constForce_impulse`: work and impulse identities over `[t₀, t₁]`.
- `spring_power_port`, `spring_work`: the spring example on the oscillator trajectory.
- `inverseSquare_work`: inverse-square work along a path that avoids the centre.
- `hasGradientAt_inverseSquarePotential`: away from the centre the inverse-square field is the
  gradient of `-μ / ‖y‖`.
- `inverseSquarePotential_not_continuousAt_zero`: the inverse-square potential is not
  continuous at the centre.
- `planarRigid_power_port`, `planarRigid_power_port_neg_torque`: the planar rigid-body power
  port, and the failure of the wrong torque sign.
- `kineticEnergy_eq_planar`, `axial_torque_balance`: Physlib's kinetic-energy split and the
  rotational balance law for a rigid motion turning about its third body axis.

## iii. Table of contents

- A. Model: the constant-force trajectory
- B. Force port: the trajectory is actual
- C. Power port, work and impulse
- D. Spring example on the existing oscillator trajectory
- E. Inverse-square work needs collision exclusion
- F. Planar rigid-body power port

## iv. References

- R. C. Hibbeler, *Engineering Mechanics: Dynamics*, 14th edition, chapters 14-15 (work and
  energy, impulse and momentum of a particle) and 17-18 (planar kinetics of a rigid body; its
  work and energy, `T = m v_G² / 2 + I_G ω² / 2`).
- L. D. Landau and E. M. Lifshitz, *Mechanics*, Sections 32 and 36 (the kinetic energy of a rigid
  body; Euler's equations).
- H. Goldstein, *Classical Mechanics*, central-force chapter (inverse-square potential).
- `PhyslibExt.EarthScience.NewtonianEnergy` and `PhyslibExt.Mechanics.HarmonicMechanics`: the
  kinetic-energy derivative and the oscillator trajectory reused here.
- `PhyslibExt.Mechanics.OrbitalPerturbations` and `PhyslibExt.EarthScience.PointMassGradient`:
  the inverse-square field and the point-mass gradient reused here.
- Physlib's `RigidBodyMotion.kineticEnergy_eq_translational_add_bodyAngularVelocity` and the
  rotational balance law of `PhyslibExt.Mechanics.RigidMotionPorts`: the kinetic-energy split
  and Euler's equations reused here.
-/

@[expose] public section

namespace PhyslibExt.Mechanics.PowerPorts

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## A. Model: the constant-force trajectory -/

/-- Position on the actual trajectory of a particle of mass `m` under the constant force `F`,
started at `x₀` with velocity `v₀`. -/
noncomputable def constForcePosition (m : ℝ) (x₀ v₀ F : E) (t : ℝ) : E :=
  x₀ + t • v₀ + (t ^ 2 / (2 * m)) • F

/-- Velocity on that trajectory. -/
noncomputable def constForceVelocity (m : ℝ) (v₀ F : E) (t : ℝ) : E :=
  v₀ + (t / m) • F

/-! ## B. Force port: the trajectory is actual -/

/-- The position has derivative the velocity. -/
lemma constForcePosition_hasDerivAt (m : ℝ) (x₀ v₀ F : E) (t : ℝ) :
    HasDerivAt (constForcePosition m x₀ v₀ F) (constForceVelocity m v₀ F t) t := by
  unfold constForcePosition constForceVelocity
  have h1 : HasDerivAt (fun s : ℝ => s • v₀) v₀ t := by
    have h := (hasDerivAt_id t).smul_const v₀
    simpa using h
  have hpow : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
    have h := hasDerivAt_pow 2 t
    simpa using h
  have hscal : HasDerivAt (fun s : ℝ => s ^ 2 / (2 * m)) (t / m) t := by
    have h := hpow.div_const (2 * m)
    have heq : (2 * t) / (2 * m) = t / m := by
      by_cases hm0 : m = 0
      · simp [hm0]
      · field_simp
    rwa [heq] at h
  have h2 : HasDerivAt (fun s : ℝ => (s ^ 2 / (2 * m)) • F) ((t / m) • F) t :=
    hscal.smul_const F
  have h0 : HasDerivAt (fun _ : ℝ => x₀) (0 : E) t := hasDerivAt_const t x₀
  have h := (h0.add h1).add h2
  have hfun : (fun s : ℝ => x₀ + s • v₀ + (s ^ 2 / (2 * m)) • F) =
      (((fun _ : ℝ => x₀) + (fun s : ℝ => s • v₀)) + (fun s : ℝ => (s ^ 2 / (2 * m)) • F)) := by
    ext s
    simp [Pi.add_apply]
  rw [hfun]
  simpa using h

/-- The velocity has derivative the acceleration `m⁻¹ • F`. -/
lemma constForceVelocity_hasDerivAt (m : ℝ) (v₀ F : E) (t : ℝ) :
    HasDerivAt (constForceVelocity m v₀ F) (m⁻¹ • F) t := by
  unfold constForceVelocity
  have hscal : HasDerivAt (fun s : ℝ => s / m) (m⁻¹) t := by
    have h := (hasDerivAt_id t).div_const m
    rwa [one_div] at h
  have h2 : HasDerivAt (fun s : ℝ => (s / m) • F) (m⁻¹ • F) t :=
    hscal.smul_const F
  have h0 : HasDerivAt (fun _ : ℝ => v₀) (0 : E) t := hasDerivAt_const t v₀
  have h := h0.add h2
  have hfun : (fun s : ℝ => v₀ + (s / m) • F) =
      ((fun _ : ℝ => v₀) + (fun s : ℝ => (s / m) • F)) := by
    ext s
    simp [Pi.add_apply]
  rw [hfun]
  simpa using h

/-- The force port agrees with Newton's law: the trajectory starts at `x₀` with velocity `v₀`
and satisfies `m • x'' = F` at every time. -/
lemma constForce_actual_trajectory {m : ℝ} (hm : 0 < m) (x₀ v₀ F : E) :
    constForcePosition m x₀ v₀ F 0 = x₀ ∧ deriv (constForcePosition m x₀ v₀ F) 0 = v₀ ∧
      ∀ t, m • deriv (deriv (constForcePosition m x₀ v₀ F)) t = F := by
  have hm0 : m ≠ 0 := ne_of_gt hm
  have hx0 : constForcePosition m x₀ v₀ F 0 = x₀ := by
    simp [constForcePosition]
  have hderiv0 : deriv (constForcePosition m x₀ v₀ F) 0 = v₀ := by
    have h0 := (constForcePosition_hasDerivAt m x₀ v₀ F 0).deriv
    rw [h0]
    simp [constForceVelocity]
  have hderiv1 : deriv (constForcePosition m x₀ v₀ F) = constForceVelocity m v₀ F := by
    ext t
    exact (constForcePosition_hasDerivAt m x₀ v₀ F t).deriv
  have hnewton : ∀ t, m • deriv (deriv (constForcePosition m x₀ v₀ F)) t = F := by
    intro t
    have h2 : deriv (deriv (constForcePosition m x₀ v₀ F)) t = m⁻¹ • F := by
      rw [hderiv1]
      exact (constForceVelocity_hasDerivAt m v₀ F t).deriv
    rw [h2, ← smul_assoc, smul_eq_mul, mul_inv_cancel₀ hm0, one_smul]
  exact ⟨hx0, hderiv0, hnewton⟩

/-! ## C. Power port, work and impulse -/

/-- Power port: on the actual trajectory the kinetic energy has derivative the power
`⟪F, v t⟫` delivered by the force. -/
lemma constForce_power_port {m : ℝ} (hm : 0 < m) (v₀ F : E) (t : ℝ) :
    HasDerivAt (fun s => m * ‖constForceVelocity m v₀ F s‖ ^ 2 / 2)
      (inner ℝ F (constForceVelocity m v₀ F t)) t := by
  have hm0 : m ≠ 0 := ne_of_gt hm
  have hv : HasDerivAt (constForceVelocity m v₀ F) (m⁻¹ • F) t :=
    constForceVelocity_hasDerivAt m v₀ F t
  have h := EarthScience.hasDerivAt_kinetic_energy (m := m) (v := constForceVelocity m v₀ F)
    (a := fun _ => m⁻¹ • F) hv
  have heq : m • (m⁻¹ • F) = F := by
    rw [← smul_assoc, smul_eq_mul, mul_inv_cancel₀ hm0, one_smul]
  rwa [heq] at h

/-- Work identity with both endpoint terms: the work of `F` over `[t₀, t₁]` is the change of
kinetic energy, and it is also `⟪F, x t₁ - x t₀⟫`. -/
lemma constForce_work {m : ℝ} (hm : 0 < m) (x₀ v₀ F : E) (t₀ t₁ : ℝ) :
    ∫ t in t₀..t₁, inner ℝ F (constForceVelocity m v₀ F t) =
        m * ‖constForceVelocity m v₀ F t₁‖ ^ 2 / 2 - m * ‖constForceVelocity m v₀ F t₀‖ ^ 2 / 2 ∧
      ∫ t in t₀..t₁, inner ℝ F (constForceVelocity m v₀ F t) =
        inner ℝ F (constForcePosition m x₀ v₀ F t₁ - constForcePosition m x₀ v₀ F t₀) := by
  have hderivK : ∀ s ∈ Set.uIcc t₀ t₁,
      HasDerivAt (fun s => m * ‖constForceVelocity m v₀ F s‖ ^ 2 / 2)
        (inner ℝ F (constForceVelocity m v₀ F s)) s :=
    fun s _ => constForce_power_port hm v₀ F s
  have hvc : Continuous (constForceVelocity m v₀ F) := by
    unfold constForceVelocity
    exact continuous_const.add ((continuous_id.div_const m).smul continuous_const)
  have hpow_cont : Continuous (fun s => inner ℝ F (constForceVelocity m v₀ F s)) :=
    continuous_const.inner hvc
  have hint : IntervalIntegrable (fun s => inner ℝ F (constForceVelocity m v₀ F s)) volume t₀ t₁ :=
    hpow_cont.intervalIntegrable t₀ t₁
  have hfirst := intervalIntegral.integral_eq_sub_of_hasDerivAt hderivK hint
  have hderivG : ∀ s ∈ Set.uIcc t₀ t₁,
      HasDerivAt (fun s => inner ℝ F (constForcePosition m x₀ v₀ F s))
        (inner ℝ F (constForceVelocity m v₀ F s)) s := by
    intro s _
    have h := (hasDerivAt_const s F).inner ℝ (constForcePosition_hasDerivAt m x₀ v₀ F s)
    simpa using h
  have hsecond_ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderivG hint
  have hsub : inner ℝ F (constForcePosition m x₀ v₀ F t₁) -
      inner ℝ F (constForcePosition m x₀ v₀ F t₀) =
      inner ℝ F (constForcePosition m x₀ v₀ F t₁ - constForcePosition m x₀ v₀ F t₀) := by
    rw [inner_sub_right]
  rw [hsub] at hsecond_ftc
  exact ⟨hfirst, hsecond_ftc⟩

/-- Impulse identity: the impulse of `F` over `[t₀, t₁]` is the change of momentum. -/
lemma constForce_impulse [CompleteSpace E] {m : ℝ} (hm : 0 < m) (v₀ F : E) (t₀ t₁ : ℝ) :
    ∫ _ in t₀..t₁, F = m • constForceVelocity m v₀ F t₁ - m • constForceVelocity m v₀ F t₀ := by
  have hm0 : m ≠ 0 := ne_of_gt hm
  have hderiv : ∀ s ∈ Set.uIcc t₀ t₁,
      HasDerivAt (fun s => m • constForceVelocity m v₀ F s) F s := by
    intro s _
    have hv := constForceVelocity_hasDerivAt m v₀ F s
    have h := hv.const_smul m
    have heq : m • (m⁻¹ • F) = F := by
      rw [← smul_assoc, smul_eq_mul, mul_inv_cancel₀ hm0, one_smul]
    rwa [heq] at h
  have hint : IntervalIntegrable (fun _ => F) volume t₀ t₁ := intervalIntegrable_const
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/-! ## D. Spring example on the existing oscillator trajectory -/

/-- Power port of the spring force `-k x` on the oscillator trajectory `x t = A * cos (ω t)`,
`v t = -A * ω * sin (ω t)`, `ω = √(k / m)`. -/
lemma spring_power_port {m k A ω : ℝ} (hm : 0 < m) (hk : 0 < k) (hω : ω = Real.sqrt (k / m))
    (t : ℝ) :
    HasDerivAt (fun s : ℝ => m * ‖-A * ω * Real.sin (ω * s)‖ ^ 2 / 2)
      (inner ℝ (-k * (A * Real.cos (ω * t))) (-A * ω * Real.sin (ω * t))) t := by
  have hm0 : m ≠ 0 := ne_of_gt hm
  obtain ⟨_, h2, _⟩ :=
    PhyslibExt.Mechanics.HarmonicMechanics.oscillator_explicit_solution m k A ω t hm hk hω
  have h := EarthScience.hasDerivAt_kinetic_energy (m := m)
    (v := fun s : ℝ => -A * ω * Real.sin (ω * s))
    (a := fun s : ℝ => -(k / m) * (A * Real.cos (ω * s))) h2
  have heq : m • (-(k / m) * (A * Real.cos (ω * t))) = -k * (A * Real.cos (ω * t)) := by
    rw [smul_eq_mul]
    field_simp
  rwa [heq] at h

/-- Spring work over `[t₀, t₁]`: the change of kinetic energy, and the decrease of the potential
`k x ^ 2 / 2 + C`, whatever the constant `C`. -/
lemma spring_work {m k A ω : ℝ} (hm : 0 < m) (hk : 0 < k) (hω : ω = Real.sqrt (k / m))
    (t₀ t₁ C : ℝ) :
    ∫ t in t₀..t₁, inner ℝ (-k * (A * Real.cos (ω * t))) (-A * ω * Real.sin (ω * t)) =
        m * ‖-A * ω * Real.sin (ω * t₁)‖ ^ 2 / 2 - m * ‖-A * ω * Real.sin (ω * t₀)‖ ^ 2 / 2 ∧
      ∫ t in t₀..t₁, inner ℝ (-k * (A * Real.cos (ω * t))) (-A * ω * Real.sin (ω * t)) =
        -((k * (A * Real.cos (ω * t₁)) ^ 2 / 2 + C) -
          (k * (A * Real.cos (ω * t₀)) ^ 2 / 2 + C)) := by
  have hderivK : ∀ s ∈ Set.uIcc t₀ t₁,
      HasDerivAt (fun s : ℝ => m * ‖-A * ω * Real.sin (ω * s)‖ ^ 2 / 2)
        (inner ℝ (-k * (A * Real.cos (ω * s))) (-A * ω * Real.sin (ω * s))) s :=
    fun s _ => spring_power_port hm hk hω s
  have hlin : Continuous fun t : ℝ => ω * t := continuous_id.const_mul ω
  have hcos : Continuous fun t : ℝ => A * Real.cos (ω * t) :=
    continuous_const.mul (Real.continuous_cos.comp hlin)
  have hsin : Continuous fun t : ℝ => -A * ω * Real.sin (ω * t) :=
    continuous_const.mul (Real.continuous_sin.comp hlin)
  have hf : Continuous fun t : ℝ => -k * (A * Real.cos (ω * t)) :=
    continuous_const.mul hcos
  have hpow_cont : Continuous fun t : ℝ =>
      inner ℝ (-k * (A * Real.cos (ω * t))) (-A * ω * Real.sin (ω * t)) :=
    hf.inner hsin
  have hint : IntervalIntegrable (fun t : ℝ =>
      inner ℝ (-k * (A * Real.cos (ω * t))) (-A * ω * Real.sin (ω * t))) volume t₀ t₁ :=
    hpow_cont.intervalIntegrable t₀ t₁
  have hfirst := intervalIntegral.integral_eq_sub_of_hasDerivAt hderivK hint
  have hE1 := (PhyslibExt.Mechanics.HarmonicMechanics.oscillator_explicit_solution
    m k A ω t₁ hm hk hω).2.2
  have hE0 := (PhyslibExt.Mechanics.HarmonicMechanics.oscillator_explicit_solution
    m k A ω t₀ hm hk hω).2.2
  unfold PhyslibExt.Mechanics.HarmonicMechanics.oscillatorEnergy at hE1 hE0
  have hnorm : ∀ y : ℝ, m * ‖y‖ ^ 2 / 2 = (1 / 2) * m * y ^ 2 := by
    intro y
    rw [Real.norm_eq_abs, sq_abs]
    ring
  have hsecond : ∫ t in t₀..t₁, inner ℝ (-k * (A * Real.cos (ω * t))) (-A * ω * Real.sin (ω * t)) =
      -((k * (A * Real.cos (ω * t₁)) ^ 2 / 2 + C) - (k * (A * Real.cos (ω * t₀)) ^ 2 / 2 + C)) := by
    rw [hfirst, hnorm, hnorm]
    linear_combination hE1 - hE0
  exact ⟨hfirst, hsecond⟩

/-! ## E. Inverse-square work needs collision exclusion -/

/-- Work of the inverse-square force `-OrbitalPerturbations.inverseSquareField μ y`
(`= -(μ / ‖y‖ ^ 3) • y`) along a path that never meets the centre on `[a, b]` equals the
decrease of the potential `-μ / ‖y‖`. -/
lemma inverseSquare_work {μ a b : ℝ} {γ γ' : ℝ → E}
    (hγ : ∀ t ∈ Set.uIcc a b, HasDerivAt γ (γ' t) t) (hcoll : ∀ t ∈ Set.uIcc a b, γ t ≠ 0)
    (hint : IntervalIntegrable
      (fun t => inner ℝ (-OrbitalPerturbations.inverseSquareField μ (γ t)) (γ' t)) volume a b) :
    ∫ t in a..b, inner ℝ (-OrbitalPerturbations.inverseSquareField μ (γ t)) (γ' t) =
      -(-μ / ‖γ b‖ - -μ / ‖γ a‖) := by
  have hfield : ∀ y : E, -OrbitalPerturbations.inverseSquareField μ y = -(μ / ‖y‖ ^ 3) • y :=
    fun y => by rw [OrbitalPerturbations.inverseSquareField, neg_smul]
  simp only [hfield] at hint ⊢
  have hnorm_ne : ∀ s ∈ Set.uIcc a b, ‖γ s‖ ≠ 0 :=
    fun s hs => norm_ne_zero_iff.mpr (hcoll s hs)
  have hderiv : ∀ s ∈ Set.uIcc a b,
      HasDerivAt (fun t => μ / ‖γ t‖) (inner ℝ (-(μ / ‖γ s‖ ^ 3) • γ s) (γ' s)) s := by
    intro s hs
    have hγs := hγ s hs
    have hne : ‖γ s‖ ≠ 0 := hnorm_ne s hs
    have hsq_ne : ‖γ s‖ ^ 2 ≠ 0 := pow_ne_zero 2 hne
    have h_norm_sq : HasDerivAt (fun t => ‖γ t‖ ^ 2) (2 * inner ℝ (γ s) (γ' s)) s :=
      hγs.norm_sq
    have h_sqrt : HasDerivAt (fun y => √(‖γ y‖ ^ 2))
        ((2 * inner ℝ (γ s) (γ' s)) / (2 * √(‖γ s‖ ^ 2))) s :=
      h_norm_sq.sqrt hsq_ne
    have hsqrt_eq : ∀ y : ℝ, √(‖γ y‖ ^ 2) = ‖γ y‖ :=
      fun y => Real.sqrt_sq (norm_nonneg _)
    have hfun_sqrt : (fun y : ℝ => √(‖γ y‖ ^ 2)) = (fun y : ℝ => ‖γ y‖) := by
      ext y
      exact hsqrt_eq y
    rw [hfun_sqrt, hsqrt_eq s] at h_sqrt
    have h_div := (hasDerivAt_const s μ).div h_sqrt hne
    have hfun_div : (fun t : ℝ => μ / ‖γ t‖) =
        ((fun _ : ℝ => μ) / (fun t : ℝ => ‖γ t‖)) := by
      ext t
      simp [Pi.div_apply]
    rw [hfun_div]
    have hderiv_eq : ((0 * ‖γ s‖ - μ * ((2 * inner ℝ (γ s) (γ' s)) / (2 * ‖γ s‖))) / ‖γ s‖ ^ 2) =
        inner ℝ (-(μ / ‖γ s‖ ^ 3) • γ s) (γ' s) := by
      rw [real_inner_smul_left]
      field_simp
      ring
    rwa [hderiv_eq] at h_div
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hfinal : μ / ‖γ b‖ - μ / ‖γ a‖ = -(-μ / ‖γ b‖ - -μ / ‖γ a‖) := by
    ring
  rwa [hfinal] at hftc

/-- Away from the centre the inverse-square field is the gradient of the potential `-μ / ‖y‖`
(`EarthScience.hasGradientAt_pointMass_potential` with `G = μ`, `M = 1`), so the force in
`inverseSquare_work` is minus that gradient. Completeness is needed only for `HasGradientAt`. -/
lemma hasGradientAt_inverseSquarePotential [CompleteSpace E] {μ : ℝ} {x : E} (hx : x ≠ 0) :
    HasGradientAt (fun y : E => -μ / ‖y‖) (OrbitalPerturbations.inverseSquareField μ x) x := by
  have h := EarthScience.hasGradientAt_pointMass_potential (G := μ) (M := 1) hx
  simpa [OrbitalPerturbations.inverseSquareField] using h

/-- At the collision point the inverse-square potential (whose value there is the division-by-zero
convention `-μ / 0 = 0`) is not continuous, so no gradient of it exists there. -/
lemma inverseSquarePotential_not_continuousAt_zero [Nontrivial E] {μ : ℝ} (hμ : μ ≠ 0) :
    ¬ ContinuousAt (fun y : E => -μ / ‖y‖) 0 := by
  intro hcont
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ, hδpos, hδ⟩ := hcont 1 (by norm_num)
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hvnorm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hμabs_pos : 0 < |μ| := abs_pos.mpr hμ
  set t : ℝ := min (δ / 2) (|μ| / 2) / ‖v‖ with ht
  have hmin_pos : 0 < min (δ / 2) (|μ| / 2) := lt_min (by linarith) (by linarith)
  have ht_pos : 0 < t := div_pos hmin_pos hvnorm_pos
  have ht_ne : t ≠ 0 := ne_of_gt ht_pos
  set y : E := t • v with hy
  have hy_norm : ‖y‖ = min (δ / 2) (|μ| / 2) := by
    rw [hy, norm_smul, Real.norm_eq_abs, abs_of_pos ht_pos, ht]
    field_simp
  have hy_ne : y ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hy_norm
    linarith [hmin_pos]
  have hdist_y : dist y 0 < δ := by
    rw [dist_zero_right, hy_norm]
    have hle : min (δ / 2) (|μ| / 2) ≤ δ / 2 := min_le_left _ _
    linarith
  have hconseq := hδ hdist_y
  simp only [norm_zero, div_zero] at hconseq
  have hdist_f : dist (-μ / ‖y‖) 0 = |μ| / ‖y‖ := by
    rw [dist_zero_right, Real.norm_eq_abs]
    have hne_y : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy_ne
    rw [abs_div, abs_neg, abs_of_nonneg (norm_nonneg y)]
  rw [hdist_f, hy_norm] at hconseq
  have hle2 : min (δ / 2) (|μ| / 2) ≤ |μ| / 2 := min_le_right _ _
  have hge : (2 : ℝ) ≤ |μ| / min (δ / 2) (|μ| / 2) := by
    have h1 : |μ| / min (δ / 2) (|μ| / 2) ≥ |μ| / (|μ| / 2) :=
      div_le_div_of_nonneg_left hμabs_pos.le hmin_pos hle2
    have h2 : |μ| / (|μ| / 2) = 2 := by field_simp
    linarith
  linarith

/-! ## F. Planar rigid-body power port -/

open scoped Matrix Time
open _root_.Mechanics.RigidMotionPorts _root_.Units.EngineeringFrames

/-- Planar rigid-body power port: for a body of mass `m > 0` with constant moment of inertia
`J > 0` about the fixed axis through its centre of mass, centre-of-mass velocity `V` of class `C¹`
and actual rotation angle `θ` of class `C²` about the axis, the declared balances `m V' = F` and
`J θ'' = τ` give `d/dt (m ‖V‖² / 2 + J θ'² / 2) = ⟪F, V⟫ + τ θ'`. -/
lemma planarRigid_power_port {m J : ℝ} (_hm : 0 < m) (_hJ : 0 < J) {V F : ℝ → E}
    {θ τ : ℝ → ℝ} (hV : ContDiff ℝ 1 V) (hθ : ContDiff ℝ 2 θ) (hF : ∀ t, m • deriv V t = F t)
    (hτ : ∀ t, J * deriv (deriv θ) t = τ t) (t : ℝ) :
    HasDerivAt (fun s => m * ‖V s‖ ^ 2 / 2 + J * deriv θ s ^ 2 / 2)
      (inner ℝ (F t) (V t) + τ t * deriv θ t) t := by
  have hVd : HasDerivAt V (deriv V t) t := ((hV.differentiable one_ne_zero) t).hasDerivAt
  have hω : HasDerivAt (deriv θ) (deriv (deriv θ) t) t :=
    (((contDiff_succ_iff_deriv.1 hθ).2.2.differentiable one_ne_zero) t).hasDerivAt
  have htr := EarthScience.hasDerivAt_kinetic_energy (m := m) (v := V) (a := deriv V) hVd
  rw [hF t] at htr
  have hrot : HasDerivAt (fun s => J * deriv θ s ^ 2 / 2) (τ t * deriv θ t) t := by
    have h := ((hω.pow 2).const_mul J).div_const 2
    rw [← hτ t]
    convert h using 1
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    ring
  exact htr.add hrot

/-- A wrong torque sign fails the power balance: where `τ θ' ≠ 0`, the kinetic energy of the
planar body does not have the rate `⟪F, V⟫ + (-τ) θ'`. -/
lemma planarRigid_power_port_neg_torque {m J : ℝ} (hm : 0 < m) (hJ : 0 < J) {V F : ℝ → E}
    {θ τ : ℝ → ℝ} (hV : ContDiff ℝ 1 V) (hθ : ContDiff ℝ 2 θ) (hF : ∀ t, m • deriv V t = F t)
    (hτ : ∀ t, J * deriv (deriv θ) t = τ t) {t : ℝ} (hτθ : τ t * deriv θ t ≠ 0) :
    ¬ HasDerivAt (fun s => m * ‖V s‖ ^ 2 / 2 + J * deriv θ s ^ 2 / 2)
      (inner ℝ (F t) (V t) + -τ t * deriv θ t) t := by
  intro h
  have h' := planarRigid_power_port hm hJ hV hθ hF hτ t
  have heq := h.unique h'
  apply hτθ
  linarith

/-- Link to Physlib's kinetic-energy split: a rigid motion of positive mass, with body frame
centered at its centre of mass and body angular velocity `(0, 0, ω)` at `t` (rotation about the
third body axis), has Physlib's total kinetic energy `T = m ‖V‖² / 2 + J ω² / 2`, with `V` the
centre-of-mass velocity and `J = (I_B)₃₃` the moment of inertia about the axis through the centre
of mass. -/
lemma kineticEnergy_eq_planar (M : RigidBodyMotion 3) (t : Time) (hm : 0 < M.mass)
    (hR : DifferentiableAt ℝ (fun s => (M.orientation s).1) t) (hc : M.centerOfMass = 0)
    {ω : ℝ} (hω : M.bodyAngularVelocity t = ![0, 0, ω]) :
    M.kineticEnergy t = M.mass * ‖M.centerOfMassVelocity t‖ ^ 2 / 2 +
      M.inertiaTensorAbout M.centerOfMass 2 2 * ω ^ 2 / 2 := by
  rw [M.kineticEnergy_eq_translational_add_bodyAngularVelocity t hm.ne' hR hc, hω,
    real_inner_self_eq_norm_sq]
  have hI : M.toRigidBody.inertiaTensor = M.inertiaTensorAbout M.centerOfMass := by
    rw [hc, RigidBody.inertiaTensorAbout_zero]
  rw [RigidBody.rotationalKineticEnergy, hI]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- The planar torque balance is the axial component of the rotational balance law of the
torque-balance section: along a rigid motion whose orientation is `C²` entry by entry on an open
set `U` of times, with body frame centered at the centre of mass and body angular velocity
`(0, 0, ω)` on `U`, the balance law `dL_COM/dt = τ_I` at `t ∈ U` gives `J ω' = τ`, with
`J = (I_B)₃₃` and `τ = (Rᵀ τ_I)₃` the axial body torque. -/
lemma axial_torque_balance (M : RigidBodyMotion 3) {U : Set Time} (hU : IsOpen U)
    (hR : ∀ i j, ContDiffOn ℝ 2 (fun s => (M.orientation s).1 i j) U) (hc : M.centerOfMass = 0)
    {ω : Time → ℝ} (hω : ∀ s ∈ U, M.bodyAngularVelocity s = ![0, 0, ω s]) {t : Time}
    (ht : t ∈ U) {τI : Fin 3 → ℝ} (hbal : ∂ₜ (comAngularMomentum M) t = τI) :
    M.inertiaTensorAbout M.centerOfMass 2 2 * ∂ₜ ω t =
      inertialToBodyVec (M.orientation t) τI 2 := by
  have heul := (deriv_comAngularMomentum_eq_iff_euler M hU hR hc ht τI).mp hbal
  have hev : M.bodyAngularVelocity =ᶠ[nhds t] fun s => ω s • (![0, 0, 1] : Fin 3 → ℝ) :=
    Filter.eventually_of_mem (hU.mem_nhds ht) fun s hs => by
      rw [hω s hs]
      ext i
      fin_cases i <;> simp
  have hd : ∂ₜ M.bodyAngularVelocity t = ∂ₜ ω t • (![0, 0, 1] : Fin 3 → ℝ) := by
    rw [Time.deriv_eq, hev.fderiv_eq]
    by_cases hf : DifferentiableAt ℝ ω t
    · rw [fderiv_smul_const hf, ContinuousLinearMap.smulRight_apply]
      rfl
    · have hnd : ¬ DifferentiableAt ℝ (fun s => ω s • (![0, 0, 1] : Fin 3 → ℝ)) t := by
        intro h
        apply hf
        simpa using (differentiableAt_pi.1 h) 2
      rw [fderiv_zero_of_not_differentiableAt hnd, Time.deriv_eq,
        fderiv_zero_of_not_differentiableAt hf]
      simp
  have h2 := congrFun heul 2
  rw [hd, hω t ht] at h2
  simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, cross_apply, mul_comm] using h2

end PhyslibExt.Mechanics.PowerPorts
