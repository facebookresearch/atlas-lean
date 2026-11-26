/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Analysis.ODE.FiniteElement1D
public import MathlibExt.Analysis.ODE.RungeKutta
public import PhyslibExt.Elasticity.PrismaticMembers
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import MathlibExt.Analysis.ODE.InvariantRegions
import MathlibExt.Analysis.ODE.TimeStepping
import PhyslibExt.HeatTransfer.ConductionPorts

/-!
# Physical error budgets: P1 bar pullback, thermal Euler and RK4 errors, and an Euler defect budget

## i. Overview

A bar of length `L > 0` and constant axial rigidity `EA > 0`, fixed at both ends, carries the
uniform axial load `q`. Its displacement `axialDisplacement EA L q x = q * x * (L - x) / (2 * EA)`
(the fixed-fixed bar of `PhyslibExt.Elasticity.PrismaticMembers`) is the amplitude
`α = q * L ^ 2 / (2 * EA)` times the unit profile `û ξ = ξ * (1 - ξ)` at `ξ = x / L`, and `û` is
a classical solution of the unit problem `-û'' = 2`, `û 0 = û 1 = 0`, of
`MathlibExt.Analysis.ODE.FiniteElement1D`.

For a partition `P` of `[0, 1]`, the physical P1 reconstruction is `u_h x = α * (I_P û) (x / L)`,
where `I_P = interp P` is the existing nodal interpolant, which is also the P1 Galerkin solution
of the unit problem. The error `e = u - u_h` is `α` times the unit error `ê = û - I_P û` at
`x / L`, so changing variables gives

* `∫₀ᴸ EA (e')² = (EA / L) α² ∫₀¹ (ê')²` and `∫₀ᴸ e² = L α² ∫₀¹ ê²`,

with derivatives in the convention of the finite element module (`deriv` takes junk values at
the finitely many nodes, which no integral sees). The existing mesh estimates then bound both
physical quantities. Both the coordinate factor (`1 / L` in the strain, `L` in `dx`) and the
amplitude `α` are kept.

The normalization is inverted, `û ξ = α⁻¹ * u (L * ξ)`, only when `α ≠ 0`, that is `q ≠ 0`. The
zero load is treated directly: the physical solution, its reconstruction and the error are zero,
and the inverse map does not recover `û`.

Two uniform cells: the unit error vanishes at the nodes and is `1 / 16` at `ξ = 1 / 4`, with
`∫₀¹ (ê')² = 1 / 12` and `∫₀¹ ê² = 1 / 480`; physically `e (L / 4) = α / 16`, the energy is
`(EA / L) α² / 12` and the squared `L²` error is `L α² / 480`. For `EA = 2`, `L = 3`, `q = 4`:
`α = 9`, `e (3 / 4) = 9 / 16`, energy `9 / 2`, squared `L²` error `81 / 160`.

Model inputs: small-strain linear elastic bar with constant `EA`, both ends fixed, uniform load.
Non-goals: no second assembled finite element carrier, no variable `EA`, no claim that zero nodal
error means zero reconstructed error, and no empirical adequacy or system safety claim.

Sections F-H treat a lumped body of heat capacity `C > 0` coupled through the conductance `G > 0`
to a fixed bath at temperature `T_amb`, which delivers the power `Q(T) = -G (T - T_amb)`. The bath
is an external reservoir: `Q` is the source of a one-node thermal network of `ConductionPorts`
with no internal conductance, whose storage law `d(C T)/dt = Q` the trajectory satisfies; with
`Q = 0` the same one-node law keeps the temperature constant instead of relaxing it to `T_amb`.
The trajectory `T(t) = T_amb + Δ exp(-t / τ)`, `τ = C / G`, is the shifted scalar exponential
solution `MetaMathlibExt.scalar_exp_solution` with rate `-1 / τ` and solves `C T' = Q(T)`. One
explicit Euler step of size `dt` maps `T` to `T + dt Q(T) / C = T_amb + (1 - dt / τ) (T - T_amb)`.
At `dt = τ / 10` every real sequence obeying this recurrence from `T_amb + Δ` is
`T_amb + Δ (9 / 10) ^ j`. After ten steps the time is `τ`, and
`T_10 - T(τ) = Δ ((9 / 10) ^ 10 - exp (-1))` is the temperature amplitude times the evaluated
decay error of `MathlibExt.Analysis.ODE.TimeStepping.decay_euler_numeric_bound`, so
`|T_10 - T(τ)| ≤ |Δ| / 10`, and the error is positive for `Δ ≠ 0`. The step depends on `dt` and
`τ` only through `dt / τ`: expressing both times in a common unit leaves it unchanged, while a
step entered in seconds against a time constant in minutes is `60` times too large. The bath is
stable for every step size, but the Euler step `dt = 3 τ` has the amplification `-2`; that
unstable step is outside the selected `dt = τ / 10`.

Sections I-K run the classical fourth-order Runge–Kutta method `rk4` of
`MathlibExt.Analysis.ODE.RungeKutta` on the same model. The right side `Q(T) / C` is the field
`bathField`, on which the one-stage method is `bathEulerStep`. The field does not depend on time,
so an RK4 step from any time equals the step from time `0`, and it is affine in `T`: the step from
`T` is `T_amb` plus the step of the linear decay `θ' = -θ / τ` from the excess `θ = T - T_amb`,
which `rk4_stability` evaluates as `θ R(z)` with `R(z) = 1 + z + z² / 2 + z³ / 6 + z⁴ / 24` and
`z = -dt / τ`. At `dt = τ / 10`, `R = 72387 / 80000`, so ten actual RK4 steps from `T_amb + Δ`
reach `T_amb + Δ (72387 / 80000) ^ 10` at the time `τ`. Mathlib's bounds
`2.7182818283 < exp 1 < 2.7182818286` show that the error, about `3.33 × 10⁻⁷ |Δ|`, is positive and
below `|Δ| × 10⁻⁶` for `Δ ≠ 0`. This is one evaluated instance, not a convergence theorem: the
order conditions of `rk4_orderFour` alone do not give global convergence, and order four does not
give stability, since the step `dt = 3 τ` multiplies the excess by `R(-3) = 11 / 8 > 1`.

Section L propagates the actual residuals of a computed temperature sequence `Y` through the
explicit Euler recurrence of section G at `dt = τ / 10`. The residual of step `j` is
`η_j = Y (j + 1) - (Y j + (τ / 10) Q(Y j) / C)` (`bathEulerResidual`), computed from `Y`, not a
named tolerance. The step maps temperature differences by `9 / 10`, so the defect
`e_j = Y j - X j` against the exact Euler recurrence `X` obeys `e_{j+1} = (9 / 10) e_j + η_j`. The
ten-step defect bound `MathlibExt.Analysis.ODE.TimeStepping.tenStep_defect_le`, from the
product-form discrete Grönwall inequality, then bounds `|e_10|` by
`(9 / 10) ^ 10 |e_0| + ∑_{j < 10} (9 / 10) ^ (9 - j) |η_j|`: a residual at an early step is damped
by more steps than one at a late step. Applied to temperature differences, and only then added to
the truncation term `|Δ| / 10` of section G, this puts the computed `Y 10` within the three-term
budget `tenStepErrorBudget` of the exact trajectory at `τ`: the propagated initial error, the
weighted actual residuals and the truncation, all in the temperature unit. A change of temperature
unit `T ↦ k T + c` (`k > 0`) divides the heat capacity and the conductance by `k`, leaves `τ`
unchanged and multiplies the budget by `k`. Replacing an observed residual by zero can undercut the
actual error.

Model inputs of sections F-L: constant `C`, `G` and `T_amb`, the linear bath law and the lumped
body. Non-goals: no general Euler or Runge–Kutta convergence theorem, no arithmetic or
floating-point refinement (section L takes whatever residuals the computed sequence has) and no
model-discrepancy term.

## ii. Key results

- `unitProfile_isClassicalSolution`, `axialDisplacement_eq_barAmplitude_mul`,
  `isFixedFixedSolution_barAmplitude_mul`, `physicalP1_zero_and_length`,
  `physicalP1_eq_galerkin`: the pullback, the physical load and the Dirichlet values.
- `barAmplitude_ne_zero_iff`, `unitProfile_eq_inv_barAmplitude_mul`, `zero_load`,
  `zero_load_inverse_ne`: inverse normalization only for `α ≠ 0`, and the zero-load branch.
- `physicalError_eq`, `integral_energy_physicalError`, `integral_sq_physicalError`: the two
  scaling identities.
- `integral_energy_physicalError_le_mesh`, `integral_sq_physicalError_le_mesh`: the physical
  instances of the existing mesh estimates.
- `twoCells`, `unitError_twoCells`, `physicalError_twoCells`: the two-cell record; the nonunit
  numeric fixture is in `PhyslibExtTest.Numerical.PhysicalErrorBudgetsTest`.
- `bathPower`, `thermalTimeConstant`, `bathTrajectory`, `bathEulerStep`: the bath model, its
  trajectory and one Euler step.
- `bathTrajectory_solves`, `bathTrajectory_storage`, `oneNode_noSource_const`: the trajectory
  solves `C T' = Q(T)` and the one-node storage law with the bath source; without a source the
  temperature stays constant.
- `bathEuler_closed_form`, `bathEuler_tenStep_error`, `bathEuler_tenStep_error_pos`: the Euler
  recurrence at `dt = τ / 10` and the ten-step error `|T_10 - T(τ)| ≤ |Δ| / 10`, positive for
  `Δ ≠ 0`; the numeric fixture is in the test module.
- `bathEulerStep_timeUnit`, `bathEulerStep_minutes_seconds`, `bathEuler_threeTau`: time units
  and the unstable step `dt = 3 τ`.
- `bathField`, `bathField_eulerStep`, `bathField_rk4_time_indep`, `bathField_rk4_shift`,
  `bathField_rk4_step`: the bath field, its one-stage (Euler) step, and the time independence,
  ambient-temperature shift and stability-polynomial form of its RK4 step.
- `bathRK4_closed_form`, `bathRK4_tenStep_excess`, `bathRK4_tenStep_error`,
  `bathRK4_tenStep_error_pos`: ten RK4 steps at `dt = τ / 10` and the error at `τ`, below
  `|Δ| × 10⁻⁶` and positive for `Δ ≠ 0`; the numeric fixture is in the test module.
- `bathRK4_threeTau`: the unstable RK4 step `dt = 3 τ` of the stable bath.
- `bathEulerResidual`, `tenStepErrorBudget`, `bathEulerStep_sub_tenth`, `defect_recurrence`: the
  actual residual of a computed sequence and the defect recurrence `e_{j+1} = (9 / 10) e_j + η_j`.
- `bathEuler_total_error`, `tenStepErrorBudget_tempUnit`: the three-term ten-step budget, and its
  scaling by `k` under a change of temperature unit `T ↦ k T + c` with the heat capacity and the
  conductance converted to `C / k` and `G / k`; the dropped-residual fixture is in the test module.

## iii. Table of contents

- A. Amplitude, unit profile and the physical reconstruction
- B. Inverse normalization and the zero load
- C. Scaling of the two error integrals
- D. The mesh estimates in physical form
- E. Two uniform cells
- F. The bath-cooling trajectory and the one-node storage law
- G. Ten Euler steps of size `τ / 10`
- H. Time units and the unstable step
- I. Classical Runge–Kutta steps on the bath-cooling model
- J. Ten Runge–Kutta steps of size `τ / 10`
- K. The unstable Runge–Kutta step
- L. Defects through the actual Euler recurrence

## iv. References

- S. C. Brenner and L. R. Scott, *The Mathematical Theory of Finite Element Methods*, 3rd ed.,
  Springer, 2008, chapters 0 to 2 (the one-dimensional P1 method and its error estimates).
- T. J. R. Hughes, *The Finite Element Method: Linear Static and Dynamic Finite Element
  Analysis*, Dover, 2000, chapter 1 (the one-dimensional bar model problem).
- J. M. Gere and B. J. Goodno, *Mechanics of Materials*, 8th ed., 2013 (statically indeterminate
  bars under distributed axial loads).
- F. P. Incropera, D. P. DeWitt, T. L. Bergman and A. S. Lavine, *Fundamentals of Heat and Mass
  Transfer*, 7th ed., Wiley (2011), Section 5.1 (the lumped capacitance method and the thermal
  time constant).
- E. Hairer, S. P. Nørsett and G. Wanner, *Solving Ordinary Differential Equations I*, 2nd ed.,
  Springer (1993), Sections I.7 and II.1 (the explicit Euler method and the classical Runge–Kutta
  method).
- E. Hairer and G. Wanner, *Solving Ordinary Differential Equations II*, 2nd ed., Springer (1996),
  Section IV.2 (stability functions of explicit Runge–Kutta methods).
- E. Süli and D. F. Mayers, *An Introduction to Numerical Analysis*, Cambridge University Press,
  2003, chapter 12 (the global error of one-step methods from their truncation errors).
- `MathlibExt.Analysis.ODE.TimeStepping.decay_euler_numeric_bound`,
  `MetaMathlibExt.scalar_exp_solution`, `ConductionPorts.hasDerivAt_thermalStorage`, and
  `MathlibExt.Analysis.ODE.RungeKutta.rk4_stability` and `euler_step`.
- `MathlibExt.Analysis.ODE.TimeStepping.tenStep_defect_le` (the ten-step defect bound, through
  Mathlib's `discrete_gronwall_prod_general`).
-/

@[expose] public section

namespace PhysicalErrorBudgets

open MeasureTheory MathlibExt.Analysis.Integration MathlibExt.Analysis.ODE.FiniteElement1D
  Elasticity.PrismaticMembers

/-! ## A. Amplitude, unit profile and the physical reconstruction -/

/-- The amplitude `α = q * L ^ 2 / (2 * EA)` of the uniform-load fixed-fixed bar. -/
noncomputable def barAmplitude (EA L q : ℝ) : ℝ :=
  q * L ^ 2 / (2 * EA)

/-- The unit profile `û ξ = ξ * (1 - ξ)`. -/
def unitProfile (ξ : ℝ) : ℝ :=
  ξ * (1 - ξ)

/-- The unit error `ê = û - I_P û` of the existing nodal interpolant on a partition `P` of
`[0, 1]`. -/
noncomputable def unitError (P : Partition (0 : ℝ) 1) (ξ : ℝ) : ℝ :=
  unitProfile ξ - interp P unitProfile ξ

/-- The physical P1 reconstruction `u_h x = α * (I_P û) (x / L)`. -/
noncomputable def physicalP1 (P : Partition (0 : ℝ) 1) (EA L q x : ℝ) : ℝ :=
  barAmplitude EA L q * interp P unitProfile (x / L)

/-- The physical error `e x = u x - u_h x` of the reconstruction against the exact
displacement. -/
noncomputable def physicalError (P : Partition (0 : ℝ) 1) (EA L q x : ℝ) : ℝ :=
  axialDisplacement EA L q x - physicalP1 P EA L q x

/-- The derivative of the unit profile: `û' x = 1 - 2 * x`. -/
private lemma hasDerivAt_unitProfile (x : ℝ) : HasDerivAt unitProfile (1 - 2 * x) x := by
  have h : HasDerivAt (fun ξ : ℝ => ξ * (1 - ξ)) (1 * (1 - x) + x * -1) x :=
    (hasDerivAt_id' x).mul ((hasDerivAt_id' x).const_sub 1)
  exact h.congr_deriv (by ring)

/-- The derivative of the unit profile, as a function. -/
private lemma deriv_unitProfile : deriv unitProfile = fun x => 1 - 2 * x :=
  funext fun x => (hasDerivAt_unitProfile x).deriv

/-- The unit profile is `C²`. -/
private lemma contDiff_unitProfile : ContDiff ℝ 2 unitProfile := by
  unfold unitProfile
  fun_prop

/-- The unit profile is a classical solution of `-û'' = 2` with `û 0 = û 1 = 0`. -/
lemma unitProfile_isClassicalSolution : IsClassicalSolution (fun _ => 2) unitProfile := by
  refine ⟨contDiff_unitProfile, continuous_const, by simp [unitProfile], by simp [unitProfile],
    fun x _ => ?_⟩
  rw [deriv_unitProfile]
  have h : HasDerivAt (fun x : ℝ => 1 - 2 * x) (-(2 * 1)) x :=
    ((hasDerivAt_id' x).const_mul 2).const_sub 1
  rw [h.deriv]
  norm_num

/-- Coordinate and amplitude pullback: `u x = α * û (x / L)` at every `x`. -/
lemma axialDisplacement_eq_barAmplitude_mul {L : ℝ} (hL : L ≠ 0) (EA q x : ℝ) :
    axialDisplacement EA L q x = barAmplitude EA L q * unitProfile (x / L) := by
  unfold axialDisplacement barAmplitude unitProfile
  rcases eq_or_ne EA 0 with h | h
  · simp [h]
  · field_simp

/-- The physical load is `q` and both ends are fixed: the pulled-back profile solves the
fixed-fixed bar problem `-(EA * u'') = q`, `u 0 = u L = 0`. -/
lemma isFixedFixedSolution_barAmplitude_mul {EA L : ℝ} (hL : 0 < L) (hEA : 0 < EA) (q : ℝ) :
    IsFixedFixedSolution EA L (fun _ => q)
      (fun x => barAmplitude EA L q * unitProfile (x / L)) := by
  have h : (fun x => barAmplitude EA L q * unitProfile (x / L)) = axialDisplacement EA L q :=
    funext fun x => (axialDisplacement_eq_barAmplitude_mul hL.ne' EA q x).symm
  rw [h]
  exact isFixedFixedSolution_axialDisplacement hL hEA q

/-- Both Dirichlet values of the reconstruction: `u_h 0 = 0` and `u_h L = 0`. -/
lemma physicalP1_zero_and_length (P : Partition (0 : ℝ) 1) {L : ℝ} (hL : L ≠ 0) (EA q : ℝ) :
    physicalP1 P EA L q 0 = 0 ∧ physicalP1 P EA L q L = 0 := by
  have hnode : ∀ j, interp P unitProfile (P.points j) = unitProfile (P.points j) :=
    fun j => p1_points P _ j
  have h0 : interp P unitProfile 0 = unitProfile 0 := by simpa [P.first] using hnode 0
  have h1 : interp P unitProfile 1 = unitProfile 1 := by simpa [P.last] using hnode (Fin.last P.n)
  constructor
  · simp [physicalP1, h0, unitProfile]
  · simp [physicalP1, div_self hL, h1, unitProfile]

/-- The reconstruction is the amplitude times the Galerkin solution of the unit problem. -/
lemma physicalP1_eq_galerkin (P : Partition (0 : ℝ) 1) {c : Fin (P.n + 1) → ℝ}
    (hc : IsGalerkinSolution P (fun _ => 2) c) (EA L q x : ℝ) :
    physicalP1 P EA L q x = barAmplitude EA L q * p1 P c (x / L) := by
  rw [physicalP1, p1_eq_interp_of_isGalerkinSolution P unitProfile_isClassicalSolution hc]

/-! ## B. Inverse normalization and the zero load -/

/-- For `EA ≠ 0` and `L ≠ 0`, the amplitude is nonzero exactly for a nonzero load. -/
lemma barAmplitude_ne_zero_iff {EA L : ℝ} (hEA : EA ≠ 0) (hL : L ≠ 0) (q : ℝ) :
    barAmplitude EA L q ≠ 0 ↔ q ≠ 0 := by
  unfold barAmplitude
  constructor
  · intro h hq
    apply h
    simp [hq]
  · intro hq
    exact div_ne_zero (mul_ne_zero hq (pow_ne_zero 2 hL)) (mul_ne_zero two_ne_zero hEA)

/-- Inverse normalization, only for `α ≠ 0`: `û ξ = α⁻¹ * u (L * ξ)`. -/
lemma unitProfile_eq_inv_barAmplitude_mul {EA L q : ℝ} (hL : L ≠ 0)
    (hα : barAmplitude EA L q ≠ 0) (ξ : ℝ) :
    unitProfile ξ = (barAmplitude EA L q)⁻¹ * axialDisplacement EA L q (L * ξ) := by
  rw [axialDisplacement_eq_barAmplitude_mul hL, mul_div_cancel_left₀ ξ hL,
    inv_mul_cancel_left₀ hα]

/-- Zero load, treated directly: the amplitude, the physical solution, its reconstruction and
the error are all zero. -/
lemma zero_load (P : Partition (0 : ℝ) 1) (EA L : ℝ) :
    barAmplitude EA L 0 = 0 ∧ (∀ x, axialDisplacement EA L 0 x = 0) ∧
      (∀ x, physicalP1 P EA L 0 x = 0) ∧ ∀ x, physicalError P EA L 0 x = 0 := by
  refine ⟨by simp [barAmplitude], fun x => by simp [axialDisplacement],
    fun x => by simp [physicalP1, barAmplitude], fun x => ?_⟩
  simp [physicalError, physicalP1, barAmplitude, axialDisplacement]

/-- At zero load the inverse amplitude map does not recover the unit profile: at `ξ = 1 / 2` it
gives `0`, while `û (1 / 2) = 1 / 4`. -/
lemma zero_load_inverse_ne (EA L : ℝ) :
    (barAmplitude EA L 0)⁻¹ * axialDisplacement EA L 0 (L * (1 / 2)) ≠ unitProfile (1 / 2) := by
  norm_num [barAmplitude, axialDisplacement, unitProfile]

/-! ## C. Scaling of the two error integrals -/

/-- The physical error is the amplitude times the unit error at `x / L`, at every `x`. -/
lemma physicalError_eq (P : Partition (0 : ℝ) 1) {L : ℝ} (hL : L ≠ 0) (EA q x : ℝ) :
    physicalError P EA L q x = barAmplitude EA L q * unitError P (x / L) := by
  rw [physicalError, axialDisplacement_eq_barAmplitude_mul hL, physicalP1, unitError]
  ring

/-- Energy scaling: `∫₀ᴸ EA (e')² = (EA / L) α² ∫₀¹ (ê')²`. -/
lemma integral_energy_physicalError (P : Partition (0 : ℝ) 1) {L : ℝ} (hL : 0 < L) (EA q : ℝ) :
    ∫ x in (0 : ℝ)..L, EA * deriv (physicalError P EA L q) x ^ 2 =
      EA / L * barAmplitude EA L q ^ 2 * ∫ ξ in (0 : ℝ)..1, deriv (unitError P) ξ ^ 2 := by
  have hL0 := hL.ne'
  have hs : physicalError P EA L q = fun x => barAmplitude EA L q * unitError P (L⁻¹ * x) := by
    funext x
    rw [physicalError_eq P hL0, div_eq_inv_mul]
  have hd : ∀ x, deriv (physicalError P EA L q) x =
      barAmplitude EA L q * (L⁻¹ * deriv (unitError P) (L⁻¹ * x)) := by
    intro x
    rw [hs, deriv_const_mul_field, deriv_comp_mul_left, smul_eq_mul]
  have hi : ∫ x in (0 : ℝ)..L, EA * deriv (physicalError P EA L q) x ^ 2 =
      ∫ x in (0 : ℝ)..L, EA * barAmplitude EA L q ^ 2 * L⁻¹ ^ 2 *
        deriv (unitError P) (L⁻¹ * x) ^ 2 := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [hd]
    ring
  rw [hi, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun ξ => deriv (unitError P) ξ ^ 2)
      (inv_ne_zero hL0), mul_zero, inv_mul_cancel₀ hL0, inv_inv, smul_eq_mul]
  field_simp

/-- `L²` scaling: `∫₀ᴸ e² = L α² ∫₀¹ ê²`. -/
lemma integral_sq_physicalError (P : Partition (0 : ℝ) 1) {L : ℝ} (hL : 0 < L) (EA q : ℝ) :
    ∫ x in (0 : ℝ)..L, physicalError P EA L q x ^ 2 =
      L * barAmplitude EA L q ^ 2 * ∫ ξ in (0 : ℝ)..1, unitError P ξ ^ 2 := by
  have hL0 := hL.ne'
  have hi : ∫ x in (0 : ℝ)..L, physicalError P EA L q x ^ 2 =
      ∫ x in (0 : ℝ)..L, barAmplitude EA L q ^ 2 * unitError P (L⁻¹ * x) ^ 2 := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [physicalError_eq P hL0, div_eq_inv_mul]
    ring
  rw [hi, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun ξ => unitError P ξ ^ 2) (inv_ne_zero hL0),
    mul_zero, inv_mul_cancel₀ hL0, inv_inv, smul_eq_mul]
  ring

/-! ## D. The mesh estimates in physical form -/

/-- The existing energy estimate `‖ê‖²_a ≤ (h / π)² ‖2‖²_{L²}` in physical form:
`∫₀ᴸ EA (e')² ≤ (EA / L) α² (4 (h / π)²)`, with `h` the mesh size of `P`. -/
lemma integral_energy_physicalError_le_mesh (P : Partition (0 : ℝ) 1) {EA L : ℝ} (hL : 0 < L)
    (hEA : 0 < EA) (q : ℝ) :
    ∫ x in (0 : ℝ)..L, EA * deriv (physicalError P EA L q) x ^ 2 ≤
      EA / L * barAmplitude EA L q ^ 2 * (4 * (P.mesh / Real.pi) ^ 2) := by
  rw [integral_energy_physicalError P hL EA q]
  have hc := isGalerkinSolution_nodal P unitProfile_isClassicalSolution
  have hb := energy_sub_galerkin_le_mesh P unitProfile_isClassicalSolution hc
  have h1 : ∫ ξ in (0 : ℝ)..1, deriv (unitError P) ξ ^ 2 =
      energy (unitProfile - p1 P fun j => unitProfile (P.points j))
        (unitProfile - p1 P fun j => unitProfile (P.points j)) := by
    unfold energy
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [sq]
    rfl
  have h2 : ∫ x in (0 : ℝ)..1, (fun _ : ℝ => (2 : ℝ)) x ^ 2 = 4 := by norm_num
  have hk : 0 ≤ EA / L * barAmplitude EA L q ^ 2 :=
    mul_nonneg (div_nonneg hEA.le hL.le) (sq_nonneg _)
  rw [h1]
  calc _ ≤ EA / L * barAmplitude EA L q ^ 2 *
        ((P.mesh / Real.pi) ^ 2 * ∫ x in (0 : ℝ)..1, (fun _ : ℝ => (2 : ℝ)) x ^ 2) :=
        mul_le_mul_of_nonneg_left hb hk
    _ = _ := by rw [h2]; ring

/-- The existing `L²` estimate `‖ê‖²_{L²} ≤ (h / π)⁴ ‖2‖²_{L²}` in physical form:
`∫₀ᴸ e² ≤ L α² (4 (h / π)⁴)`. -/
lemma integral_sq_physicalError_le_mesh (P : Partition (0 : ℝ) 1) {L : ℝ} (hL : 0 < L)
    (EA q : ℝ) :
    ∫ x in (0 : ℝ)..L, physicalError P EA L q x ^ 2 ≤
      L * barAmplitude EA L q ^ 2 * (4 * (P.mesh / Real.pi) ^ 4) := by
  rw [integral_sq_physicalError P hL EA q]
  have hc := isGalerkinSolution_nodal P unitProfile_isClassicalSolution
  have hb := integral_sq_sub_galerkin_le_mesh P unitProfile_isClassicalSolution hc
  have h2 : ∫ x in (0 : ℝ)..1, (fun _ : ℝ => (2 : ℝ)) x ^ 2 = 4 := by norm_num
  have hk : 0 ≤ L * barAmplitude EA L q ^ 2 := mul_nonneg hL.le (sq_nonneg _)
  calc _ ≤ L * barAmplitude EA L q ^ 2 *
        ((P.mesh / Real.pi) ^ 4 * ∫ x in (0 : ℝ)..1, (fun _ : ℝ => (2 : ℝ)) x ^ 2) :=
        mul_le_mul_of_nonneg_left hb hk
    _ = _ := by rw [h2]; ring

/-! ## E. Two uniform cells -/

/-- The partition `0 < 1 / 2 < 1` of `[0, 1]` into two uniform cells. -/
noncomputable def twoCells : Partition (0 : ℝ) 1 where
  n := 2
  points := ![0, 1 / 2, 1]
  ordered := by
    refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
    fin_cases i <;> norm_num
  first := rfl
  last := by simp

/-- Inside the `i`-th element, the unit error has derivative `1 - 2 x - slopeᵢ`, with `slopeᵢ`
the slope of the interpolant there. -/
private lemma hasDerivAt_unitError (P : Partition (0 : ℝ) 1) (i : Fin P.n) {x : ℝ}
    (hx : x ∈ Set.Ioo (P.points i.castSucc) (P.points i.succ)) :
    HasDerivAt (unitError P)
      (1 - 2 * x - elementSlope P (fun j => unitProfile (P.points j)) i) x :=
  (hasDerivAt_unitProfile x).sub (hasDerivAt_p1 P _ i hx)

/-- The integral of a polynomial of degree at most four over `[a, b]`. -/
private lemma integral_poly4 (a b c0 c1 c2 c3 c4 : ℝ) :
    ∫ x in a..b, (c0 + c1 * x + c2 * x ^ 2 + c3 * x ^ 3 + c4 * x ^ 4) =
      c0 * (b - a) + c1 * (b ^ 2 - a ^ 2) / 2 + c2 * (b ^ 3 - a ^ 3) / 3 +
        c3 * (b ^ 4 - a ^ 4) / 4 + c4 * (b ^ 5 - a ^ 5) / 5 := by
  have hG : ∀ x ∈ Set.uIcc a b, HasDerivAt
      (fun x => c0 * x + c1 * x ^ 2 / 2 + c2 * x ^ 3 / 3 + c3 * x ^ 4 / 4 + c4 * x ^ 5 / 5)
      (c0 + c1 * x + c2 * x ^ 2 + c3 * x ^ 3 + c4 * x ^ 4) x := by
    intro x _
    have h := (((((hasDerivAt_id' x).const_mul c0).add
      (((hasDerivAt_pow 2 x).const_mul c1).div_const 2)).add
      (((hasDerivAt_pow 3 x).const_mul c2).div_const 3)).add
      (((hasDerivAt_pow 4 x).const_mul c3).div_const 4)).add
      (((hasDerivAt_pow 5 x).const_mul c4).div_const 5)
    convert h using 1
    norm_num
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hG
    ((by fun_prop : Continuous fun x : ℝ =>
      c0 + c1 * x + c2 * x ^ 2 + c3 * x ^ 3 + c4 * x ^ 4).intervalIntegrable _ _)]
  ring

/-- Two cells, unit problem: the error vanishes at the nodes but is `1 / 16` at `ξ = 1 / 4`;
`∫₀¹ (ê')² = 1 / 12` and `∫₀¹ ê² = 1 / 480`. -/
lemma unitError_twoCells :
    (∀ j, unitError twoCells (twoCells.points j) = 0) ∧ unitError twoCells (1 / 4) = 1 / 16 ∧
      ∫ ξ in (0 : ℝ)..1, deriv (unitError twoCells) ξ ^ 2 = 1 / 12 ∧
      ∫ ξ in (0 : ℝ)..1, unitError twoCells ξ ^ 2 = 1 / 480 := by
  have hp0 : twoCells.points 0 = 0 := rfl
  have hp1 : twoCells.points 1 = 1 / 2 := rfl
  have hp2 : twoCells.points 2 = 1 := rfl
  have hs0 :
      elementSlope twoCells (fun j => unitProfile (twoCells.points j)) (0 : Fin 2) = 1 / 2 := by
    simp only [elementSlope, width]
    change (unitProfile (twoCells.points 1) - unitProfile (twoCells.points 0)) /
      (twoCells.points 1 - twoCells.points 0) = 1 / 2
    rw [hp0, hp1]
    norm_num [unitProfile]
  have hs1 :
      elementSlope twoCells (fun j => unitProfile (twoCells.points j)) (1 : Fin 2) = -1 / 2 := by
    simp only [elementSlope, width]
    change (unitProfile (twoCells.points 2) - unitProfile (twoCells.points 1)) /
      (twoCells.points 2 - twoCells.points 1) = -1 / 2
    rw [hp1, hp2]
    norm_num [unitProfile]
  have hlin0 : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2), unitError twoCells x = x / 2 - x ^ 2 := by
    intro x hx
    have h := p1_eq_of_mem_Icc twoCells (fun j => unitProfile (twoCells.points j)) (0 : Fin 2)
      (x := x) (by
        change x ∈ Set.Icc (twoCells.points 0) (twoCells.points 1); rw [hp0, hp1]; exact hx)
    rw [unitError, interp, h, hs0]
    change unitProfile x - (unitProfile (twoCells.points 0) + 1 / 2 * (x - twoCells.points 0)) = _
    rw [hp0]
    simp [unitProfile]
    ring
  have hlin1 : ∀ x ∈ Set.Icc (1 / 2 : ℝ) 1, unitError twoCells x = 3 / 2 * x - x ^ 2 - 1 / 2 := by
    intro x hx
    have h := p1_eq_of_mem_Icc twoCells (fun j => unitProfile (twoCells.points j)) (1 : Fin 2)
      (x := x) (by
        change x ∈ Set.Icc (twoCells.points 1) (twoCells.points 2); rw [hp1, hp2]; exact hx)
    rw [unitError, interp, h, hs1]
    change unitProfile x - (unitProfile (twoCells.points 1) + -1 / 2 * (x - twoCells.points 1)) = _
    rw [hp1]
    simp [unitProfile]
    ring
  have hd0 : Set.EqOn (fun x : ℝ => (1 / 2 - 2 * x) ^ 2) (fun x => deriv (unitError twoCells) x ^ 2)
      (Set.uIoo 0 (1 / 2)) := by
    intro x hx
    rw [Set.uIoo_of_le (by norm_num)] at hx
    have h := hasDerivAt_unitError twoCells (0 : Fin 2) (x := x)
      (by change x ∈ Set.Ioo (twoCells.points 0) (twoCells.points 1); rw [hp0, hp1]; exact hx)
    simp only
    rw [h.deriv, hs0]
    ring
  have hd1 : Set.EqOn (fun x : ℝ => (3 / 2 - 2 * x) ^ 2) (fun x => deriv (unitError twoCells) x ^ 2)
      (Set.uIoo (1 / 2) 1) := by
    intro x hx
    rw [Set.uIoo_of_le (by norm_num)] at hx
    have h := hasDerivAt_unitError twoCells (1 : Fin 2) (x := x)
      (by change x ∈ Set.Ioo (twoCells.points 1) (twoCells.points 2); rw [hp1, hp2]; exact hx)
    simp only
    rw [h.deriv, hs1]
    ring
  refine ⟨fun j => ?_, ?_, ?_, ?_⟩
  · rw [unitError, interp, p1_points]
    simp
  · rw [hlin0 _ ⟨by norm_num, by norm_num⟩]
    norm_num
  · have hc0 : Continuous fun x : ℝ => (1 / 2 - 2 * x) ^ 2 := by fun_prop
    have hc1 : Continuous fun x : ℝ => (3 / 2 - 2 * x) ^ 2 := by fun_prop
    rw [← intervalIntegral.integral_add_adjacent_intervals
      ((hc0.intervalIntegrable 0 (1 / 2)).congr_uIoo hd0)
      ((hc1.intervalIntegrable (1 / 2) 1).congr_uIoo hd1),
      ← intervalIntegral.integral_congr_uIoo hd0, ← intervalIntegral.integral_congr_uIoo hd1]
    have e0 : ∫ x in (0 : ℝ)..(1 / 2), (1 / 2 - 2 * x) ^ 2 =
        ∫ x in (0 : ℝ)..(1 / 2), ((1 / 4) + (-2) * x + 4 * x ^ 2 + 0 * x ^ 3 + 0 * x ^ 4) :=
      intervalIntegral.integral_congr fun x _ => by ring
    have e1 : ∫ x in (1 / 2 : ℝ)..1, (3 / 2 - 2 * x) ^ 2 =
        ∫ x in (1 / 2 : ℝ)..1, ((9 / 4) + (-6) * x + 4 * x ^ 2 + 0 * x ^ 3 + 0 * x ^ 4) :=
      intervalIntegral.integral_congr fun x _ => by ring
    rw [e0, e1, integral_poly4, integral_poly4]
    norm_num
  · have hc : Continuous fun x => unitError twoCells x ^ 2 :=
      ((contDiff_unitProfile.continuous).sub (continuous_p1 twoCells _)).pow 2
    rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 (1 / 2))
      (hc.intervalIntegrable (1 / 2) 1)]
    have e0 : ∫ x in (0 : ℝ)..(1 / 2), unitError twoCells x ^ 2 =
        ∫ x in (0 : ℝ)..(1 / 2), (0 + 0 * x + (1 / 4) * x ^ 2 + (-1) * x ^ 3 + 1 * x ^ 4) := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [Set.uIcc_of_le (by norm_num)] at hx
      rw [hlin0 x hx]
      ring
    have e1 : ∫ x in (1 / 2 : ℝ)..1, unitError twoCells x ^ 2 =
        ∫ x in (1 / 2 : ℝ)..1,
          ((1 / 4) + (-3 / 2) * x + (13 / 4) * x ^ 2 + (-3) * x ^ 3 + 1 * x ^ 4)
          := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [Set.uIcc_of_le (by norm_num)] at hx
      rw [hlin1 x hx]
      ring
    rw [e0, e1, integral_poly4, integral_poly4]
    norm_num

/-- Two cells, physical bar: `e (L / 4) = α / 16`, energy `(EA / L) α² / 12` and squared `L²`
error `L α² / 480`. -/
lemma physicalError_twoCells {L : ℝ} (hL : 0 < L) (EA q : ℝ) :
    physicalError twoCells EA L q (L / 4) = barAmplitude EA L q / 16 ∧
      ∫ x in (0 : ℝ)..L, EA * deriv (physicalError twoCells EA L q) x ^ 2 =
        EA / L * barAmplitude EA L q ^ 2 / 12 ∧
      ∫ x in (0 : ℝ)..L, physicalError twoCells EA L q x ^ 2 =
        L * barAmplitude EA L q ^ 2 / 480 := by
  obtain ⟨-, h4, hE, hS⟩ := unitError_twoCells
  refine ⟨?_, ?_, ?_⟩
  · rw [physicalError_eq twoCells hL.ne', show L / 4 / L = 1 / 4 by field_simp [hL.ne'], h4]
    ring
  · rw [integral_energy_physicalError twoCells hL EA q, hE]
    ring
  · rw [integral_sq_physicalError twoCells hL EA q, hS]
    ring

/-! ## F. The bath-cooling trajectory and the one-node storage law -/

/-- The power `Q(T) = -G (T - T_amb)` that a fixed bath at temperature `T_amb` delivers through the
conductance `G` to a body at temperature `T`. -/
def bathPower (G Tamb T : ℝ) : ℝ := -G * (T - Tamb)

/-- The thermal time constant `τ = C / G` of a body of heat capacity `C` coupled to a bath through
the conductance `G`. -/
noncomputable def thermalTimeConstant (C G : ℝ) : ℝ := C / G

/-- The bath-cooling trajectory `T(t) = T_amb + Δ exp(-t / τ)` with `τ = C / G`. -/
noncomputable def bathTrajectory (C G Tamb Δ t : ℝ) : ℝ :=
  Tamb + Δ * Real.exp (-t / thermalTimeConstant C G)

/-- One explicit Euler step `T ↦ T + dt Q(T) / C` of `C T' = Q(T)` with the time step `dt`. -/
noncomputable def bathEulerStep (C G Tamb dt T : ℝ) : ℝ := T + dt * bathPower G Tamb T / C

/-- **The trajectory solves the bath equation.** For `C, G > 0`, `T(0) = T_amb + Δ` and
`T' = Q(T) / C`, that is `C T' = Q(T)`, at every time: the excess `T - T_amb` is the scalar
exponential solution with rate `-1 / τ`. -/
lemma bathTrajectory_solves {C G : ℝ} (hC : 0 < C) (hG : 0 < G) (Tamb Δ : ℝ) :
    bathTrajectory C G Tamb Δ 0 = Tamb + Δ ∧
      ∀ t, HasDerivAt (bathTrajectory C G Tamb Δ)
        (bathPower G Tamb (bathTrajectory C G Tamb Δ t) / C) t := by
  have hx : ∀ t, bathTrajectory C G Tamb Δ t - Tamb =
      Δ * Real.exp (-1 / thermalTimeConstant C G * t) := by
    intro t
    rw [bathTrajectory, add_sub_cancel_left]
    congr 2
    ring
  obtain ⟨h0, hd⟩ := MetaMathlibExt.scalar_exp_solution hx
  refine ⟨by linarith, fun t => ?_⟩
  have h := (hd t).add_const Tamb
  simp only [sub_add_cancel] at h
  convert h using 1
  unfold bathPower thermalTimeConstant
  field_simp

/-- **The one-node storage law with the bath source.** For `C, G > 0` the stored heat `C T` of the
trajectory has the rate `Q(T(t))`: `ConductionPorts.hasDerivAt_thermalStorage` for one node with
capacity `C`, no internal conductance and the bath power as its source. -/
lemma bathTrajectory_storage {C G : ℝ} (hC : 0 < C) (hG : 0 < G) (Tamb Δ t : ℝ) :
    HasDerivAt (fun s => C * bathTrajectory C G Tamb Δ s)
      (bathPower G Tamb (bathTrajectory C G Tamb Δ t)) t := by
  have h := ConductionPorts.hasDerivAt_thermalStorage (ι := Unit) (C := fun _ => C)
    (G := fun _ _ => 0) (T := fun _ => bathTrajectory C G Tamb Δ)
    (dT := fun _ => bathPower G Tamb (bathTrajectory C G Tamb Δ t) / C)
    (Q := fun _ => bathPower G Tamb (bathTrajectory C G Tamb Δ t)) (fun _ _ => rfl)
    (fun _ => (bathTrajectory_solves hC hG Tamb Δ).2 t)
    (fun _ => by simp only [zero_mul, Finset.sum_const_zero, zero_add]; field_simp)
  simpa using h

/-- **No source, constant temperature.** A one-node network with capacity `C > 0`, no internal
conductance and no source (`C T' = 0`) keeps its temperature: the storage law gives a constant
`C T`. -/
lemma oneNode_noSource_const {C : ℝ} (hC : 0 < C) {T dT : ℝ → ℝ}
    (hT : ∀ t, HasDerivAt T (dT t) t) (hbal : ∀ t, C * dT t = 0) (t : ℝ) : T t = T 0 := by
  have hstore : ∀ s, HasDerivAt (fun τ => C * T τ) 0 s := by
    intro s
    have h := ConductionPorts.hasDerivAt_thermalStorage (ι := Unit) (C := fun _ => C)
      (G := fun _ _ => 0) (T := fun _ => T) (dT := fun _ => dT s) (Q := fun _ => 0)
      (fun _ _ => rfl) (fun _ => hT s) (fun _ => by simpa using hbal s)
    simpa using h
  have hconst := is_const_of_deriv_eq_zero (fun s => (hstore s).differentiableAt)
    (fun s => (hstore s).deriv) t 0
  exact mul_left_cancel₀ hC.ne' hconst

/-! ## G. Ten Euler steps of size `τ / 10` -/

/-- **The actual Euler recurrence at `dt = τ / 10`.** For `C, G > 0`, every real sequence with
`X 0 = T_amb + Δ` and `X (j + 1) = X j + (τ / 10) Q(X j) / C` is `X j = T_amb + Δ (9 / 10) ^ j`. -/
lemma bathEuler_closed_form {C G : ℝ} (hC : 0 < C) (hG : 0 < G) {Tamb Δ : ℝ} {X : ℕ → ℝ}
    (h0 : X 0 = Tamb + Δ)
    (hstep : ∀ j, X (j + 1) = bathEulerStep C G Tamb (thermalTimeConstant C G / 10) (X j))
    (j : ℕ) : X j = Tamb + Δ * (9 / 10) ^ j := by
  induction j with
  | zero => simpa using h0
  | succ j ih =>
    rw [hstep, ih, bathEulerStep, bathPower, thermalTimeConstant, pow_succ]
    field_simp
    ring

/-- **Ten-step error bound.** For `C, G > 0`, the actual Euler recurrence at `dt = τ / 10` started
at `T_amb + Δ` satisfies `|T_10 - T(τ)| ≤ |Δ| / 10`: the temperature amplitude `|Δ|` times the
evaluated decay error `|(9 / 10) ^ 10 - exp (-1)| ≤ 1 / 10`. -/
lemma bathEuler_tenStep_error {C G : ℝ} (hC : 0 < C) (hG : 0 < G) {Tamb Δ : ℝ} {X : ℕ → ℝ}
    (h0 : X 0 = Tamb + Δ)
    (hstep : ∀ j, X (j + 1) = bathEulerStep C G Tamb (thermalTimeConstant C G / 10) (X j)) :
    |X 10 - bathTrajectory C G Tamb Δ (thermalTimeConstant C G)| ≤ |Δ| / 10 := by
  have hτ : thermalTimeConstant C G ≠ 0 := (div_pos hC hG).ne'
  have hbound := MathlibExt.Analysis.ODE.TimeStepping.decay_euler_numeric_bound
  rw [bathEuler_closed_form hC hG h0 hstep 10, bathTrajectory, neg_div, div_self hτ]
  calc |Tamb + Δ * (9 / 10) ^ 10 - (Tamb + Δ * Real.exp (-1))|
      = |Δ| * |(9 / 10 : ℝ) ^ 10 - Real.exp (-1)| := by
        rw [← abs_mul]
        ring_nf
    _ ≤ |Δ| * (1 * (1 / 10)) := mul_le_mul_of_nonneg_left hbound (abs_nonneg Δ)
    _ = |Δ| / 10 := by ring

/-- **The error is not zero.** Under the hypotheses of `bathEuler_tenStep_error` with `Δ ≠ 0`,
`|T_10 - T(τ)| > 0`: `(9 / 10) ^ 10 < 0.3487 < exp (-1)`. -/
lemma bathEuler_tenStep_error_pos {C G : ℝ} (hC : 0 < C) (hG : 0 < G) {Tamb Δ : ℝ}
    (hΔ : Δ ≠ 0) {X : ℕ → ℝ} (h0 : X 0 = Tamb + Δ)
    (hstep : ∀ j, X (j + 1) = bathEulerStep C G Tamb (thermalTimeConstant C G / 10) (X j)) :
    0 < |X 10 - bathTrajectory C G Tamb Δ (thermalTimeConstant C G)| := by
  have hτ : thermalTimeConstant C G ≠ 0 := (div_pos hC hG).ne'
  have hlt : (9 / 10 : ℝ) ^ 10 < Real.exp (-1) := by
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have hexp : Real.exp (-1 : ℝ) = 1 / Real.exp 1 := by rw [Real.exp_neg, one_div]
    rw [hexp, lt_div_iff₀ (Real.exp_pos 1)]
    nlinarith
  rw [bathEuler_closed_form hC hG h0 hstep 10, bathTrajectory, neg_div, div_self hτ,
    show Tamb + Δ * (9 / 10) ^ 10 - (Tamb + Δ * Real.exp (-1)) =
      Δ * ((9 / 10) ^ 10 - Real.exp (-1)) by ring, abs_mul]
  exact mul_pos (abs_pos.mpr hΔ) (abs_pos.mpr (by linarith))

/-! ## H. Time units and the unstable step -/

/-- **Common time unit.** Expressing both times in a unit `k > 0` times smaller (`dt ↦ k dt`,
`G ↦ G / k`) multiplies the time constant by `k` and leaves the Euler step unchanged: the step
depends on `dt` and `τ` only through `dt / τ`. -/
lemma bathEulerStep_timeUnit {k : ℝ} (hk : 0 < k) (C G Tamb dt T : ℝ) :
    thermalTimeConstant C (G / k) = k * thermalTimeConstant C G ∧
      bathEulerStep C (G / k) Tamb (k * dt) T = bathEulerStep C G Tamb dt T := by
  unfold thermalTimeConstant bathEulerStep bathPower
  rcases eq_or_ne G 0 with rfl | hG
  · simp
  · constructor <;> field_simp

/-- **Mismatched time units.** A step `τ / 10` entered in seconds against a time constant in
minutes is `60` times too large: for `C, G > 0` it multiplies the excess by `1 - 6 = -5`. -/
lemma bathEulerStep_minutes_seconds {C G : ℝ} (hC : 0 < C) (hG : 0 < G) (Tamb θ : ℝ) :
    bathEulerStep C G Tamb (60 * (thermalTimeConstant C G / 10)) (Tamb + θ) = Tamb - 5 * θ := by
  unfold bathEulerStep bathPower thermalTimeConstant
  field_simp
  ring

/-- **The unstable step of a stable bath.** For `C, G > 0` the exact excess never exceeds its
initial size, `|T(t) - T_amb| ≤ |Δ|` for `t ≥ 0`, but the Euler recurrence with `dt = 3 τ` has
the amplification `-2`: `X j = T_amb + Δ (-2) ^ j` and `|X j - T_amb| = 2 ^ j |Δ|`. -/
lemma bathEuler_threeTau {C G : ℝ} (hC : 0 < C) (hG : 0 < G) {Tamb Δ : ℝ} {X : ℕ → ℝ}
    (h0 : X 0 = Tamb + Δ)
    (hstep : ∀ j, X (j + 1) = bathEulerStep C G Tamb (3 * thermalTimeConstant C G) (X j)) :
    (∀ t, 0 ≤ t → |bathTrajectory C G Tamb Δ t - Tamb| ≤ |Δ|) ∧
      ∀ j, X j = Tamb + Δ * (-2) ^ j ∧ |X j - Tamb| = 2 ^ j * |Δ| := by
  have hτ : 0 < thermalTimeConstant C G := div_pos hC hG
  have hX : ∀ j, X j = Tamb + Δ * (-2) ^ j := by
    intro j
    induction j with
    | zero => simpa using h0
    | succ j ih =>
      rw [hstep, ih, bathEulerStep, bathPower, thermalTimeConstant, pow_succ]
      field_simp
      ring
  refine ⟨fun t ht => ?_, fun j => ⟨hX j, ?_⟩⟩
  · rw [bathTrajectory, add_sub_cancel_left, abs_mul, Real.abs_exp]
    have h1 : Real.exp (-t / thermalTimeConstant C G) ≤ 1 :=
      Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by linarith) hτ.le)
    nlinarith [abs_nonneg Δ]
  · rw [hX j, add_sub_cancel_left, abs_mul, abs_pow, abs_neg, abs_two, mul_comm]


/-! ## I. Classical Runge–Kutta steps on the bath-cooling model -/

section RungeKuttaComparison

open MathlibExt.Analysis.ODE.RungeKutta

/-- The right side `(t, T) ↦ Q(T) / C` of the bath-cooling equation `C T' = Q(T)` of
`PhysicalErrorBudgets`, as a field that does not depend on the time `t`. -/
noncomputable def bathField (C G Tamb : ℝ) (_t T : ℝ) : ℝ := bathPower G Tamb T / C

/-- The stages of an explicit Runge–Kutta method for a field that ignores time do not depend on
the start time. -/
private lemma stageRow_autonomous {s : ℕ} (rk : ExplicitRK s) (g : ℝ → ℝ) (t t' y h : ℝ) :
    ∀ n, stageRow rk (fun _ x => g x) t y h n = stageRow rk (fun _ x => g x) t' y h n
  | 0 => rfl
  | n + 1 => by
      funext i
      simp only [stageRow]
      rw [stageRow_autonomous rk g t t' y h n]

/-- The stages for the affine field `x ↦ λ (x - c)` from `y` are those for the linear field
`x ↦ λ x` from `y - c`. -/
private lemma stageRow_shift {s : ℕ} (rk : ExplicitRK s) (lam c t y h : ℝ) :
    ∀ n, stageRow rk (fun _ x => lam * (x - c)) t y h n =
      stageRow rk (fun _ x => lam * x) 0 (y - c) h n
  | 0 => rfl
  | n + 1 => by
      funext i
      simp only [stageRow]
      rw [stageRow_shift rk lam c t y h n]
      split_ifs
      · simp only [smul_eq_mul]
        ring
      · rfl

/-- The bath field is the affine field `T ↦ (-1 / τ) (T - T_amb)`. -/
private lemma bathField_eq (C G Tamb : ℝ) :
    bathField C G Tamb = fun _ x => -1 / thermalTimeConstant C G * (x - Tamb) := by
  funext t x
  rw [bathField, bathPower, thermalTimeConstant, neg_div, one_div_div]
  ring

/-- **The same model as the Euler budget.** The one-stage Runge–Kutta method on the bath field is
the explicit Euler step `bathEulerStep` of `PhysicalErrorBudgets`, from every time `t`; an
identity for all real parameters. -/
lemma bathField_eulerStep (C G Tamb t T dt : ℝ) :
    rkStep eulerRK (bathField C G Tamb) t T dt = bathEulerStep C G Tamb dt T := by
  rw [euler_step, bathField, bathEulerStep, smul_eq_mul]
  ring

/-- **Time independence.** The bath field does not depend on time, so one RK4 step from any time
`t` equals the step from time `0`; an identity for all real parameters. -/
lemma bathField_rk4_time_indep (C G Tamb t T dt : ℝ) :
    rkStep rk4 (bathField C G Tamb) t T dt = rkStep rk4 (bathField C G Tamb) 0 T dt := by
  change rkStep rk4 (fun _ x => (fun y => bathPower G Tamb y / C) x) t T dt =
    rkStep rk4 (fun _ x => (fun y => bathPower G Tamb y / C) x) 0 T dt
  simp only [rkStep, stage, stageRow_autonomous rk4 (fun y => bathPower G Tamb y / C) t 0 T dt]

/-- **Ambient-temperature shift.** One RK4 step of the bath field from `T` is `T_amb` plus the RK4
step of the linear decay `θ' = (-1 / τ) θ` from the excess `T - T_amb`; an identity for all real
parameters. -/
lemma bathField_rk4_shift (C G Tamb t T dt : ℝ) :
    rkStep rk4 (bathField C G Tamb) t T dt =
      Tamb + rkStep rk4 (fun _ y => -1 / thermalTimeConstant C G * y) 0 (T - Tamb) dt := by
  rw [bathField_rk4_time_indep, bathField_eq]
  simp only [rkStep, stage, stageRow_shift rk4 (-1 / thermalTimeConstant C G) Tamb 0 T dt,
    smul_eq_mul]
  ring

/-- **The step through the stability polynomial.** One RK4 step of size `dt` of the bath field
multiplies the excess `T - T_amb` by `R(z) = 1 + z + z² / 2 + z³ / 6 + z⁴ / 24` with
`z = (-1 / τ) dt`: `rk4_stability` after the shift. -/
lemma bathField_rk4_step (C G Tamb t T dt : ℝ) :
    rkStep rk4 (bathField C G Tamb) t T dt =
      Tamb + (T - Tamb) * (1 + -1 / thermalTimeConstant C G * dt +
        (-1 / thermalTimeConstant C G * dt) ^ 2 / 2 +
        (-1 / thermalTimeConstant C G * dt) ^ 3 / 6 +
        (-1 / thermalTimeConstant C G * dt) ^ 4 / 24) := by
  rw [bathField_rk4_shift, rk4_stability]

/-! ## J. Ten Runge–Kutta steps of size `τ / 10` -/

/-- **The actual RK4 recurrence at `dt = τ / 10`.** For `C, G > 0`, every real sequence with
`X 0 = T_amb + Δ` and `X (j + 1)` the RK4 step of size `τ / 10` from `X j` at the time `j τ / 10`
is `X j = T_amb + Δ (72387 / 80000) ^ j`. -/
lemma bathRK4_closed_form {C G : ℝ} (hC : 0 < C) (hG : 0 < G) {Tamb Δ : ℝ} {X : ℕ → ℝ}
    (h0 : X 0 = Tamb + Δ)
    (hstep : ∀ j : ℕ, X (j + 1) = rkStep rk4 (bathField C G Tamb)
      (j * (thermalTimeConstant C G / 10)) (X j) (thermalTimeConstant C G / 10))
    (j : ℕ) : X j = Tamb + Δ * (72387 / 80000) ^ j := by
  have hτ : thermalTimeConstant C G ≠ 0 := (div_pos hC hG).ne'
  have hz : -1 / thermalTimeConstant C G * (thermalTimeConstant C G / 10) = -1 / 10 := by
    field_simp
  induction j with
  | zero => simpa using h0
  | succ j ih =>
    rw [hstep, bathField_rk4_step, hz, ih, pow_succ]
    ring

/-- **Ten steps.** Under the hypotheses of `bathRK4_closed_form`, after ten RK4 steps of size
`τ / 10` the excess over the bath is `T_10 - T_amb = Δ (72387 / 80000) ^ 10`. -/
lemma bathRK4_tenStep_excess {C G : ℝ} (hC : 0 < C) (hG : 0 < G) {Tamb Δ : ℝ} {X : ℕ → ℝ}
    (h0 : X 0 = Tamb + Δ)
    (hstep : ∀ j : ℕ, X (j + 1) = rkStep rk4 (bathField C G Tamb)
      (j * (thermalTimeConstant C G / 10)) (X j) (thermalTimeConstant C G / 10)) :
    X 10 - Tamb = Δ * (72387 / 80000) ^ 10 := by
  rw [bathRK4_closed_form hC hG h0 hstep 10]
  ring

/-- The evaluated RK4 decay at `τ`: `(72387 / 80000) ^ 10 - exp (-1)` lies in `(0, 10⁻⁶)`. -/
private lemma rk4_decay_error_mem :
    0 < (72387 / 80000 : ℝ) ^ 10 - Real.exp (-1) ∧
      (72387 / 80000 : ℝ) ^ 10 - Real.exp (-1) < 1 / 10 ^ 6 := by
  have he1 := Real.exp_one_gt_d9
  have he2 := Real.exp_one_lt_d9
  have hpos := Real.exp_pos 1
  rw [Real.exp_neg, ← one_div]
  constructor
  · rw [sub_pos, div_lt_iff₀ hpos]
    norm_num at he1 ⊢
    linarith
  · rw [sub_lt_comm, lt_div_iff₀ hpos]
    norm_num at he2 ⊢
    linarith

/-- The ten-step error as the excess amplitude times the evaluated decay error. -/
private lemma bathRK4_tenStep_error_eq {C G : ℝ} (hC : 0 < C) (hG : 0 < G) {Tamb Δ : ℝ}
    {X : ℕ → ℝ} (h0 : X 0 = Tamb + Δ)
    (hstep : ∀ j : ℕ, X (j + 1) = rkStep rk4 (bathField C G Tamb)
      (j * (thermalTimeConstant C G / 10)) (X j) (thermalTimeConstant C G / 10)) :
    |X 10 - bathTrajectory C G Tamb Δ (thermalTimeConstant C G)| =
      |Δ| * ((72387 / 80000 : ℝ) ^ 10 - Real.exp (-1)) := by
  have hτ : thermalTimeConstant C G ≠ 0 := (div_pos hC hG).ne'
  rw [bathRK4_closed_form hC hG h0 hstep 10, bathTrajectory, neg_div, div_self hτ,
    show Tamb + Δ * (72387 / 80000) ^ 10 - (Tamb + Δ * Real.exp (-1)) =
      Δ * ((72387 / 80000) ^ 10 - Real.exp (-1)) by ring, abs_mul,
    abs_of_pos rk4_decay_error_mem.1]

/-- **Ten-step error bound.** For `C, G > 0` and `Δ ≠ 0`, the ten-step RK4 iterate at
`dt = τ / 10` differs from the exact temperature at `τ` by less than `|Δ| × 10⁻⁶`:
`|T_10 - T(τ)| < |Δ| / 10 ^ 6`. -/
lemma bathRK4_tenStep_error {C G : ℝ} (hC : 0 < C) (hG : 0 < G) {Tamb Δ : ℝ} (hΔ : Δ ≠ 0)
    {X : ℕ → ℝ} (h0 : X 0 = Tamb + Δ)
    (hstep : ∀ j : ℕ, X (j + 1) = rkStep rk4 (bathField C G Tamb)
      (j * (thermalTimeConstant C G / 10)) (X j) (thermalTimeConstant C G / 10)) :
    |X 10 - bathTrajectory C G Tamb Δ (thermalTimeConstant C G)| < |Δ| / 10 ^ 6 := by
  rw [bathRK4_tenStep_error_eq hC hG h0 hstep]
  calc |Δ| * ((72387 / 80000 : ℝ) ^ 10 - Real.exp (-1)) < |Δ| * (1 / 10 ^ 6) :=
        mul_lt_mul_of_pos_left rk4_decay_error_mem.2 (abs_pos.mpr hΔ)
    _ = |Δ| / 10 ^ 6 := by ring

/-- **The error is not zero.** Under the hypotheses of `bathRK4_tenStep_error`,
`|T_10 - T(τ)| > 0`: the RK4 factor `(72387 / 80000) ^ 10` exceeds the exact decay `exp (-1)`. -/
lemma bathRK4_tenStep_error_pos {C G : ℝ} (hC : 0 < C) (hG : 0 < G) {Tamb Δ : ℝ} (hΔ : Δ ≠ 0)
    {X : ℕ → ℝ} (h0 : X 0 = Tamb + Δ)
    (hstep : ∀ j : ℕ, X (j + 1) = rkStep rk4 (bathField C G Tamb)
      (j * (thermalTimeConstant C G / 10)) (X j) (thermalTimeConstant C G / 10)) :
    0 < |X 10 - bathTrajectory C G Tamb Δ (thermalTimeConstant C G)| := by
  rw [bathRK4_tenStep_error_eq hC hG h0 hstep]
  exact mul_pos (abs_pos.mpr hΔ) rk4_decay_error_mem.1

/-! ## K. The unstable Runge–Kutta step -/

/-- **The unstable step of a stable bath.** For `C, G > 0` the exact excess never exceeds its
initial size, `|T(t) - T_amb| ≤ |Δ|` for `t ≥ 0`, but RK4 with `dt = 3 τ` multiplies the excess by
`R(-3) = 11 / 8`: `X j = T_amb + Δ (11 / 8) ^ j` and `|X j - T_amb| = (11 / 8) ^ j |Δ|`. -/
lemma bathRK4_threeTau {C G : ℝ} (hC : 0 < C) (hG : 0 < G) {Tamb Δ : ℝ} {X : ℕ → ℝ}
    (h0 : X 0 = Tamb + Δ)
    (hstep : ∀ j : ℕ, X (j + 1) = rkStep rk4 (bathField C G Tamb)
      (j * (3 * thermalTimeConstant C G)) (X j) (3 * thermalTimeConstant C G)) :
    (∀ t, 0 ≤ t → |bathTrajectory C G Tamb Δ t - Tamb| ≤ |Δ|) ∧
      ∀ j, X j = Tamb + Δ * (11 / 8) ^ j ∧ |X j - Tamb| = (11 / 8) ^ j * |Δ| := by
  have hτ : 0 < thermalTimeConstant C G := div_pos hC hG
  have hz : -1 / thermalTimeConstant C G * (3 * thermalTimeConstant C G) = -3 := by
    field_simp
  have hX : ∀ j, X j = Tamb + Δ * (11 / 8) ^ j := by
    intro j
    induction j with
    | zero => simpa using h0
    | succ j ih =>
      rw [hstep, bathField_rk4_step, hz, ih, pow_succ]
      ring
  refine ⟨fun t ht => ?_, fun j => ⟨hX j, ?_⟩⟩
  · rw [bathTrajectory, add_sub_cancel_left, abs_mul, Real.abs_exp]
    have h1 : Real.exp (-t / thermalTimeConstant C G) ≤ 1 :=
      Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by linarith) hτ.le)
    nlinarith [abs_nonneg Δ]
  · rw [hX j, add_sub_cancel_left, abs_mul, abs_pow, mul_comm]
    norm_num

end RungeKuttaComparison

/-! ## L. Defects through the actual Euler recurrence -/

open Finset

/-- The actual residual of a computed temperature sequence `Y` in the Euler recurrence at
`dt = τ / 10`: `η_j = Y (j + 1) - (Y j + (τ / 10) Q(Y j) / C)`, the amount by which the computed
step `j` misses one exact Euler step. It is computed from `Y`, in the temperature unit of `Y`. -/
noncomputable def bathEulerResidual (C G Tamb : ℝ) (Y : ℕ → ℝ) (j : ℕ) : ℝ :=
  Y (j + 1) - bathEulerStep C G Tamb (thermalTimeConstant C G / 10) (Y j)

/-- The ten-step error budget of a computed temperature sequence `Y` against the exact trajectory
from `T_amb + Δ`: the propagated initial error, the weighted actual residuals and the truncation
term `|Δ| / 10` of the exact Euler recurrence, three separate terms in the temperature unit. -/
noncomputable def tenStepErrorBudget (C G Tamb Δ : ℝ) (Y : ℕ → ℝ) : ℝ :=
  (9 / 10) ^ 10 * |Y 0 - (Tamb + Δ)| +
    ∑ j ∈ range 10, (9 / 10) ^ (9 - j) * |bathEulerResidual C G Tamb Y j| + |Δ| / 10

/-- **The actual step has slope `9 / 10`.** For `C, G > 0`, one Euler step of size `τ / 10` maps
the difference of two temperatures to `9 / 10` of it. -/
lemma bathEulerStep_sub_tenth {C G : ℝ} (hC : 0 < C) (hG : 0 < G) (Tamb T X : ℝ) :
    bathEulerStep C G Tamb (thermalTimeConstant C G / 10) T -
        bathEulerStep C G Tamb (thermalTimeConstant C G / 10) X = 9 / 10 * (T - X) := by
  have hC' := hC.ne'
  have hG' := hG.ne'
  unfold bathEulerStep bathPower thermalTimeConstant
  field_simp
  ring

/-- **The defect recurrence.** For `C, G > 0`, the exact Euler recurrence `X` at `dt = τ / 10`
and any computed sequence `Y`, the defect `Y - X` obeys `e_{j+1} = (9 / 10) e_j + η_j` with the
actual residual `η_j` of `Y`. -/
lemma defect_recurrence {C G : ℝ} (hC : 0 < C) (hG : 0 < G) {Tamb : ℝ} {X : ℕ → ℝ}
    (hstep : ∀ j, X (j + 1) = bathEulerStep C G Tamb (thermalTimeConstant C G / 10) (X j))
    (Y : ℕ → ℝ) (j : ℕ) :
    Y (j + 1) - X (j + 1) = 9 / 10 * (Y j - X j) + bathEulerResidual C G Tamb Y j := by
  have h := bathEulerStep_sub_tenth hC hG Tamb (Y j) (X j)
  rw [hstep j]
  unfold bathEulerResidual
  linarith

/-- **Three-term ten-step error budget.** For `C, G > 0`, the exact Euler recurrence `X` at
`dt = τ / 10` from `X 0 = T_amb + Δ` and any computed sequence `Y`, the computed temperature
after ten steps is within the budget of the exact trajectory at `τ`: the propagated initial error,
the weighted actual residuals and the truncation term `|Δ| / 10`. -/
lemma bathEuler_total_error {C G : ℝ} (hC : 0 < C) (hG : 0 < G) {Tamb Δ : ℝ} {X : ℕ → ℝ}
    (h0 : X 0 = Tamb + Δ)
    (hstep : ∀ j, X (j + 1) = bathEulerStep C G Tamb (thermalTimeConstant C G / 10) (X j))
    (Y : ℕ → ℝ) :
    |Y 10 - bathTrajectory C G Tamb Δ (thermalTimeConstant C G)| ≤
      tenStepErrorBudget C G Tamb Δ Y := by
  have hrec : ∀ j < 10, (fun i => Y i - X i) (j + 1) =
      9 / 10 * (fun i => Y i - X i) j + bathEulerResidual C G Tamb Y j :=
    fun j _ => defect_recurrence hC hG hstep Y j
  have hdef := MathlibExt.Analysis.ODE.TimeStepping.tenStep_defect_le
    (e := fun i => Y i - X i) (η := bathEulerResidual C G Tamb Y) hrec
  have htrunc := bathEuler_tenStep_error hC hG h0 hstep
  have htri := abs_sub_le (Y 10) (X 10) (bathTrajectory C G Tamb Δ (thermalTimeConstant C G))
  simp only [h0] at hdef
  unfold tenStepErrorBudget
  linarith

/-- **Temperature units.** A change of temperature unit `T ↦ k T + c` with `k > 0` maps every
temperature, the bath `T_amb` and the computed sequence `Y`, by `T ↦ k T + c`, multiplies every
temperature difference, the initial excess `Δ`, by `k`, and divides the per-degree coefficients,
the heat capacity `C` and the conductance `G`, by `k`; the time constant `τ = C / G` is unchanged.
Each residual and the whole budget are then multiplied by `k`: all three terms are temperature
differences in one unit. -/
lemma tenStepErrorBudget_tempUnit {k : ℝ} (hk : 0 < k) (c C G Tamb Δ : ℝ) (Y : ℕ → ℝ) :
    (∀ j, bathEulerResidual (C / k) (G / k) (k * Tamb + c) (fun i => k * Y i + c) j =
        k * bathEulerResidual C G Tamb Y j) ∧
      tenStepErrorBudget (C / k) (G / k) (k * Tamb + c) (k * Δ) (fun i => k * Y i + c) =
        k * tenStepErrorBudget C G Tamb Δ Y := by
  have hk0 : k ≠ 0 := hk.ne'
  have hτ : thermalTimeConstant (C / k) (G / k) = thermalTimeConstant C G := by
    unfold thermalTimeConstant
    rw [div_div_div_cancel_right₀ hk0]
  have hres : ∀ j, bathEulerResidual (C / k) (G / k) (k * Tamb + c) (fun i => k * Y i + c) j =
      k * bathEulerResidual C G Tamb Y j := by
    intro j
    unfold bathEulerResidual bathEulerStep
    rw [hτ]
    unfold bathPower
    rcases eq_or_ne C 0 with rfl | hC
    · simp
      ring
    · field_simp
      ring
  refine ⟨hres, ?_⟩
  unfold tenStepErrorBudget
  simp only [hres]
  have h1 : k * Y 0 + c - (k * Tamb + c + k * Δ) = k * (Y 0 - (Tamb + Δ)) := by ring
  have hsum : ∑ j ∈ range 10, (9 / 10 : ℝ) ^ (9 - j) * |k * bathEulerResidual C G Tamb Y j| =
      k * ∑ j ∈ range 10, (9 / 10 : ℝ) ^ (9 - j) * |bathEulerResidual C G Tamb Y j| := by
    rw [mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [abs_mul, abs_of_pos hk]
    ring
  rw [h1, hsum, abs_mul, abs_mul, abs_of_pos hk]
  ring

end PhysicalErrorBudgets

end
