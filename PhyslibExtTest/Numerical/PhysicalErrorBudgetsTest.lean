/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Numerical.PhysicalErrorBudgets
import Mathlib.Tactic.NormNum

/-!
# Tests for `PhyslibExt.Numerical.PhysicalErrorBudgets`

* a nonunit bar `EA = 2`, `L = 3`, `q = 4` on two uniform cells, keeping both the coordinate and
  the amplitude scaling;
* the same bar: the amplitude is nonzero, the reconstruction is fixed at both ends, and the
  physical error obeys the mesh estimates;
* the zero load, treated without the inverse amplitude map;
* a body of heat capacity `500` coupled through `G = 5` to a bath at `300` (`τ = 100`), started
  at `350`: ten Euler steps of size `10` give `T_10 = 300 + 50 (9 / 10) ^ 10`, with
  `0 < |T_10 - T(100)| ≤ 5`;
* the same body: its trajectory solves `C T' = Q(T)` and the one-node storage law, while a node
  without a source keeps its temperature;
* the same body in minutes and in seconds, the step `τ / 10` entered in seconds against `τ` in
  minutes, and the unstable step `3 τ`;
* the same body under the classical Runge–Kutta method: the one-stage method is the Euler step,
  the RK4 step from `350` does not depend on the start time and multiplies the excess `50` by
  `72387 / 80000`, ten steps of size `10` give `T_10 = 300 + 50 (72387 / 80000) ^ 10` with
  `0 < |T_10 - T(100)| < 50 / 10 ^ 6`, and the step `3 τ` multiplies the excess by `11 / 8`;
* defects through the actual recurrence: a constant offset of `1 / 2` in the computed temperatures
  has the residual `1 / 20` at every step and the budget `1 / 2 + 5`, the budget in degrees
  Fahrenheit, with the heat capacity and the conductance converted per degree Fahrenheit, is
  `9 / 5` times the budget in degrees Celsius, and dropping an observed residual undercuts the
  actual error.
-/

@[expose] public section

namespace PhyslibExtTest.Numerical.PhysicalErrorBudgets

open _root_.PhysicalErrorBudgets

/-! ## A. A nonunit bar on two cells -/

-- Nonunit fixture `EA = 2`, `L = 3`, `q = 4`, keeping both the coordinate and the amplitude
-- scaling: `α = 9`, quarter-point error `9 / 16`, energy `9 / 2`, squared `L²` error `81 / 160`.
example :
    barAmplitude 2 3 4 = 9 ∧ physicalError twoCells 2 3 4 (3 / 4) = 9 / 16 ∧
      ∫ x in (0 : ℝ)..3, 2 * deriv (physicalError twoCells 2 3 4) x ^ 2 = 9 / 2 ∧
      ∫ x in (0 : ℝ)..3, physicalError twoCells 2 3 4 x ^ 2 = 81 / 160 := by
  have hα : barAmplitude 2 3 4 = 9 := by norm_num [barAmplitude]
  obtain ⟨h1, h2, h3⟩ := physicalError_twoCells (L := 3) (by norm_num) 2 4
  refine ⟨hα, ?_, ?_, ?_⟩
  · rw [h1, hα]
  · rw [h2, hα]
    norm_num
  · rw [h3, hα]
    norm_num

-- The amplitude of that bar is nonzero, so the normalization can be inverted.
example : barAmplitude 2 3 4 ≠ 0 :=
  (barAmplitude_ne_zero_iff (by norm_num) (by norm_num) 4).2 (by norm_num)

-- Its reconstruction is fixed at both ends of `[0, 3]`.
example : physicalP1 twoCells 2 3 4 0 = 0 ∧ physicalP1 twoCells 2 3 4 3 = 0 :=
  physicalP1_zero_and_length twoCells (by norm_num) 2 4

-- The energy and `L²` errors obey the physical mesh estimates.
example :
    ∫ x in (0 : ℝ)..3, 2 * deriv (physicalError twoCells 2 3 4) x ^ 2 ≤
        2 / 3 * barAmplitude 2 3 4 ^ 2 * (4 * (twoCells.mesh / Real.pi) ^ 2) ∧
      ∫ x in (0 : ℝ)..3, physicalError twoCells 2 3 4 x ^ 2 ≤
        3 * barAmplitude 2 3 4 ^ 2 * (4 * (twoCells.mesh / Real.pi) ^ 4) :=
  ⟨integral_energy_physicalError_le_mesh twoCells (by norm_num) (by norm_num) 4,
    integral_sq_physicalError_le_mesh twoCells (by norm_num) 2 4⟩

/-! ## B. Zero load -/

-- With `q = 0` the error vanishes everywhere, and the inverse amplitude map does not recover
-- the unit profile.
example :
    physicalError twoCells 2 3 0 (3 / 4) = 0 ∧
      (barAmplitude 2 3 0)⁻¹ * Elasticity.PrismaticMembers.axialDisplacement 2 3 0 (3 * (1 / 2)) ≠
        unitProfile (1 / 2) :=
  ⟨(zero_load twoCells 2 3).2.2.2 (3 / 4), zero_load_inverse_ne 2 3⟩

/-! ## C. A body cooling in a fixed bath -/

/-- **Nonzero temperature excess.** A body of heat capacity `500` coupled through `G = 5` to a
bath at `300` has `τ = 100`. Started at `350` (`Δ = 50`), ten Euler steps of `10` (that is
`τ / 10`, in the same time unit as `τ`) give `T_10 = 300 + 50 (9 / 10) ^ 10`, and
`0 < |T_10 - T(100)| ≤ 5`. -/
lemma bathEuler_fixture {X : ℕ → ℝ} (h0 : X 0 = 350)
    (hstep : ∀ j, X (j + 1) = bathEulerStep 500 5 300 10 (X j)) :
    X 10 = 300 + 50 * (9 / 10) ^ 10 ∧
      0 < |X 10 - bathTrajectory 500 5 300 50 100| ∧
      |X 10 - bathTrajectory 500 5 300 50 100| ≤ 5 := by
  have hτ : thermalTimeConstant 500 5 = 100 := by norm_num [thermalTimeConstant]
  have h0' : X 0 = 300 + 50 := by rw [h0]; norm_num
  have hstep' : ∀ j, X (j + 1) =
      bathEulerStep 500 5 300 (thermalTimeConstant 500 5 / 10) (X j) := by
    intro j
    rw [hτ, hstep]
    norm_num
  have herr := bathEuler_tenStep_error (by norm_num) (by norm_num) h0' hstep'
  have hpos := bathEuler_tenStep_error_pos (by norm_num) (by norm_num) (by norm_num) h0' hstep'
  rw [hτ] at herr hpos
  refine ⟨bathEuler_closed_form (by norm_num) (by norm_num) h0' hstep' 10, hpos, ?_⟩
  norm_num at herr
  exact herr

/-! ## D. The bath trajectory and the one-node law -/

-- The trajectory of the body starts at `350` and satisfies `T' = Q(T) / C`: at `t = 0` the bath
-- power is `-5 · 50 = -250` and `T' = -250 / 500 = -1 / 2`; the stored heat `500 T` has the rate
-- `Q(T) = -250` there.
example :
    bathTrajectory 500 5 300 50 0 = 350 ∧
      HasDerivAt (bathTrajectory 500 5 300 50) (-1 / 2) 0 ∧
      HasDerivAt (fun s => 500 * bathTrajectory 500 5 300 50 s) (-250) 0 := by
  obtain ⟨h0, hd⟩ := bathTrajectory_solves (C := 500) (G := 5) (by norm_num) (by norm_num) 300 50
  have hQ : bathPower 5 300 (bathTrajectory 500 5 300 50 0) = -250 := by
    rw [h0]
    norm_num [bathPower]
  refine ⟨by rw [h0]; norm_num, ?_, ?_⟩
  · have h := hd 0
    rw [hQ] at h
    convert h using 1
    norm_num
  · have h := bathTrajectory_storage (C := 500) (G := 5) (by norm_num) (by norm_num) 300 50 0
    rwa [hQ] at h

-- A node of capacity `500` without a source (`500 T' = 0`) keeps its temperature up to `t = 1000`,
-- while the body coupled to the bath has left its initial temperature by then.
example {T dT : ℝ → ℝ} (hT : ∀ t, HasDerivAt T (dT t) t) (hbal : ∀ t, 500 * dT t = 0) :
    T 1000 = T 0 ∧ bathTrajectory 500 5 300 50 1000 ≠ bathTrajectory 500 5 300 50 0 := by
  refine ⟨oneNode_noSource_const (by norm_num) hT hbal 1000, ?_⟩
  have h : Real.exp (-1000 / thermalTimeConstant 500 5) < 1 :=
    Real.exp_lt_one_iff.mpr (by norm_num [thermalTimeConstant])
  intro heq
  simp only [bathTrajectory, neg_zero, zero_div, Real.exp_zero, mul_one] at heq
  linarith

/-! ## E. Time units and the unstable step -/

-- The same body in minutes and in seconds: with the conductance `300` per minute, `τ = 5 / 3`
-- minutes; in seconds (`k = 60`) the conductance is `300 / 60 = 5` per second and
-- `τ = 60 · (5 / 3) = 100`. The step `τ / 10`, `1 / 6` minute or `10` seconds, takes the body
-- from `350` to `345` in both units.
example :
    thermalTimeConstant 500 (300 / 60) = 60 * thermalTimeConstant 500 300 ∧
      thermalTimeConstant 500 300 = 5 / 3 ∧
      bathEulerStep 500 (300 / 60) 300 (60 * (1 / 6)) 350 =
        bathEulerStep 500 300 300 (1 / 6) 350 ∧
      bathEulerStep 500 300 300 (1 / 6) 350 = 345 := by
  obtain ⟨hτ, hstep⟩ := bathEulerStep_timeUnit (by norm_num : (0 : ℝ) < 60) 500 300 300 (1 / 6) 350
  exact ⟨hτ, by norm_num [thermalTimeConstant], hstep, by norm_num [bathEulerStep, bathPower]⟩

-- Mismatched units: with `τ = 5 / 3` minutes, the step `τ / 10` entered as its value in seconds,
-- `10`, is `60` times too large. It multiplies the excess `50` by `-5`: the body at `350` jumps to
-- `50`, far below the bath at `300`, instead of moving to `345`.
example : bathEulerStep 500 300 300 10 350 = 50 ∧ bathEulerStep 500 300 300 (1 / 6) 350 = 345 := by
  have h := bathEulerStep_minutes_seconds (C := 500) (G := 300) (by norm_num) (by norm_num) 300 50
  have hdt : (60 : ℝ) * (thermalTimeConstant 500 300 / 10) = 10 := by
    norm_num [thermalTimeConstant]
  rw [hdt] at h
  refine ⟨?_, by norm_num [bathEulerStep, bathPower]⟩
  rw [show (350 : ℝ) = 300 + 50 by norm_num, h]
  norm_num

-- The unstable step of the stable bath: with `τ = 100`, the step `3 τ = 300` multiplies the excess
-- by `-2`, giving `350`, `200`, `500`, ..., so after ten steps the excess is `2 ^ 10 · 50 = 51200`,
-- while the exact excess `50 exp (-t / 100)` never exceeds `50`.
example {X : ℕ → ℝ} (h0 : X 0 = 350)
    (hstep : ∀ j, X (j + 1) = bathEulerStep 500 5 300 300 (X j)) :
    X 1 = 200 ∧ X 2 = 500 ∧ |X 10 - 300| = 51200 ∧
      |bathTrajectory 500 5 300 50 1000 - 300| ≤ 50 := by
  have hτ : thermalTimeConstant 500 5 = 100 := by norm_num [thermalTimeConstant]
  have h0' : X 0 = 300 + 50 := by rw [h0]; norm_num
  have hstep' : ∀ j, X (j + 1) =
      bathEulerStep 500 5 300 (3 * thermalTimeConstant 500 5) (X j) := by
    intro j
    rw [hτ, hstep]
    norm_num
  obtain ⟨hexact, hX⟩ := bathEuler_threeTau (by norm_num) (by norm_num) h0' hstep'
  refine ⟨?_, ?_, ?_, (hexact 1000 (by norm_num)).trans_eq (by norm_num)⟩
  · rw [(hX 1).1]
    norm_num
  · rw [(hX 2).1]
    norm_num
  · rw [(hX 10).2]
    norm_num


/-! ## F. Ten classical Runge–Kutta steps on the same body -/

open MathlibExt.Analysis.ODE.RungeKutta

/-- **Nonzero temperature excess and exact rational amplification.** A body of heat capacity
`500` coupled through `G = 5` to a bath at `300` has `τ = 100`. Started at `350` (`Δ = 50`), ten
RK4 steps of `10` (that is `τ / 10`, in the same time unit as `τ`) at the times `10 j` give
`T_10 = 300 + 50 (72387 / 80000) ^ 10`, and `0 < |T_10 - T(100)| < 50 / 10 ^ 6`. -/
lemma bathRK4_fixture {X : ℕ → ℝ} (h0 : X 0 = 350)
    (hstep : ∀ j : ℕ, X (j + 1) = rkStep rk4 (bathField 500 5 300) (j * 10) (X j) 10) :
    X 10 = 300 + 50 * (72387 / 80000) ^ 10 ∧
      0 < |X 10 - bathTrajectory 500 5 300 50 100| ∧
      |X 10 - bathTrajectory 500 5 300 50 100| < 50 / 10 ^ 6 := by
  have hτ : thermalTimeConstant 500 5 = 100 := by norm_num [thermalTimeConstant]
  have h0' : X 0 = 300 + 50 := by rw [h0]; norm_num
  have hstep' : ∀ j : ℕ, X (j + 1) = rkStep rk4 (bathField 500 5 300)
      (j * (thermalTimeConstant 500 5 / 10)) (X j) (thermalTimeConstant 500 5 / 10) := by
    intro j
    rw [hτ, show (100 : ℝ) / 10 = 10 by norm_num]
    exact hstep j
  have herr := bathRK4_tenStep_error (by norm_num) (by norm_num) (by norm_num) h0' hstep'
  have hpos := bathRK4_tenStep_error_pos (by norm_num) (by norm_num) (by norm_num) h0' hstep'
  rw [hτ] at herr hpos
  refine ⟨bathRK4_closed_form (by norm_num) (by norm_num) h0' hstep' 10, hpos, ?_⟩
  simpa using herr

-- The one-stage method on the bath field is the Euler step of section C: from `350` the step `10`
-- gives `345`.
example : rkStep eulerRK (bathField 500 5 300) 0 350 10 = 345 := by
  rw [bathField_eulerStep]
  norm_num [bathEulerStep, bathPower]

-- The RK4 step from `350` does not depend on the start time; it is `300` plus the step of the
-- linear decay `θ' = -θ / 100` from the excess `50`, which multiplies the excess by
-- `R(-1 / 10) = 72387 / 80000`.
example :
    rkStep rk4 (bathField 500 5 300) 70 350 10 = rkStep rk4 (bathField 500 5 300) 0 350 10 ∧
      rkStep rk4 (bathField 500 5 300) 70 350 10 =
        300 + rkStep rk4 (fun _ y => -1 / thermalTimeConstant 500 5 * y) 0 50 10 ∧
      rkStep rk4 (bathField 500 5 300) 70 350 10 = 300 + 50 * (72387 / 80000) := by
  refine ⟨bathField_rk4_time_indep 500 5 300 70 350 10, ?_, ?_⟩
  · rw [bathField_rk4_shift]
    norm_num
  · rw [bathField_rk4_step]
    norm_num [thermalTimeConstant]

-- After ten steps of size `10` the excess over the bath is `50 (72387 / 80000) ^ 10`.
example {X : ℕ → ℝ} (h0 : X 0 = 350)
    (hstep : ∀ j : ℕ, X (j + 1) = rkStep rk4 (bathField 500 5 300) (j * 10) (X j) 10) :
    X 10 - 300 = 50 * (72387 / 80000) ^ 10 := by
  have hτ : thermalTimeConstant 500 5 = 100 := by norm_num [thermalTimeConstant]
  have h0' : X 0 = 300 + 50 := by rw [h0]; norm_num
  have hstep' : ∀ j : ℕ, X (j + 1) = rkStep rk4 (bathField 500 5 300)
      (j * (thermalTimeConstant 500 5 / 10)) (X j) (thermalTimeConstant 500 5 / 10) := by
    intro j
    rw [hτ, show (100 : ℝ) / 10 = 10 by norm_num]
    exact hstep j
  exact bathRK4_tenStep_excess (by norm_num) (by norm_num) h0' hstep'

-- The unstable RK4 step of the stable bath: with `τ = 100`, the step `3 τ = 300` multiplies the
-- excess by `R(-3) = 11 / 8`, giving `350`, `2950 / 8`, ..., so after ten steps the excess is
-- `(11 / 8) ^ 10 · 50`, while the exact excess never exceeds `50`.
example {X : ℕ → ℝ} (h0 : X 0 = 350)
    (hstep : ∀ j : ℕ, X (j + 1) = rkStep rk4 (bathField 500 5 300) (j * 300) (X j) 300) :
    X 1 = 2950 / 8 ∧ |X 10 - 300| = (11 / 8) ^ 10 * 50 ∧
      |bathTrajectory 500 5 300 50 1000 - 300| ≤ 50 := by
  have hτ : thermalTimeConstant 500 5 = 100 := by norm_num [thermalTimeConstant]
  have h0' : X 0 = 300 + 50 := by rw [h0]; norm_num
  have hstep' : ∀ j : ℕ, X (j + 1) = rkStep rk4 (bathField 500 5 300)
      (j * (3 * thermalTimeConstant 500 5)) (X j) (3 * thermalTimeConstant 500 5) := by
    intro j
    rw [hτ, show (3 : ℝ) * 100 = 300 by norm_num]
    exact hstep j
  obtain ⟨hexact, hX⟩ := bathRK4_threeTau (by norm_num) (by norm_num) h0' hstep'
  refine ⟨?_, ?_, (hexact 1000 (by norm_num)).trans_eq (by norm_num)⟩
  · rw [(hX 1).1]
    norm_num
  · rw [(hX 10).2]
    norm_num

/-! ## G. Defects through the actual Euler recurrence -/

open Finset

/-- **Observed residuals cannot be replaced by zero.** For `C = G = 1`, `T_amb = 0`, `Δ = 1`, a
computed sequence equal to the exact Euler iterates except for a last step off by `1` has the
residual `1` at step `9` and `0` before; dropping that residual from the budget leaves
`(9 / 10) ^ 10 |Y 0 - 1| + 1 / 10`, which is below the actual error. -/
lemma bathEuler_residual_not_zero {Y : ℕ → ℝ} (hY : ∀ j ≤ 9, Y j = (9 / 10) ^ j)
    (hY10 : Y 10 = (9 / 10) ^ 10 + 1) :
    (∀ j < 9, bathEulerResidual 1 1 0 Y j = 0) ∧ bathEulerResidual 1 1 0 Y 9 = 1 ∧
      (9 / 10) ^ 10 * |Y 0 - (0 + 1)| + |(1 : ℝ)| / 10 <
        |Y 10 - bathTrajectory 1 1 0 1 (thermalTimeConstant 1 1)| := by
  have hτ : thermalTimeConstant 1 1 = 1 := by norm_num [thermalTimeConstant]
  refine ⟨fun j hj => ?_, ?_, ?_⟩
  · unfold bathEulerResidual bathEulerStep bathPower
    rw [hτ, hY (j + 1) (by omega), hY j (by omega), pow_succ]
    ring
  · unfold bathEulerResidual bathEulerStep bathPower
    rw [hτ, hY10, hY 9 (by norm_num)]
    ring
  · rw [hY 0 (by norm_num), hY10]
    unfold bathTrajectory
    rw [hτ]
    have he : Real.exp (-1 / 1) < 1 := by
      rw [Real.exp_lt_one_iff]
      norm_num
    have hp : (0 : ℝ) < (9 / 10) ^ 10 := by positivity
    have hpos : 0 < (9 / 10 : ℝ) ^ 10 + 1 - (0 + 1 * Real.exp (-1 / 1)) := by linarith
    rw [abs_of_pos hpos]
    norm_num
    linarith

-- One step of size `10` of the body in the bath maps the temperatures `350` and `340` to points
-- `9` apart.
example :
    bathEulerStep 500 5 300 (thermalTimeConstant 500 5 / 10) 350 -
      bathEulerStep 500 5 300 (thermalTimeConstant 500 5 / 10) 340 = 9 := by
  rw [bathEulerStep_sub_tenth (by norm_num) (by norm_num)]
  norm_num

-- A constant offset of `1 / 2` in the computed temperatures of the body in the bath: the residual
-- is `1 / 20` at every step, the budget is `1 / 2 + 5`, and the computed temperature after ten
-- steps is within it.
example {X : ℕ → ℝ} (h0 : X 0 = 300 + 50)
    (hstep : ∀ j, X (j + 1) = bathEulerStep 500 5 300 (thermalTimeConstant 500 5 / 10) (X j)) :
    (∀ j, bathEulerResidual 500 5 300 (fun i => X i + 1 / 2) j = 1 / 20) ∧
      tenStepErrorBudget 500 5 300 50 (fun i => X i + 1 / 2) = 11 / 2 ∧
      |X 10 + 1 / 2 - bathTrajectory 500 5 300 50 (thermalTimeConstant 500 5)| ≤ 11 / 2 := by
  have hres : ∀ j, bathEulerResidual 500 5 300 (fun i => X i + 1 / 2) j = 1 / 20 := by
    intro j
    have h := defect_recurrence (by norm_num) (by norm_num) hstep (fun i => X i + 1 / 2) j
    linarith
  have hb : tenStepErrorBudget 500 5 300 50 (fun i => X i + 1 / 2) = 11 / 2 := by
    simp only [tenStepErrorBudget, hres, h0]
    norm_num [sum_range_succ]
  refine ⟨hres, hb, ?_⟩
  have h := bathEuler_total_error (by norm_num) (by norm_num) h0 hstep (fun i => X i + 1 / 2)
  rwa [hb] at h

-- The budget in degrees Fahrenheit (`k = 9 / 5`, `c = 32`), with the heat capacity `500` and the
-- conductance `5` per degree Celsius converted to `500 / (9 / 5) = 2500 / 9` and
-- `5 / (9 / 5) = 25 / 9` per degree Fahrenheit, is `9 / 5` times the budget in degrees Celsius.
example (Y : ℕ → ℝ) :
    tenStepErrorBudget (2500 / 9) (25 / 9) (9 / 5 * 27 + 32) (9 / 5 * 50)
        (fun i => 9 / 5 * Y i + 32) =
      9 / 5 * tenStepErrorBudget 500 5 27 50 Y := by
  have h := (tenStepErrorBudget_tempUnit (k := 9 / 5) (by norm_num) 32 500 5 27 50 Y).2
  rwa [show (500 : ℝ) / (9 / 5) = 2500 / 9 by norm_num,
    show (5 : ℝ) / (9 / 5) = 25 / 9 by norm_num] at h

end PhyslibExtTest.Numerical.PhysicalErrorBudgets

end
