/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import MathlibExt.Analysis.ODE.GreensOperator

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Beam modes: simply supported mode in physical units

## i. Overview

The `k`-th simply supported Euler-Bernoulli beam mode
`w(x, t) = sin(kπx / L) * cos(ωt)` with modal frequency
`ω_k = (kπ / L)^2 * √(EI / ρA)`: it solves
`ρA * w_tt + EI * w_xxxx = 0` with `w = w_xx = 0` at both ends, and
its total energy (kinetic plus bending, integrated over `[0, L]`) is
the constant `(L / 4) * EI * (kπ / L)^4`. Uniform beam, unit mode
amplitude; no mode-completeness or first-mode claim is made.

## ii. Key results

- `BeamModes.beamMode_beamEquation`: the mode at its modal frequency
  satisfies the beam equation at every `x, t`.
- `BeamModes.beamModeEnergy_conserved`: the integrated energy is
  constant in time.
- `BeamModes.orthonormal_tail_norm_sq_le`: for a finite modal sum
  in an orthonormal family, the squared norm of the tail modes
  `N + 1 .. K` is at most that of the full sum `1 .. K` (finite
  Parseval plus nonnegativity of each modal contribution).
- `BeamModes.sineBasis_tail_norm_sq_le`: that tail bound for the
  existing sine Hilbert basis on `L²([0, 1])`.

## iii. Table of contents

- A. The simply supported mode and its energy
- B. Finite-mode truncation tail bound

## iv. References

- The Dirichlet sine eigenfunctions of
  `MathlibExt.Analysis.ODE.DirichletSineEigenfunctions`, whose
  differential identities this physical-units mode instantiates with
  explicit `EI`, `ρA`, and `L`.
- S. S. Rao, *Mechanical Vibrations*, 6th ed., Pearson (2017):
  the Euler-Bernoulli beam equation `ρA * w_tt + EI * w_xxxx = 0`,
  the simply supported modal frequencies
  `ω_k = (kπ / L)^2 * √(EI / ρA)`, and the kinetic/bending energy
  expressions used here.

## A. The simply supported mode and its energy

-/

@[expose] public section

namespace BeamModes

/-- The `k`-th simply supported beam mode in physical units:
`w(x, t) = sin(kπx / L) * cos(ωt)` for `k ≥ 1`. -/
noncomputable def beamMode (k : ℕ+) (L ω x t : ℝ) : ℝ :=
  Real.sin ((k : ℝ) * Real.pi * x / L) * Real.cos (ω * t)

/-- Modal frequency `ω_k = (kπ / L)^2 * √(EI / ρA)`. -/
noncomputable def beamFreq (EI ρA L : ℝ) (k : ℕ+) : ℝ :=
  ((k : ℝ) * Real.pi / L) ^ 2 * Real.sqrt (EI / ρA)

/-- Left support value: `w(0, t) = 0`. -/
lemma beamMode_zero_left (k : ℕ+) (L ω t : ℝ) : beamMode k L ω 0 t = 0 := by
  simp [beamMode]

/-- Right support value: `w(L, t) = 0` for `L ≠ 0`. -/
lemma beamMode_zero_right (k : ℕ+) {L : ℝ} (hL : L ≠ 0) (ω t : ℝ) :
    beamMode k L ω L t = 0 := by
  unfold beamMode
  have hLL : (k : ℝ) * Real.pi * L / L = ((k.val : ℕ) : ℝ) * Real.pi := by
    field_simp
  rw [hLL]
  simp [Real.sin_nat_mul_pi]

/-- Second spatial derivative: `w_xx = -(kπ / L)^2 * w`. -/
lemma beamMode_iteratedDeriv_two (k : ℕ+) (L ω x t : ℝ) :
    iteratedDeriv 2 (fun y : ℝ => beamMode k L ω y t) x =
      -((k : ℝ) * Real.pi / L) ^ 2 * beamMode k L ω x t := by
  have hlin : ∀ y : ℝ, deriv (fun y : ℝ => (k : ℝ) * Real.pi * y / L) y =
      (k : ℝ) * Real.pi / L := by
    intro y
    simp
  have h1 : deriv (fun y : ℝ => beamMode k L ω y t) =
      fun y => Real.cos ((k : ℝ) * Real.pi * y / L) * ((k : ℝ) * Real.pi / L) *
        Real.cos (ω * t) := by
    funext y
    unfold beamMode
    rw [deriv_mul_const_field]
    rw [deriv_sin (by fun_prop)]
    rw [hlin y]
  have h2 : deriv (fun y : ℝ => Real.cos ((k : ℝ) * Real.pi * y / L) *
      ((k : ℝ) * Real.pi / L) * Real.cos (ω * t)) x =
      -((k : ℝ) * Real.pi / L) ^ 2 * beamMode k L ω x t := by
    rw [deriv_mul_const_field]
    rw [deriv_mul_const_field]
    rw [deriv_cos (by fun_prop)]
    rw [hlin x]
    unfold beamMode
    ring
  have hIter : iteratedDeriv 2 (fun y : ℝ => beamMode k L ω y t) x =
      deriv (deriv (fun y : ℝ => beamMode k L ω y t)) x := by
    have hsucc : iteratedDeriv 2 (fun y : ℝ => beamMode k L ω y t) =
        deriv (iteratedDeriv 1 (fun y : ℝ => beamMode k L ω y t)) := by
      have := iteratedDeriv_succ (n := 1) (f := fun y : ℝ => beamMode k L ω y t)
      simpa using this
    have hone : iteratedDeriv 1 (fun y : ℝ => beamMode k L ω y t) =
        deriv (fun y : ℝ => beamMode k L ω y t) := iteratedDeriv_one
    rw [hsucc, hone]
  rw [hIter, h1]
  exact h2

/-- Fourth spatial derivative: `w_xxxx = (kπ / L)^4 * w`. -/
lemma beamMode_iteratedDeriv_four (k : ℕ+) (L ω x t : ℝ) :
    iteratedDeriv 4 (fun y : ℝ => beamMode k L ω y t) x =
      ((k : ℝ) * Real.pi / L) ^ 4 * beamMode k L ω x t := by
  have hlin : ∀ y : ℝ, deriv (fun y : ℝ => (k : ℝ) * Real.pi * y / L) y =
      (k : ℝ) * Real.pi / L := by
    intro y
    simp
  have h1 : deriv (fun y : ℝ => beamMode k L ω y t) =
      fun y => Real.cos ((k : ℝ) * Real.pi * y / L) * ((k : ℝ) * Real.pi / L) *
        Real.cos (ω * t) := by
    funext y
    unfold beamMode
    rw [deriv_mul_const_field]
    rw [deriv_sin (by fun_prop)]
    rw [hlin y]
  have h2 : deriv (fun y : ℝ => Real.cos ((k : ℝ) * Real.pi * y / L) *
      ((k : ℝ) * Real.pi / L) * Real.cos (ω * t)) =
      fun y => -((k : ℝ) * Real.pi / L) ^ 2 *
        Real.sin ((k : ℝ) * Real.pi * y / L) * Real.cos (ω * t) := by
    funext y
    rw [deriv_mul_const_field]
    rw [deriv_mul_const_field]
    rw [deriv_cos (by fun_prop)]
    rw [hlin y]
    ring
  have h3 : deriv (fun y : ℝ => -((k : ℝ) * Real.pi / L) ^ 2 *
      Real.sin ((k : ℝ) * Real.pi * y / L) * Real.cos (ω * t)) =
      fun y => -((k : ℝ) * Real.pi / L) ^ 3 *
        Real.cos ((k : ℝ) * Real.pi * y / L) * Real.cos (ω * t) := by
    funext y
    rw [deriv_mul_const_field]
    rw [deriv_const_mul_field]
    rw [deriv_sin (by fun_prop)]
    rw [hlin y]
    ring
  have h4 : deriv (fun y : ℝ => -((k : ℝ) * Real.pi / L) ^ 3 *
      Real.cos ((k : ℝ) * Real.pi * y / L) * Real.cos (ω * t)) x =
      ((k : ℝ) * Real.pi / L) ^ 4 * beamMode k L ω x t := by
    rw [deriv_mul_const_field]
    rw [deriv_const_mul_field]
    rw [deriv_cos (by fun_prop)]
    rw [hlin x]
    unfold beamMode
    ring
  have hIter4 : iteratedDeriv 4 (fun y : ℝ => beamMode k L ω y t) x =
      deriv (deriv (deriv (deriv (fun y : ℝ => beamMode k L ω y t)))) x := by
    have h4s : iteratedDeriv 4 (fun y : ℝ => beamMode k L ω y t) =
        deriv (iteratedDeriv 3 (fun y : ℝ => beamMode k L ω y t)) := by
      have := iteratedDeriv_succ (n := 3) (f := fun y : ℝ => beamMode k L ω y t)
      simpa using this
    have h3s : iteratedDeriv 3 (fun y : ℝ => beamMode k L ω y t) =
        deriv (iteratedDeriv 2 (fun y : ℝ => beamMode k L ω y t)) := by
      have := iteratedDeriv_succ (n := 2) (f := fun y : ℝ => beamMode k L ω y t)
      simpa using this
    have h2s : iteratedDeriv 2 (fun y : ℝ => beamMode k L ω y t) =
        deriv (iteratedDeriv 1 (fun y : ℝ => beamMode k L ω y t)) := by
      have := iteratedDeriv_succ (n := 1) (f := fun y : ℝ => beamMode k L ω y t)
      simpa using this
    have h1s : iteratedDeriv 1 (fun y : ℝ => beamMode k L ω y t) =
        deriv (fun y : ℝ => beamMode k L ω y t) := iteratedDeriv_one
    rw [h4s, h3s, h2s, h1s]
  rw [hIter4, h1, h2, h3]
  exact h4

/-- Second temporal derivative: `w_tt = -ω^2 * w`. -/
lemma beamMode_iteratedDeriv_two_time (k : ℕ+) (L ω x t : ℝ) :
    iteratedDeriv 2 (fun s : ℝ => beamMode k L ω x s) t =
      -ω ^ 2 * beamMode k L ω x t := by
  have hlin : ∀ s : ℝ, deriv (fun s : ℝ => ω * s) s = ω := by
    intro s
    simp
  have h1 : deriv (fun s : ℝ => beamMode k L ω x s) =
      fun s => (-Real.sin ((k : ℝ) * Real.pi * x / L) * ω) * Real.sin (ω * s) := by
    funext s
    unfold beamMode
    rw [deriv_const_mul_field]
    rw [deriv_cos (by fun_prop)]
    rw [hlin s]
    ring
  have h2 : deriv (fun s : ℝ => (-Real.sin ((k : ℝ) * Real.pi * x / L) * ω) *
      Real.sin (ω * s)) t = -ω ^ 2 * beamMode k L ω x t := by
    rw [deriv_const_mul_field]
    rw [deriv_sin (by fun_prop)]
    rw [hlin t]
    unfold beamMode
    ring
  have hIter : iteratedDeriv 2 (fun s : ℝ => beamMode k L ω x s) t =
      deriv (deriv (fun s : ℝ => beamMode k L ω x s)) t := by
    have hsucc : iteratedDeriv 2 (fun s : ℝ => beamMode k L ω x s) =
        deriv (iteratedDeriv 1 (fun s : ℝ => beamMode k L ω x s)) := by
      have := iteratedDeriv_succ (n := 1) (f := fun s : ℝ => beamMode k L ω x s)
      simpa using this
    have hone : iteratedDeriv 1 (fun s : ℝ => beamMode k L ω x s) =
        deriv (fun s : ℝ => beamMode k L ω x s) := iteratedDeriv_one
    rw [hsucc, hone]
  rw [hIter, h1]
  exact h2

/-- Simply supported curvature conditions: `w_xx = 0` at both ends. -/
lemma beamMode_curvature_zero (k : ℕ+) {L : ℝ} (hL : L ≠ 0) (ω t : ℝ) :
    iteratedDeriv 2 (fun y : ℝ => beamMode k L ω y t) 0 = 0 ∧
      iteratedDeriv 2 (fun y : ℝ => beamMode k L ω y t) L = 0 := by
  constructor
  · rw [beamMode_iteratedDeriv_two, beamMode_zero_left, mul_zero]
  · rw [beamMode_iteratedDeriv_two, beamMode_zero_right k hL, mul_zero]

/-- The modal frequency squared: `ω_k^2 = (kπ / L)^4 * (EI / ρA)` for
`EI, ρA > 0`. -/
lemma beamFreq_sq {EI ρA L : ℝ} (hEI : 0 < EI) (hρ : 0 < ρA) (k : ℕ+) :
    beamFreq EI ρA L k ^ 2 = ((k : ℝ) * Real.pi / L) ^ 4 * (EI / ρA) := by
  unfold beamFreq
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  ring

/-- The beam equation `ρA * w_tt + EI * w_xxxx = 0` for the mode at
its modal frequency. -/
theorem beamMode_beamEquation {EI ρA L : ℝ} (hEI : 0 < EI) (hρ : 0 < ρA)
    (hL : L ≠ 0) (k : ℕ+) (x t : ℝ) :
    ρA * iteratedDeriv 2 (fun s : ℝ => beamMode k L (beamFreq EI ρA L k) x s) t +
        EI * iteratedDeriv 4 (fun y : ℝ => beamMode k L (beamFreq EI ρA L k) y t) x =
      0 := by
  rw [beamMode_iteratedDeriv_two_time, beamMode_iteratedDeriv_four, beamFreq_sq hEI hρ]
  have hρ' : ρA ≠ 0 := ne_of_gt hρ
  field_simp
  ring

/-- Beam energy of the mode at time `t`: the integral over `[0, L]` of
`(ρA * w_t^2 + EI * w_xx^2) / 2`. -/
noncomputable def beamModeEnergy (EI ρA L ω : ℝ) (k : ℕ+) (t : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..L,
    (ρA * deriv (fun s : ℝ => beamMode k L ω x s) t ^ 2 +
      EI * iteratedDeriv 2 (fun y : ℝ => beamMode k L ω y t) x ^ 2) / 2

private lemma cos_two_mul_integral_zero (k : ℕ+) {L : ℝ} (hL : 0 < L) :
    ∫ x in (0 : ℝ)..L, Real.cos (2 * ((k : ℝ) * Real.pi * x / L)) = 0 := by
  have hk : (0 : ℝ) < (k : ℝ) := by exact_mod_cast k.pos
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have ha_pos : (0 : ℝ) < (k : ℝ) * Real.pi / L := by positivity
  have hc0 : (2 : ℝ) * ((k : ℝ) * Real.pi / L) ≠ 0 := by positivity
  have hlin2 : ∀ y : ℝ, deriv (fun y : ℝ => 2 * ((k : ℝ) * Real.pi * y / L)) y =
      2 * ((k : ℝ) * Real.pi / L) := by
    intro y
    simp
  have hGderiv : deriv (fun x : ℝ => Real.sin (2 * ((k : ℝ) * Real.pi * x / L)) /
      (2 * ((k : ℝ) * Real.pi / L))) =
      fun x => Real.cos (2 * ((k : ℝ) * Real.pi * x / L)) := by
    funext x
    rw [deriv_div_const]
    rw [deriv_sin (by fun_prop)]
    rw [hlin2 x]
    field_simp
  have hGdiff : ∀ x ∈ Set.uIcc (0 : ℝ) L, DifferentiableAt ℝ
      (fun x : ℝ => Real.sin (2 * ((k : ℝ) * Real.pi * x / L)) /
        (2 * ((k : ℝ) * Real.pi / L))) x := by
    intro x _
    fun_prop
  have hGint : IntervalIntegrable
      (deriv (fun x : ℝ => Real.sin (2 * ((k : ℝ) * Real.pi * x / L)) /
        (2 * ((k : ℝ) * Real.pi / L)))) MeasureTheory.volume (0 : ℝ) L := by
    rw [hGderiv]
    apply Continuous.intervalIntegrable _ _ _
    fun_prop
  have hFTC := intervalIntegral.integral_deriv_eq_sub (a := (0 : ℝ)) (b := L)
    (f := fun x : ℝ => Real.sin (2 * ((k : ℝ) * Real.pi * x / L)) /
      (2 * ((k : ℝ) * Real.pi / L))) hGdiff hGint
  rw [hGderiv] at hFTC
  have hGL : Real.sin (2 * ((k : ℝ) * Real.pi * L / L)) /
      (2 * ((k : ℝ) * Real.pi / L)) = 0 := by
    have hLL : (k : ℝ) * Real.pi * L / L = ((k.val : ℕ) : ℝ) * Real.pi := by
      have hL0 : L ≠ 0 := ne_of_gt hL
      field_simp
    have h2 : 2 * ((k : ℝ) * Real.pi * L / L) =
        ((2 * (k.val : ℕ) : ℕ) : ℝ) * Real.pi := by
      rw [hLL]
      push_cast
      ring
    rw [h2, Real.sin_nat_mul_pi]
    simp
  have hG0 : Real.sin (2 * ((k : ℝ) * Real.pi * 0 / L)) /
      (2 * ((k : ℝ) * Real.pi / L)) = 0 := by
    simp
  rw [hFTC, hGL, hG0, sub_zero]

private lemma sin_sq_integral (k : ℕ+) {L : ℝ} (hL : 0 < L) :
    ∫ x in (0 : ℝ)..L, Real.sin ((k : ℝ) * Real.pi * x / L) ^ 2 = L / 2 := by
  have hfun : (fun x : ℝ => Real.sin ((k : ℝ) * Real.pi * x / L) ^ 2) =
      (fun x : ℝ => (1 : ℝ) / 2 - Real.cos (2 * ((k : ℝ) * Real.pi * x / L)) / 2) := by
    funext x
    rw [Real.sin_sq_eq_half_sub]
  rw [hfun]
  have h1 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ) / 2) MeasureTheory.volume (0 : ℝ) L := by
    apply Continuous.intervalIntegrable _ _ _
    fun_prop
  have h2 : IntervalIntegrable
      (fun x : ℝ => Real.cos (2 * ((k : ℝ) * Real.pi * x / L)) / 2)
      MeasureTheory.volume (0 : ℝ) L := by
    apply Continuous.intervalIntegrable _ _ _
    fun_prop
  rw [intervalIntegral.integral_sub h1 h2]
  have hconst : ∫ x in (0 : ℝ)..L, (1 : ℝ) / 2 = L / 2 := by
    rw [intervalIntegral.integral_const]
    simp
    ring
  have hcos : ∫ x in (0 : ℝ)..L, Real.cos (2 * ((k : ℝ) * Real.pi * x / L)) / 2 = 0 := by
    rw [intervalIntegral.integral_div]
    rw [cos_two_mul_integral_zero k hL]
    simp
  rw [hconst, hcos, sub_zero]

/-- The mode energy evaluates to
`(L / 4) * (ρA * ω^2 * sin^2(ωt) + EI * (kπ / L)^4 * cos^2(ωt))`. -/
lemma beamModeEnergy_eq {EI ρA L ω : ℝ} (hL : 0 < L) (k : ℕ+) (t : ℝ) :
    beamModeEnergy EI ρA L ω k t =
      (L / 4) * (ρA * ω ^ 2 * Real.sin (ω * t) ^ 2 +
        EI * ((k : ℝ) * Real.pi / L) ^ 4 * Real.cos (ω * t) ^ 2) := by
  have hWt : ∀ x : ℝ, deriv (fun s : ℝ => beamMode k L ω x s) t =
      (-Real.sin ((k : ℝ) * Real.pi * x / L) * ω) * Real.sin (ω * t) := by
    intro x
    unfold beamMode
    rw [deriv_const_mul_field]
    rw [deriv_cos (by fun_prop)]
    have hlin' : deriv (fun s : ℝ => ω * s) t = ω := by simp
    rw [hlin']
    ring
  have hWxx : ∀ x : ℝ, iteratedDeriv 2 (fun y : ℝ => beamMode k L ω y t) x =
      -((k : ℝ) * Real.pi / L) ^ 2 * Real.sin ((k : ℝ) * Real.pi * x / L) *
        Real.cos (ω * t) := by
    intro x
    rw [beamMode_iteratedDeriv_two]
    unfold beamMode
    ring
  have hfun : (fun x : ℝ => (ρA * deriv (fun s : ℝ => beamMode k L ω x s) t ^ 2 +
      EI * iteratedDeriv 2 (fun y : ℝ => beamMode k L ω y t) x ^ 2) / 2) =
      (fun x : ℝ => Real.sin ((k : ℝ) * Real.pi * x / L) ^ 2 *
        ((ρA * ω ^ 2 * Real.sin (ω * t) ^ 2 +
          EI * ((k : ℝ) * Real.pi / L) ^ 4 * Real.cos (ω * t) ^ 2) / 2)) := by
    funext x
    rw [hWt x, hWxx x]
    ring
  unfold beamModeEnergy
  rw [hfun]
  rw [intervalIntegral.integral_mul_const]
  rw [sin_sq_integral k hL]
  ring

/-- Energy conservation at the modal frequency: the energy is the
constant `(L / 4) * EI * (kπ / L)^4`. -/
theorem beamModeEnergy_conserved {EI ρA L : ℝ} (hEI : 0 < EI)
    (hρ : 0 < ρA) (hL : 0 < L) (k : ℕ+) (t : ℝ) :
    beamModeEnergy EI ρA L (beamFreq EI ρA L k) k t =
      (L / 4) * EI * ((k : ℝ) * Real.pi / L) ^ 4 := by
  rw [beamModeEnergy_eq hL]
  have hρ' : ρA ≠ 0 := ne_of_gt hρ
  have hB : ρA * beamFreq EI ρA L k ^ 2 = EI * ((k : ℝ) * Real.pi / L) ^ 4 := by
    rw [beamFreq_sq hEI hρ]
    field_simp
  have htrig : Real.sin (beamFreq EI ρA L k * t) ^ 2 +
      Real.cos (beamFreq EI ρA L k * t) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq _
  linear_combination (L / 4) * Real.sin (beamFreq EI ρA L k * t) ^ 2 * hB +
    (L / 4) * EI * ((k : ℝ) * Real.pi / L) ^ 4 * htrig

/-! ## B. Finite-mode truncation tail bound -/

/-- Finite Parseval identity for an orthonormal family: for any
finite index set `s` and coefficients `c`,
`‖∑ k ∈ s, c k • e k‖^2 = ∑ k ∈ s, (c k)^2`. -/
theorem orthonormal_sum_norm_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {e : ℕ → E} (he : Orthonormal ℝ e)
    (c : ℕ → ℝ) (s : Finset ℕ) :
    ‖∑ k ∈ s, c k • e k‖ ^ 2 = ∑ k ∈ s, c k ^ 2 := by
  have h := Orthonormal.inner_sum he c c s
  rw [real_inner_self_eq_norm_sq] at h
  refine h.trans ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [RCLike.conj_to_real, pow_two]

/-- Tail bound for a finite modal sum: the squared norm of the tail
modes `N + 1 .. K` is at most the squared norm of the full sum
`1 .. K`, since every modal contribution `(c k)^2` is nonnegative.
This is the displacement-tail bound for a finite-mode beam
truncation in an orthonormal sine basis; modal coefficients `c k`
at a fixed time already contain the initial-velocity contribution
`(b k) / ω k` in their sine-in-time part. -/
theorem orthonormal_tail_norm_sq_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {e : ℕ → E} (he : Orthonormal ℝ e)
    (c : ℕ → ℝ) {N K : ℕ} (hNK : N ≤ K) :
    ‖∑ k ∈ Finset.Ico (N + 1) (K + 1), c k • e k‖ ^ 2 ≤
      ‖∑ k ∈ Finset.Icc 1 K, c k • e k‖ ^ 2 := by
  have _ : N ≤ K := hNK
  rw [orthonormal_sum_norm_sq he, orthonormal_sum_norm_sq he]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?hsub (fun k _ _ => sq_nonneg _)
  intro x hx
  rw [Finset.mem_Ico] at hx
  rw [Finset.mem_Icc]
  exact ⟨Nat.le_trans (Nat.le_add_left 1 N) hx.1, Nat.le_of_lt_succ hx.2⟩

/-- Tail bound for the existing sine Hilbert basis
`MathlibExt.Analysis.ODE.GreensOperator.sineHilbertBasis` on
`L²([0, 1])`: the basis is indexed by positive mode number, so
with zero-based coefficient indices the full sum runs over
`k ∈ Finset.Ico 0 K` (modes `1 .. K`, coefficient `c k` on mode
`k + 1`) and the tail over `k ∈ Finset.Ico N K` (modes
`N + 1 .. K`); the tail's squared norm is at most the full sum's.
Fixed-time modal coefficients already contain the
initial-velocity contribution divided by the modal frequency. -/
theorem sineBasis_tail_norm_sq_le (c : ℕ → ℝ) {N K : ℕ} (hNK : N ≤ K) :
    ‖∑ k ∈ Finset.Ico N K,
        c k • MathlibExt.Analysis.ODE.GreensOperator.sineHilbertBasis
          ⟨k + 1, Nat.succ_pos k⟩‖ ^ 2 ≤
      ‖∑ k ∈ Finset.Ico 0 K,
        c k • MathlibExt.Analysis.ODE.GreensOperator.sineHilbertBasis
          ⟨k + 1, Nat.succ_pos k⟩‖ ^ 2 := by
  have he : Orthonormal ℝ (fun k : ℕ =>
      MathlibExt.Analysis.ODE.GreensOperator.sineHilbertBasis
        ⟨k + 1, Nat.succ_pos k⟩) :=
    MathlibExt.Analysis.ODE.GreensOperator.sineHilbertBasis.orthonormal.comp
      (fun n : ℕ => (⟨n + 1, Nat.succ_pos n⟩ : ℕ+))
      (fun a b h => by
        simpa using congrArg (fun p : ℕ+ => (p : ℕ)) h)
  rw [orthonormal_sum_norm_sq he, orthonormal_sum_norm_sq he]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Ico_subset_Ico (Nat.zero_le N) le_rfl) (fun k _ _ => sq_nonneg _)

end BeamModes
