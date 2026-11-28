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
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Beam modes: simply supported mode and clamped-free mode in physical units

## i. Overview

The `k`-th simply supported Euler-Bernoulli beam mode
`w(x, t) = sin(kπx / L) * cos(ωt)` with modal frequency
`ω_k = (kπ / L)^2 * √(EI / ρA)`: it solves
`ρA * w_tt + EI * w_xxxx = 0` with `w = w_xx = 0` at both ends, and
its total energy (kinetic plus bending, integrated over `[0, L]`) is
the constant `(L / 4) * EI * (kπ / L)^4`. Uniform beam, unit mode
amplitude; no mode-completeness or first-mode claim is made.

For the beam clamped at `x = 0` and free at `x = L`, every member
`c₀ cos βx + c₁ sin βx + c₂ cosh βx + c₃ sinh βx` of the four-parameter
family solves the mode equation `W'''' = β ^ 4 W`, and its four boundary
traces (`W 0`, `W' 0` at the clamp; `W'' L`, `W''' L`, zero bending
moment and shear force, at the free end) are the rows of a `4 × 4`
boundary matrix applied to its coefficients. The determinant of that
matrix at `z = β L` is `2 (cos z cosh z + 1)`, so a family member with
nonzero coefficients meets the four conditions exactly when
`cos z cosh z + 1 = 0`. The characteristic function is positive on
`(0, π / 2]` and strictly decreasing on `(π / 2, π)`, so the least
positive root `z₁ ≈ 1.8751` lies in `(π / 2, π)` and is the only root
there. For every positive root the mode
`(sin z + sinh z) (cos βx - cosh βx) - (cos z + cosh z) (sin βx - sinh βx)`,
`β = z / L`, meets the four conditions and has a nonzero tip deflection;
at `ω = (z / L) ^ 2 √(EI / ρA)` it solves the beam equation, and the
frequency scales as `1 / L ^ 2`. The bracket `((2 k - 1) π / 2, k π)` for
the `k`-th root is not used: the second root lies below `3 π / 2`. That
every eigenfunction of the clamped-free problem lies in the family is not
claimed.

## ii. Key results

- `BeamModes.beamMode_beamEquation`: the mode at its modal frequency
  satisfies the beam equation at every `x, t`.
- `BeamModes.beamModeEnergy_conserved`: the integrated energy is
  constant in time.
- `BeamModes.clampedFreeMatrix_det`, `BeamModes.exists_isClampedFree_iff`:
  the clamped-free boundary matrix and the characteristic equation
  `cos z cosh z + 1 = 0`.
- `BeamModes.cantileverChar_pos`, `BeamModes.cantileverChar_strictAntiOn`,
  `BeamModes.isLeast_cantileverRoot`, `BeamModes.cantileverRoot_mem_Ioo`,
  `BeamModes.eq_cantileverRoot_of_mem_Ioo`: the least positive root lies
  in `(π / 2, π)` and is the only root there.
- `BeamModes.isClampedFree_cantileverMode`,
  `BeamModes.cantileverMode_tip_ne_zero`,
  `BeamModes.cantileverMode_beamEquation`,
  `BeamModes.cantileverFreq_length_scaling`,
  `BeamModes.cantileverFirstMode`: the nonzero clamped-free mode, its
  frequency and the `1 / L ^ 2` scaling.
- `BeamModes.secondRoot_lt_three_pi_div_two`: the second root lies below
  `3 π / 2`, so the bracket `((2 k - 1) π / 2, k π)` fails at `k = 2`.


## iii. Table of contents

- A. The simply supported mode and its energy
- B. The clamped-free mode
  - B.1. The characteristic function and the boundary matrix
  - B.2. The least positive root
  - B.3. The mode and its frequency
  - B.4. The old root bracket

## iv. References

- The Dirichlet sine eigenfunctions of
  `MathlibExt.Analysis.ODE.DirichletSineEigenfunctions`, whose
  differential identities this physical-units mode instantiates with
  explicit `EI`, `ρA`, and `L`.
- S. S. Rao, *Mechanical Vibrations*, 6th ed., Pearson (2017):
  the Euler-Bernoulli beam equation `ρA * w_tt + EI * w_xxxx = 0`,
  the simply supported modal frequencies
  `ω_k = (kπ / L)^2 * √(EI / ρA)`, and the kinetic/bending energy
  expressions used here; the clamped-free frequency equation
  `cos βL cosh βL = -1` with `β₁ L ≈ 1.875104`.
- L. Meirovitch, *Fundamentals of Vibrations*, McGraw-Hill (2001):
  cantilever bending modes.

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

/-! ## B. The clamped-free mode -/

/-! ### B.1. The characteristic function and the boundary matrix -/

/-- The cantilever characteristic function `cos z * cosh z + 1`. -/
noncomputable def cantileverChar (z : ℝ) : ℝ := Real.cos z * Real.cosh z + 1

/-- The four-parameter family
`c 0 * cos (β x) + c 1 * sin (β x) + c 2 * cosh (β x) + c 3 * sinh (β x)`. -/
noncomputable def modeFamily (β : ℝ) (c : Fin 4 → ℝ) (x : ℝ) : ℝ :=
  c 0 * Real.cos (β * x) + c 1 * Real.sin (β * x) + c 2 * Real.cosh (β * x) +
    c 3 * Real.sinh (β * x)

/-- The clamped-free boundary matrix at `z = β L`: for the family member with coefficients `c`
its rows give `W 0`, `W' 0 / β`, `W'' L / β ^ 2` and `W''' L / β ^ 3`. -/
noncomputable def clampedFreeMatrix (z : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 1, 0;
    0, 1, 0, 1;
    -Real.cos z, -Real.sin z, Real.cosh z, Real.sinh z;
    Real.sin z, -Real.cos z, Real.sinh z, Real.cosh z]

/-- The clamped-free conditions for a mode shape `W` of a beam of positive length `L`: zero
deflection and slope at the clamp `x = 0`; zero curvature and zero third derivative at the free
end `x = L` (zero bending moment and shear force for `EI > 0`). -/
structure IsClampedFree (L : ℝ) (W : ℝ → ℝ) : Prop where
  span_pos : 0 < L
  zero_left : W 0 = 0
  slope_left : deriv W 0 = 0
  moment_right : iteratedDeriv 2 W L = 0
  shear_right : iteratedDeriv 3 W L = 0

/-- Coefficients of the derivative of a family member, divided by `β`. -/
private def rotC (c : Fin 4 → ℝ) : Fin 4 → ℝ := ![c 1, -c 0, c 3, c 2]

/-- The derivative of a family member is `β` times the member with coefficients `rotC c`. -/
private lemma hasDerivAt_modeFamily (β : ℝ) (c : Fin 4 → ℝ) (x : ℝ) :
    HasDerivAt (modeFamily β c) (β * modeFamily β (rotC c) x) x := by
  have hl : HasDerivAt (fun y : ℝ => β * y) β x := by
    simpa using (hasDerivAt_id x).const_mul β
  have h0 := (Real.hasDerivAt_cos (β * x)).comp x hl
  have h1 := (Real.hasDerivAt_sin (β * x)).comp x hl
  have h2 := (Real.hasDerivAt_cosh (β * x)).comp x hl
  have h3 := (Real.hasDerivAt_sinh (β * x)).comp x hl
  have h := (((h0.const_mul (c 0)).add (h1.const_mul (c 1))).add
    (h2.const_mul (c 2))).add (h3.const_mul (c 3))
  have hf : modeFamily β c = fun y => c 0 * (Real.cos ∘ fun y => β * y) y +
      c 1 * (Real.sin ∘ fun y => β * y) y + c 2 * (Real.cosh ∘ fun y => β * y) y +
      c 3 * (Real.sinh ∘ fun y => β * y) y := by
    funext y
    simp [modeFamily]
  rw [hf]
  convert h using 1
  simp [modeFamily, rotC]
  ring

/-- The `n`-th derivative of a family member: `β ^ n` times the member with the coefficients
rotated `n` times. -/
private lemma iteratedDeriv_modeFamily (β : ℝ) (n : ℕ) (c : Fin 4 → ℝ) :
    iteratedDeriv n (modeFamily β c) = fun x => β ^ n * modeFamily β (rotC^[n] c) x := by
  induction n with
  | zero => funext x; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    have h := ((hasDerivAt_modeFamily β (rotC^[n] c) x).const_mul (β ^ n)).deriv
    rw [h, Function.iterate_succ_apply']
    ring

/-- Rotating the coefficients four times gives them back. -/
private lemma rotC_four (c : Fin 4 → ℝ) : rotC^[4] c = c := by
  funext i
  fin_cases i <;> simp [rotC]

/-- Every family member solves the mode equation `W'''' = β ^ 4 W`. -/
lemma modeFamily_iteratedDeriv_four (β : ℝ) (c : Fin 4 → ℝ) (x : ℝ) :
    iteratedDeriv 4 (modeFamily β c) x = β ^ 4 * modeFamily β c x := by
  rw [iteratedDeriv_modeFamily, rotC_four]

/-- The boundary traces of a family member are the rows of the boundary matrix at `β L` applied
to its coefficients, scaled by `1, β, β ^ 2, β ^ 3`. -/
lemma modeFamily_traces (β L : ℝ) (c : Fin 4 → ℝ) :
    modeFamily β c 0 = (clampedFreeMatrix (β * L)).mulVec c 0 ∧
      deriv (modeFamily β c) 0 = β * (clampedFreeMatrix (β * L)).mulVec c 1 ∧
      iteratedDeriv 2 (modeFamily β c) L = β ^ 2 * (clampedFreeMatrix (β * L)).mulVec c 2 ∧
      iteratedDeriv 3 (modeFamily β c) L = β ^ 3 * (clampedFreeMatrix (β * L)).mulVec c 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [modeFamily, clampedFreeMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  · rw [(hasDerivAt_modeFamily β c 0).deriv]
    simp [modeFamily, clampedFreeMatrix, rotC, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  · rw [iteratedDeriv_modeFamily]
    dsimp only
    congr 1
    simp [modeFamily, clampedFreeMatrix, rotC, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    ring
  · rw [iteratedDeriv_modeFamily]
    dsimp only
    congr 1
    simp [modeFamily, clampedFreeMatrix, rotC, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    ring

/-- The determinant of the clamped-free boundary matrix is `2 (cos z cosh z + 1)`. -/
lemma clampedFreeMatrix_det (z : ℝ) : (clampedFreeMatrix z).det = 2 * cantileverChar z := by
  simp [clampedFreeMatrix, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove,
    cantileverChar]
  linear_combination Real.sin_sq_add_cos_sq z + Real.cosh_sq_sub_sinh_sq z

/-- The characteristic equation, from the boundary matrix: for `β > 0` and `L > 0` some family
member with nonzero coefficients meets the clamped-free conditions exactly when
`cos (β L) cosh (β L) + 1 = 0`. -/
lemma exists_isClampedFree_iff {β L : ℝ} (hβ : 0 < β) (hL : 0 < L) :
    (∃ c : Fin 4 → ℝ, c ≠ 0 ∧ IsClampedFree L (modeFamily β c)) ↔
      cantileverChar (β * L) = 0 := by
  constructor
  · rintro ⟨c, hc, hW⟩
    obtain ⟨t0, t1, t2, t3⟩ := modeFamily_traces β L c
    have hv : (clampedFreeMatrix (β * L)).mulVec c = 0 := by
      funext i
      fin_cases i
      · simpa [← t0] using hW.zero_left
      · have h := hW.slope_left
        rw [t1] at h
        simpa using (mul_eq_zero.mp h).resolve_left hβ.ne'
      · have h := hW.moment_right
        rw [t2] at h
        simpa using (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hβ.ne')
      · have h := hW.shear_right
        rw [t3] at h
        simpa using (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hβ.ne')
    have hdet := Matrix.exists_mulVec_eq_zero_iff.mp ⟨c, hc, hv⟩
    rw [clampedFreeMatrix_det] at hdet
    linarith
  · intro h
    have hdet : (clampedFreeMatrix (β * L)).det = 0 := by rw [clampedFreeMatrix_det, h, mul_zero]
    obtain ⟨c, hc, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    obtain ⟨t0, t1, t2, t3⟩ := modeFamily_traces β L c
    refine ⟨c, hc, hL, ?_, ?_, ?_, ?_⟩
    · rw [t0, hv]
      rfl
    · rw [t1, hv]
      simp
    · rw [t2, hv]
      simp
    · rw [t3, hv]
      simp

/-! ### B.2. The least positive root -/

/-- The characteristic function is continuous. -/
private lemma cantileverChar_continuous : Continuous cantileverChar := by
  unfold cantileverChar
  fun_prop

/-- The characteristic function is negative at `π`: `1 - cosh π < 0`. -/
private lemma cantileverChar_pi_lt : cantileverChar Real.pi < 0 := by
  unfold cantileverChar
  rw [Real.cos_pi]
  have := Real.one_lt_cosh.mpr Real.pi_pos.ne'
  linarith

/-- The characteristic function has a root in `(π / 2, π)` (intermediate value theorem). -/
private lemma exists_root_Ioo : ∃ z ∈ Set.Ioo (Real.pi / 2) Real.pi, cantileverChar z = 0 := by
  have hab : Real.pi / 2 ≤ Real.pi := by linarith [Real.pi_pos]
  have h := intermediate_value_Ioo' hab cantileverChar_continuous.continuousOn
  have hmem : (0 : ℝ) ∈ Set.Ioo (cantileverChar Real.pi) (cantileverChar (Real.pi / 2)) := by
    refine ⟨cantileverChar_pi_lt, ?_⟩
    simp [cantileverChar]
  obtain ⟨z, hz, hz0⟩ := h hmem
  exact ⟨z, hz, hz0⟩

/-- The characteristic function is positive on `(0, π / 2]`. -/
lemma cantileverChar_pos {z : ℝ} (hz : 0 < z) (hz' : z ≤ Real.pi / 2) :
    0 < cantileverChar z := by
  unfold cantileverChar
  have hc : 0 ≤ Real.cos z :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hz'⟩
  have := Real.cosh_pos z
  nlinarith

/-- The characteristic function is strictly decreasing on `(π / 2, π)`. -/
lemma cantileverChar_strictAntiOn :
    StrictAntiOn cantileverChar (Set.Ioo (Real.pi / 2) Real.pi) := by
  have hderiv : ∀ z, HasDerivAt cantileverChar
      (-Real.sin z * Real.cosh z + Real.cos z * Real.sinh z) z := by
    intro z
    have := ((Real.hasDerivAt_cos z).mul (Real.hasDerivAt_cosh z)).add_const 1
    unfold cantileverChar
    convert this using 1
  apply strictAntiOn_of_deriv_neg (convex_Ioo _ _) cantileverChar_continuous.continuousOn
  intro z hz
  rw [interior_Ioo] at hz
  rw [(hderiv z).deriv]
  have hs : 0 < Real.sin z :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos, hz.1]) hz.2
  have hc : Real.cos z < 0 :=
    Real.cos_neg_of_pi_div_two_lt_of_lt hz.1 (by linarith [Real.pi_pos, hz.2])
  have hsh : 0 < Real.sinh z := Real.sinh_pos_iff.mpr (by linarith [Real.pi_pos, hz.1])
  have hch : 0 < Real.cosh z := Real.cosh_pos z
  nlinarith [mul_pos hs hch, mul_neg_of_neg_of_pos hc hsh]

/-- A root in `(π / 2, π)` is at most every positive root. -/
private lemma le_of_root {z₁ : ℝ} (hz₁ : z₁ ∈ Set.Ioo (Real.pi / 2) Real.pi)
    (h₁ : cantileverChar z₁ = 0) {z : ℝ} (hz : 0 < z) (h : cantileverChar z = 0) : z₁ ≤ z := by
  rcases le_or_gt z (Real.pi / 2) with hle | hgt
  · exact absurd h (cantileverChar_pos hz hle).ne'
  rcases lt_or_ge z Real.pi with hlt | hge
  · exact le_of_eq (cantileverChar_strictAntiOn.injOn hz₁ ⟨hgt, hlt⟩ (h₁.trans h.symm))
  · exact le_of_lt (lt_of_lt_of_le hz₁.2 hge)

/-- A root in `(π / 2, π)` is the least positive root. -/
private lemma isLeast_of_root {z₁ : ℝ} (hz₁ : z₁ ∈ Set.Ioo (Real.pi / 2) Real.pi)
    (h₁ : cantileverChar z₁ = 0) : IsLeast {z : ℝ | 0 < z ∧ cantileverChar z = 0} z₁ :=
  ⟨⟨lt_trans (by linarith [Real.pi_pos]) hz₁.1, h₁⟩, fun _ hz => le_of_root hz₁ h₁ hz.1 hz.2⟩

/-- The least positive root of `cos z * cosh z + 1 = 0`. -/
noncomputable def cantileverRoot : ℝ := sInf {z : ℝ | 0 < z ∧ cantileverChar z = 0}

/-- `cantileverRoot` is a positive root, and no positive root is smaller. -/
lemma isLeast_cantileverRoot :
    IsLeast {z : ℝ | 0 < z ∧ cantileverChar z = 0} cantileverRoot := by
  obtain ⟨z₁, hz₁, h₁⟩ := exists_root_Ioo
  have hl := isLeast_of_root hz₁ h₁
  unfold cantileverRoot
  rw [hl.csInf_eq]
  exact hl

/-- `cantileverRoot` is a root in `(π / 2, π)`. -/
private lemma cantileverRoot_spec :
    cantileverRoot ∈ Set.Ioo (Real.pi / 2) Real.pi ∧ cantileverChar cantileverRoot = 0 := by
  obtain ⟨z₁, hz₁, h₁⟩ := exists_root_Ioo
  have := (isLeast_of_root hz₁ h₁).csInf_eq
  unfold cantileverRoot
  rw [this]
  exact ⟨hz₁, h₁⟩

/-- The least positive root lies in `(π / 2, π)`. -/
lemma cantileverRoot_mem_Ioo : cantileverRoot ∈ Set.Ioo (Real.pi / 2) Real.pi := by
  exact cantileverRoot_spec.1

/-- The least positive root is the only root in `(π / 2, π)`. -/
lemma eq_cantileverRoot_of_mem_Ioo {z : ℝ} (hz : z ∈ Set.Ioo (Real.pi / 2) Real.pi)
    (h : cantileverChar z = 0) : z = cantileverRoot := by
  exact cantileverChar_strictAntiOn.injOn hz cantileverRoot_spec.1
    (h.trans cantileverRoot_spec.2.symm)

/-! ### B.3. The mode and its frequency -/

/-- The clamped-free mode of a beam of length `L` for a root `z`, with `β = z / L`:
`(sin z + sinh z) (cos (β x) - cosh (β x)) - (cos z + cosh z) (sin (β x) - sinh (β x))`. -/
noncomputable def cantileverMode (L z x : ℝ) : ℝ :=
  (Real.sin z + Real.sinh z) * (Real.cos (z * x / L) - Real.cosh (z * x / L)) -
    (Real.cos z + Real.cosh z) * (Real.sin (z * x / L) - Real.sinh (z * x / L))

/-- The mode is the family member with `β = z / L` and coefficients
`(sin z + sinh z, -(cos z + cosh z), -(sin z + sinh z), cos z + cosh z)`. -/
lemma cantileverMode_eq_modeFamily (L z : ℝ) :
    cantileverMode L z = modeFamily (z / L) ![Real.sin z + Real.sinh z,
      -(Real.cos z + Real.cosh z), -(Real.sin z + Real.sinh z), Real.cos z + Real.cosh z] := by
  funext x
  simp only [cantileverMode, modeFamily, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  rw [show z / L * x = z * x / L by ring]
  ring

/-- For a root `z` the mode meets the clamped-free conditions. -/
lemma isClampedFree_cantileverMode {L z : ℝ} (hL : 0 < L) (hz : cantileverChar z = 0) :
    IsClampedFree L (cantileverMode L z) := by
  rw [cantileverMode_eq_modeFamily]
  obtain ⟨t0, t1, t2, t3⟩ := modeFamily_traces (z / L) L ![Real.sin z + Real.sinh z,
      -(Real.cos z + Real.cosh z), -(Real.sin z + Real.sinh z), Real.cos z + Real.cosh z]
  have hzL : z / L * L = z := by field_simp
  rw [hzL] at t0 t1 t2 t3
  unfold cantileverChar at hz
  refine ⟨hL, ?_, ?_, ?_, ?_⟩
  · rw [t0]
    simp [clampedFreeMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  · rw [t1]
    simp [clampedFreeMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  · rw [t2]
    refine mul_eq_zero_of_right _ ?_
    simp [clampedFreeMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    ring
  · rw [t3]
    refine mul_eq_zero_of_right _ ?_
    simp [clampedFreeMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    linear_combination Real.sin_sq_add_cos_sq z + Real.cosh_sq_sub_sinh_sq z + 2 * hz

/-- For a positive root the mode is nonzero: its tip deflection
`2 (sinh z cos z - sin z cosh z)` does not vanish. -/
lemma cantileverMode_tip_ne_zero {L z : ℝ} (hL : L ≠ 0) (hz : 0 < z)
    (h : cantileverChar z = 0) : cantileverMode L z L ≠ 0 := by
  unfold cantileverMode
  rw [show z * L / L = z by field_simp]
  intro h0
  unfold cantileverChar at h
  have h1 : Real.sin z * Real.cosh z = Real.sinh z * Real.cos z := by linear_combination -h0 / 2
  have h3 := Real.sin_sq_add_cos_sq z
  have h4 := Real.cosh_sq_sub_sinh_sq z
  have hsh : 0 < Real.sinh z := Real.sinh_pos_iff.mpr hz
  have key : Real.sinh z ^ 4 = 0 := by
    linear_combination (Real.cosh z * (Real.sin z * Real.cosh z ^ 2 - Real.sinh z)) * h1 +
      (Real.sinh z * (Real.sin z * Real.cosh z ^ 2 - Real.sinh z) +
        Real.cosh z ^ 2 * (Real.cos z * Real.cosh z - 1)) * h -
      Real.cosh z ^ 4 * h3 - (Real.sinh z ^ 2 + Real.cosh z ^ 2) * h4
  have : 0 < Real.sinh z ^ 4 := by positivity
  linarith

/-- The natural frequency of the mode for the root `z`: `ω = (z / L) ^ 2 * √(EI / ρA)`. -/
noncomputable def cantileverFreq (EI ρA L z : ℝ) : ℝ := (z / L) ^ 2 * Real.sqrt (EI / ρA)

/-- The second derivative of `s ↦ cos (ω s)` is `-ω ^ 2 cos (ω t)`. -/
private lemma iteratedDeriv_two_cos_mul (ω t : ℝ) :
    iteratedDeriv 2 (fun s : ℝ => Real.cos (ω * s)) t = -ω ^ 2 * Real.cos (ω * t) := by
  have hl : ∀ s : ℝ, HasDerivAt (fun s : ℝ => ω * s) ω s := fun s => by
    simpa using (hasDerivAt_id s).const_mul ω
  have h1 : deriv (fun s : ℝ => Real.cos (ω * s)) = fun s => -Real.sin (ω * s) * ω := by
    funext s
    exact ((Real.hasDerivAt_cos (ω * s)).comp s (hl s)).deriv
  have h2 : HasDerivAt (fun s : ℝ => -Real.sin (ω * s) * ω) (-(Real.cos (ω * t) * ω) * ω) t :=
    (((Real.hasDerivAt_sin (ω * t)).comp t (hl t)).neg).mul_const ω
  rw [iteratedDeriv_succ, iteratedDeriv_one, h1, h2.deriv]
  ring

/-- The mode solves `W'''' = (z / L) ^ 4 W`. -/
private lemma cantileverMode_iteratedDeriv_four (L z x : ℝ) :
    iteratedDeriv 4 (cantileverMode L z) x = (z / L) ^ 4 * cantileverMode L z x := by
  rw [cantileverMode_eq_modeFamily, modeFamily_iteratedDeriv_four]

/-- At its natural frequency the mode solves the beam equation `ρA w_tt + EI w_xxxx = 0` for
`w(x, t) = W(x) cos(ω t)`. -/
lemma cantileverMode_beamEquation {EI ρA : ℝ} (hEI : 0 < EI) (hρ : 0 < ρA) (L z x t : ℝ) :
    ρA * iteratedDeriv 2
        (fun s : ℝ => cantileverMode L z x * Real.cos (cantileverFreq EI ρA L z * s)) t +
      EI * iteratedDeriv 4
        (fun y : ℝ => cantileverMode L z y * Real.cos (cantileverFreq EI ρA L z * t)) x = 0 := by
  have ht : iteratedDeriv 2
      (fun s : ℝ => cantileverMode L z x * Real.cos (cantileverFreq EI ρA L z * s)) t =
      cantileverMode L z x * (-(cantileverFreq EI ρA L z) ^ 2 *
        Real.cos (cantileverFreq EI ρA L z * t)) := by
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_two_cos_mul]
  have hx : iteratedDeriv 4
      (fun y : ℝ => cantileverMode L z y * Real.cos (cantileverFreq EI ρA L z * t)) x =
      Real.cos (cantileverFreq EI ρA L z * t) * ((z / L) ^ 4 * cantileverMode L z x) := by
    have hf : (fun y : ℝ => cantileverMode L z y * Real.cos (cantileverFreq EI ρA L z * t)) =
        fun y => Real.cos (cantileverFreq EI ρA L z * t) * cantileverMode L z y := by
      funext y
      ring
    rw [hf, iteratedDeriv_const_mul_field, cantileverMode_iteratedDeriv_four]
  rw [ht, hx]
  have hω : cantileverFreq EI ρA L z ^ 2 = (z / L) ^ 4 * (EI / ρA) := by
    unfold cantileverFreq
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    ring
  rw [hω]
  field_simp
  ring

/-- Frequency scaling: lengthening the beam by a factor `k` divides the frequency of each mode by
`k ^ 2` (for `k = 0` both sides are `0` by the convention `x / 0 = 0`). -/
lemma cantileverFreq_length_scaling (EI ρA L z k : ℝ) :
    cantileverFreq EI ρA (k * L) z = cantileverFreq EI ρA L z / k ^ 2 := by
  unfold cantileverFreq
  ring

/-- The first mode: for the least positive root `z₁` the mode meets the clamped-free conditions,
has a nonzero tip deflection, and solves the beam equation at `ω₁ = (z₁ / L) ^ 2 * √(EI / ρA)`. -/
lemma cantileverFirstMode {EI ρA L : ℝ} (hEI : 0 < EI) (hρ : 0 < ρA) (hL : 0 < L) :
    IsClampedFree L (cantileverMode L cantileverRoot) ∧
      cantileverMode L cantileverRoot L ≠ 0 ∧
      ∀ x t : ℝ, ρA * iteratedDeriv 2 (fun s : ℝ => cantileverMode L cantileverRoot x *
          Real.cos (cantileverFreq EI ρA L cantileverRoot * s)) t +
        EI * iteratedDeriv 4 (fun y : ℝ => cantileverMode L cantileverRoot y *
          Real.cos (cantileverFreq EI ρA L cantileverRoot * t)) x = 0 := by
  have hr := cantileverRoot_spec
  have hpos : 0 < cantileverRoot := lt_trans (by linarith [Real.pi_pos]) hr.1.1
  exact ⟨isClampedFree_cantileverMode hL hr.2, cantileverMode_tip_ne_zero hL.ne' hpos hr.2,
    fun x t => cantileverMode_beamEquation hEI hρ L cantileverRoot x t⟩

/-! ### B.4. The old root bracket -/

/-- The equation `cos z cosh z + 1 = 0` has a root in `(π, 3 π / 2)` and none in
`(3 π / 2, 2 π)`, so the bracket `((2 k - 1) π / 2, k π)` fails at `k = 2`. -/
lemma secondRoot_lt_three_pi_div_two :
    (∃ z ∈ Set.Ioo Real.pi (3 * Real.pi / 2), cantileverChar z = 0) ∧
      ∀ z ∈ Set.Ioo (3 * Real.pi / 2) (2 * Real.pi), cantileverChar z ≠ 0 := by
  refine ⟨?_, fun z hz => ?_⟩
  · have hab : Real.pi ≤ 3 * Real.pi / 2 := by linarith [Real.pi_pos]
    have h := intermediate_value_Ioo hab cantileverChar_continuous.continuousOn
    have hmem : (0 : ℝ) ∈ Set.Ioo (cantileverChar Real.pi) (cantileverChar (3 * Real.pi / 2)) := by
      refine ⟨cantileverChar_pi_lt, ?_⟩
      have : Real.cos (3 * Real.pi / 2) = 0 := by
        rw [show 3 * Real.pi / 2 = Real.pi / 2 + Real.pi by ring, Real.cos_add_pi,
          Real.cos_pi_div_two, neg_zero]
      simp [cantileverChar, this]
    obtain ⟨z, hz, hz0⟩ := h hmem
    exact ⟨z, hz, hz0⟩
  · have hc : 0 < Real.cos z := by
      rw [← Real.cos_sub_two_pi]
      exact Real.cos_pos_of_mem_Ioo ⟨by linarith [hz.1], by linarith [hz.2, Real.pi_pos]⟩
    unfold cantileverChar
    have := Real.cosh_pos z
    nlinarith

end BeamModes
