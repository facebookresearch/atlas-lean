/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import MathlibExt.Analysis.Calculus.MvPolynomial
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open MvPolynomial

-- The bridge retains within-set derivatives; it does not require unique
-- differentiability of the time set (in particular, singleton sets are valid).
example {σ : Type*} [Fintype σ] (p : MvPolynomial σ ℝ)
    (F : σ → MvPolynomial σ ℝ) {u : ℝ → σ → ℝ} {s : Set ℝ} {t : ℝ}
    (hu : HasDerivWithinAt u (fun i => eval (u t) (F i)) s t) :
    HasDerivWithinAt (fun r => eval (u r) p)
      (eval (u t) (mkDerivation ℝ F p)) s t :=
  hasDerivWithinAt_eval_mkDerivation p F hu

-- The symbolic formula needs only a commutative semiring, not a field.
example : mkDerivation ℕ (fun _ : Fin 1 => (1 : MvPolynomial (Fin 1) ℕ)) (X 0 ^ 2) = 2 * X 0 := by
  rw [mkDerivation_eq_sum_pderiv]
  simp

-- All coordinates contribute to a genuinely mixed derivative.
example : fderiv ℝ (fun x : Fin 2 → ℝ => x 0 ^ 2 * x 1) ![2, 3] ![5, 7] = 88 := by
  have h := congrArg (fun L : (Fin 2 → ℝ) →L[ℝ] ℝ => L ![5, 7])
    (hasFDerivAt_eval (X 0 ^ 2 * X 1 : MvPolynomial (Fin 2) ℝ) ![2, 3]).fderiv
  norm_num [pderiv_mul, pderiv_pow, Fin.sum_univ_two, Pi.single_apply] at h
  exact h

private theorem parabola_velocity (t : ℝ) :
    HasDerivAt (fun r => (![r, r ^ 2] : Fin 2 → ℝ)) ![1, 2 * t] t := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa using! hasDerivAt_id t
  · simpa using! (hasDerivAt_id t).pow 2

-- The curve (t,t²) solves the polynomial field (1,2x). The derivative of
-- x²y along it is 4t³, with a concrete nonzero value at t=2 below.
example (s : Set ℝ) (t : ℝ) :
    HasDerivWithinAt (fun r : ℝ => r ^ 2 * r ^ 2) (4 * t ^ 3) s t := by
  have hu : HasDerivWithinAt (fun r => (![r, r ^ 2] : Fin 2 → ℝ))
      (fun i => eval ![t, t ^ 2] (![1, C 2 * X 0] i)) s t := by
    convert! (parabola_velocity t).hasDerivWithinAt using 1
    ext i; fin_cases i <;> simp
  have h := hasDerivWithinAt_eval_mkDerivation (X 0 ^ 2 * X 1) ![1, C 2 * X 0] hu
  convert! h using 1
  · simp
  · simp
    ring

example : HasDerivWithinAt (fun r : ℝ => r ^ 2 * r ^ 2) 32 (Set.Icc 0 2) 2 := by
  have h := hasDerivWithinAt_eval (s := Set.Icc 0 2) (X 0 ^ 2 * X 1 : MvPolynomial (Fin 2) ℝ)
    (parabola_velocity 2).hasDerivWithinAt
  norm_num [pderiv_mul, pderiv_pow, Fin.sum_univ_two, Pi.single_apply] at h
  exact h

-- Zero Lie derivative for rotation, with both components nonzero as polynomials.
example : mkDerivation ℝ (![-X 1, X 0] : Fin 2 → MvPolynomial (Fin 2) ℝ)
    (X 0 ^ 2 + X 1 ^ 2 - 1) = 0 := by
  rw [mkDerivation_eq_sum_pderiv]
  simp [Fin.sum_univ_two, Pi.single_apply]
  ring

example (t : ℝ) (s : Set ℝ) :
    HasDerivWithinAt (fun r => Real.cos r ^ 2 + Real.sin r ^ 2 - 1) 0 s t := by
  have hu : HasDerivAt (fun r => (![Real.cos r, Real.sin r] : Fin 2 → ℝ))
      (fun i => eval ![Real.cos t, Real.sin t] (![-X 1, X 0] i)) t := by
    apply hasDerivAt_pi.mpr
    intro i; fin_cases i
    · simpa using! Real.hasDerivAt_cos t
    · simpa using! Real.hasDerivAt_sin t
  have h := hasDerivWithinAt_eval_mkDerivation (s := s) (X 0 ^ 2 + X 1 ^ 2 - 1)
    ![-X 1, X 0] hu.hasDerivWithinAt
  convert! h using 1
  · simp
  · simp [mkDerivation_eq_sum_pderiv, Fin.sum_univ_two, Pi.single_apply]
    ring

-- The analytic result is field-generic: test complex differentiation too.
example (z : ℂ) : HasDerivWithinAt (fun w : ℂ => w ^ 2) (2 * z) Set.univ z := by
  have hu : HasDerivAt (fun w : ℂ => (![w] : Fin 1 → ℂ)) ![1] z := by
    apply hasDerivAt_pi.mpr
    intro i; fin_cases i
    simpa using! hasDerivAt_id z
  convert! hasDerivWithinAt_eval (s := Set.univ)
    (X 0 ^ 2 : MvPolynomial (Fin 1) ℂ) hu.hasDerivWithinAt using 1
  · simp
  · simp

-- A singleton admits arbitrary supplied velocities, including this nonzero
-- velocity for a constant curve. The conclusion is HasDerivWithinAt, not
-- the false assertion that the chosen derivWithin must equal one.
example : HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) 1 {0} 0 := by
  have hu : HasDerivWithinAt (fun _ : ℝ => (fun _ : Fin 1 => (0 : ℝ)))
      (fun _ => 1) {0} 0 := HasFDerivWithinAt.singleton
  simpa [mkDerivation_eq_sum_pderiv, Fin.sum_univ_one] using!
    hasDerivWithinAt_eval_mkDerivation (X 0 : MvPolynomial (Fin 1) ℝ) (fun _ => 1)
      (u := fun _ : ℝ => fun _ : Fin 1 => (0 : ℝ)) (s := {0}) (t := 0)
      (by simpa using! hu)

-- With no variables, the derivative is the empty sum even for an arbitrary polynomial.
example (p : MvPolynomial Empty ℝ) (x : Empty → ℝ) :
    HasFDerivAt (𝕜 := ℝ) (fun y => eval y p) 0 x := by
  simpa using hasFDerivAt_eval p x

example (F : Empty → MvPolynomial Empty ℝ) (p : MvPolynomial Empty ℝ) :
    mkDerivation ℝ F p = 0 := by simp [mkDerivation_eq_sum_pderiv]
