/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.SymmetricalComponentCoordinates
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.ZMod.Basic

/-!
# Balanced three-phase power

## i. Overview

For balanced three-phase phasors (positive abc sequence), the
neutral current vanishes, the total complex power is
`3 V conj(I)` in the RMS passive-sign convention, and line
voltages are `sqrt 3` times phase voltages with a +30 degree
shift; the reversed (acb) sequence flips the shift sign
(its neutral current also vanishes). Delta line currents satisfy the same
relations. The rotation constant comes from
`PhyslibExt.Circuits.SymmetricalComponentCoordinates`
(imported, not copied).

## ii. Key results

- `balancedPhases_neutral_power_lineVoltage`: the combined
  neutral, power, and line-voltage statements.
- `sum_complexPower_balancedPhases`: total power `3 V conj I`.
- `lineVoltage_balancedPhases`: the sqrt-3 line relation.

## iii. Table of contents

- A. Balanced three-phase systems

## iv. References

- J. D. Glover, M. S. Sarma, and T. J. Overbye, *Power System
  Analysis and Design*, sixth edition, Cengage, 2017:
  balanced three-phase power and line quantities.

## A. Balanced three-phase systems
-/

@[expose] public section

open ComplexConjugate
open PhyslibExt.Circuits.SymmetricalComponentCoordinates

namespace PhyslibExt.Circuits.BalancedThreePhase

open ComplexConjugate
open PhyslibExt.Circuits.SymmetricalComponentCoordinates

/-- Balanced positive-sequence (abc) phase set `(X, α² X, α X)`, indices `0, 1, 2` for phases
`a, b, c`: phase `b` lags `a` by `2π/3`. -/
noncomputable def balancedPhases (X : ℂ) : ZMod 3 → ℂ :=
  ![X, alpha ^ 2 * X, alpha * X]

/-- Balanced negative-sequence (acb) phase set `(X, α X, α² X)`. -/
noncomputable def reversedPhases (X : ℂ) : ZMod 3 → ℂ :=
  ![X, alpha * X, alpha ^ 2 * X]

/-- Complex power `V * conj I` absorbed by one phase, for RMS phasors under the passive sign
convention (no `1/2` factor). -/
def complexPower (V I : ℂ) : ℂ :=
  V * conj I

/-- Star connection with a neutral wire: the neutral current is the sum of the three line
(= phase) currents at the star point. -/
def neutralCurrent (I : ZMod 3 → ℂ) : ℂ :=
  ∑ p, I p

/-- Line-to-line voltages `(V_ab, V_bc, V_ca)`: `V p - V (p + 1)`. -/
def lineVoltage (V : ZMod 3 → ℂ) : ZMod 3 → ℂ :=
  fun p => V p - V (p + 1)

/-- Delta connection: from branch currents `J = (I_ab, I_bc, I_ca)`, the line currents
`(I_a, I_b, I_c) = (I_ab - I_ca, I_bc - I_ab, I_ca - I_bc)`, i.e. `J p - J (p - 1)`. -/
def deltaLineCurrent (J : ZMod 3 → ℂ) : ZMod 3 → ℂ :=
  fun p => J p - J (p - 1)

/-- Validation fixture: the balanced set `(I, α² I, α I)` with phase `c` perturbed by `δ`. -/
noncomputable def alteredPhases (I δ : ℂ) : ZMod 3 → ℂ :=
  ![I, alpha ^ 2 * I, alpha * I + δ]

/-! ### Private proof helpers (not part of the pin) -/

private lemma zmod3_cases : ∀ p : ZMod 3, p = 0 ∨ p = 1 ∨ p = 2 := by decide

private lemma sum_zmod3 (f : ZMod 3 → ℂ) : ∑ p, f p = f 0 + f 1 + f 2 := by
  have huniv : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
  have h0 : (0 : ZMod 3) ∉ ({1, 2} : Finset (ZMod 3)) := by decide
  have h1 : (1 : ZMod 3) ∉ ({2} : Finset (ZMod 3)) := by decide
  rw [huniv, Finset.sum_insert h0, Finset.sum_insert h1, Finset.sum_singleton,
    add_assoc]

private lemma zmod3_add1_0 : (0 : ZMod 3) + 1 = 1 := rfl
private lemma zmod3_add1_1 : (1 : ZMod 3) + 1 = 2 := rfl
private lemma zmod3_add1_2 : (2 : ZMod 3) + 1 = 0 := rfl
private lemma zmod3_sub1_0 : (0 : ZMod 3) - 1 = 2 := rfl
private lemma zmod3_sub1_1 : (1 : ZMod 3) - 1 = 0 := rfl
private lemma zmod3_sub1_2 : (2 : ZMod 3) - 1 = 1 := rfl

private lemma balancedPhases_zero (X : ℂ) : balancedPhases X 0 = X := rfl
private lemma balancedPhases_one (X : ℂ) : balancedPhases X 1 = alpha ^ 2 * X := rfl
private lemma balancedPhases_two (X : ℂ) : balancedPhases X 2 = alpha * X := rfl
private lemma reversedPhases_zero (X : ℂ) : reversedPhases X 0 = X := rfl
private lemma reversedPhases_one (X : ℂ) : reversedPhases X 1 = alpha * X := rfl
private lemma reversedPhases_two (X : ℂ) : reversedPhases X 2 = alpha ^ 2 * X := rfl
private lemma alteredPhases_zero (I δ : ℂ) : alteredPhases I δ 0 = I := rfl
private lemma alteredPhases_one (I δ : ℂ) : alteredPhases I δ 1 = alpha ^ 2 * I := rfl
private lemma alteredPhases_two (I δ : ℂ) : alteredPhases I δ 2 = alpha * I + δ := rfl

private lemma alpha_arg : (2 * Real.pi * Complex.I / 3 : ℂ)
    = ((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I := by
  push_cast
  ring

private lemma alpha_cubed : alpha ^ 3 = 1 := isPrimitiveRoot_alpha.pow_eq_one

private lemma alpha_re : alpha.re = -(1 / 2) := by
  show (Complex.exp (2 * Real.pi * Complex.I / 3)).re = _
  rw [alpha_arg, Complex.exp_ofReal_mul_I_re]
  have h : (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 := by ring
  rw [h, Real.cos_pi_sub, Real.cos_pi_div_three]

private lemma alpha_im : alpha.im = Real.sqrt 3 / 2 := by
  show (Complex.exp (2 * Real.pi * Complex.I / 3)).im = _
  rw [alpha_arg, Complex.exp_ofReal_mul_I_im]
  have h : (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 := by ring
  rw [h, Real.sin_pi_sub, Real.sin_pi_div_three]

private lemma alpha_ne_one : alpha ≠ 1 := by
  intro h
  have hre := alpha_re
  rw [h, Complex.one_re] at hre
  norm_num at hre

private lemma one_add_alpha : 1 + alpha + alpha ^ 2 = 0 := one_add_alpha_add_alpha_sq

private lemma norm_alpha : ‖alpha‖ = 1 := by
  show ‖Complex.exp (2 * Real.pi * Complex.I / 3)‖ = 1
  rw [alpha_arg]
  exact Complex.norm_exp_ofReal_mul_I _

private lemma conj_alpha : conj alpha = alpha ^ 2 := by
  have hmul : alpha * conj alpha = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_alpha, one_pow,
      Complex.ofReal_one]
  have e : alpha ^ 2 * (alpha * conj alpha) = conj alpha := by
    linear_combination conj alpha * alpha_cubed
  rw [hmul, mul_one] at e
  exact e.symm

private lemma conj_alpha_sq : conj (alpha ^ 2) = alpha := by
  rw [map_pow, conj_alpha]
  linear_combination alpha * alpha_cubed

private lemma alpha_sq_re : (alpha ^ 2).re = -(1 / 2) := by
  rw [pow_two, Complex.mul_re, alpha_re, alpha_im]
  have h33 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  linear_combination (-1 / 4) * h33

private lemma alpha_sq_im : (alpha ^ 2).im = -(Real.sqrt 3 / 2) := by
  rw [pow_two, Complex.mul_im, alpha_re, alpha_im]
  ring

private lemma one_sub_alpha_sq : 1 - alpha ^ 2
    = (Real.sqrt 3 : ℂ) * Complex.exp (((Real.pi / 6 : ℝ) : ℂ) * Complex.I) := by
  refine Complex.ext ?_ ?_
  · simp only [Complex.sub_re, Complex.one_re, alpha_sq_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, Real.cos_pi_div_six, Real.sin_pi_div_six]
    have h33 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
    linear_combination (-1 / 2) * h33
  · simp only [Complex.sub_im, Complex.one_im, alpha_sq_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, Real.cos_pi_div_six, Real.sin_pi_div_six]
    ring

private lemma one_sub_alpha : 1 - alpha
    = (Real.sqrt 3 : ℂ) * Complex.exp ((-(Real.pi / 6) : ℝ) * Complex.I) := by
  refine Complex.ext ?_ ?_
  · simp only [Complex.sub_re, Complex.one_re, alpha_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_six,
      Real.sin_pi_div_six]
    have h33 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
    linear_combination (-1 / 2) * h33
  · simp only [Complex.sub_im, Complex.one_im, alpha_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_six,
      Real.sin_pi_div_six]
    ring

private lemma norm_sqrt3 : ‖(Real.sqrt 3 : ℂ)‖ = Real.sqrt 3 := by
  have h : ‖(Real.sqrt 3 : ℂ)‖ = |Real.sqrt 3| := by simp
  rw [h, abs_of_nonneg (Real.sqrt_nonneg 3)]

private lemma norm_three : ‖(3 : ℂ)‖ = 3 := by simp

private lemma norm_conj_eq (B : ℂ) : ‖conj B‖ = ‖B‖ := Complex.norm_conj B

private lemma norm_three_mul_conj (A B : ℂ) :
    ‖3 * (A * conj B)‖ = 3 * (‖A‖ * ‖B‖) := by
  rw [norm_mul, norm_mul, norm_conj_eq, norm_three]

private lemma norm_exp_pi_div_six :
    ‖Complex.exp (((Real.pi / 6 : ℝ) : ℂ) * Complex.I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

private lemma norm_exp_neg_pi_div_six :
    ‖Complex.exp ((-(Real.pi / 6) : ℝ) * Complex.I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

private lemma norm_balancedPhases (X : ℂ) (p : ZMod 3) :
    ‖balancedPhases X p‖ = ‖X‖ := by
  rcases zmod3_cases p with rfl | rfl | rfl
  · rw [balancedPhases_zero]
  · rw [balancedPhases_one, norm_mul, norm_pow, norm_alpha, one_pow, one_mul]
  · rw [balancedPhases_two, norm_mul, norm_alpha, one_mul]

private lemma lineVoltage_balancedPhases_apply (V : ℂ) (p : ZMod 3) :
    lineVoltage (balancedPhases V) p
      = balancedPhases ((Real.sqrt 3 : ℂ) *
        Complex.exp (((Real.pi / 6 : ℝ) : ℂ) * Complex.I) * V) p := by
  rcases zmod3_cases p with rfl | rfl | rfl
  · simp only [lineVoltage, zmod3_add1_0, balancedPhases_zero, balancedPhases_one]
    linear_combination V * one_sub_alpha_sq
  · simp only [lineVoltage, zmod3_add1_1, balancedPhases_one, balancedPhases_two]
    linear_combination (V * alpha ^ 2) * one_sub_alpha_sq + (V * alpha) * alpha_cubed
  · simp only [lineVoltage, zmod3_add1_2, balancedPhases_two, balancedPhases_zero]
    linear_combination (V * alpha) * one_sub_alpha_sq + V * alpha_cubed

private lemma lineVoltage_reversedPhases_apply (V : ℂ) (p : ZMod 3) :
    lineVoltage (reversedPhases V) p
      = reversedPhases ((Real.sqrt 3 : ℂ) *
        Complex.exp ((-(Real.pi / 6) : ℝ) * Complex.I) * V) p := by
  rcases zmod3_cases p with rfl | rfl | rfl
  · simp only [lineVoltage, zmod3_add1_0, reversedPhases_zero, reversedPhases_one]
    linear_combination V * one_sub_alpha
  · simp only [lineVoltage, zmod3_add1_1, reversedPhases_one, reversedPhases_two]
    linear_combination (V * alpha) * one_sub_alpha
  · simp only [lineVoltage, zmod3_add1_2, reversedPhases_two, reversedPhases_zero]
    linear_combination (V * alpha ^ 2) * one_sub_alpha + V * alpha_cubed

private lemma deltaLineCurrent_balancedPhases_apply (J : ℂ) (p : ZMod 3) :
    deltaLineCurrent (balancedPhases J) p
      = balancedPhases ((Real.sqrt 3 : ℂ) *
        Complex.exp ((-(Real.pi / 6) : ℝ) * Complex.I) * J) p := by
  rcases zmod3_cases p with rfl | rfl | rfl
  · simp only [deltaLineCurrent, zmod3_sub1_0, balancedPhases_zero, balancedPhases_two]
    linear_combination J * one_sub_alpha
  · simp only [deltaLineCurrent, zmod3_sub1_1, balancedPhases_one, balancedPhases_zero]
    linear_combination (J * alpha ^ 2) * one_sub_alpha + J * alpha_cubed
  · simp only [deltaLineCurrent, zmod3_sub1_2, balancedPhases_two, balancedPhases_one]
    linear_combination (J * alpha) * one_sub_alpha

private lemma alpha_sq_exp :
    alpha ^ 2 = Complex.exp (-(2 * Real.pi * Complex.I / 3)) := by
  have h1 : (alpha : ℂ) = Complex.exp (2 * Real.pi * Complex.I / 3) := rfl
  have h2 : conj (Complex.exp (2 * Real.pi * Complex.I / 3))
      = Complex.exp (-(2 * Real.pi * Complex.I / 3)) := by
    rw [← Complex.exp_conj]
    congr 1
    rw [alpha_arg, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [← conj_alpha, h1]
  exact h2

private lemma alpha_def_exp :
    (alpha : ℂ) = Complex.exp (2 * Real.pi * Complex.I / 3) := rfl

private lemma complexPower_div (X Z : ℂ) :
    complexPower X (X / Z) = ((‖X‖ ^ 2 : ℝ) : ℂ) / conj Z := by
  simp only [complexPower, map_div₀]
  rw [← mul_div_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]

private lemma norm_polar (r t : ℝ) (hr : 0 ≤ r) :
    ‖(r : ℂ) * Complex.exp ((t : ℂ) * Complex.I)‖ = r := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  have h : ‖(r : ℂ)‖ = |r| := by simp
  rw [h, abs_of_nonneg hr]

private lemma polar_mul_conj (Vm Im θ φ : ℝ) :
    ((Vm : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
        * conj ((Im : ℂ) * Complex.exp (((θ - φ : ℝ) : ℂ) * Complex.I))
      = ((Vm * Im : ℝ) : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) := by
  have hexp : conj (Complex.exp (((θ - φ : ℝ) : ℂ) * Complex.I))
      = Complex.exp (((-(θ - φ) : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [map_mul, Complex.conj_ofReal, hexp]
  have e : (Vm : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
        * ((Im : ℂ) * Complex.exp (((-(θ - φ) : ℝ) : ℂ) * Complex.I))
      = ((Vm * Im : ℝ) : ℂ)
        * (Complex.exp ((θ : ℂ) * Complex.I)
          * Complex.exp (((-(θ - φ) : ℝ) : ℂ) * Complex.I)) := by
    push_cast
    ring
  rw [e, ← Complex.exp_add]
  congr 1
  congr 1
  push_cast
  ring

/-- The balanced set in the leaf's literal form `(V, V e^{-2πi/3}, V e^{2πi/3})`. -/
lemma balancedPhases_eq_exp (V : ℂ) :
    balancedPhases V 0 = V ∧
      balancedPhases V 1 = V * Complex.exp (-(2 * Real.pi * Complex.I / 3)) ∧
      balancedPhases V 2 = V * Complex.exp (2 * Real.pi * Complex.I / 3) := by
  refine ⟨balancedPhases_zero V, ?_, ?_⟩
  · rw [balancedPhases_one, alpha_sq_exp]
    ring
  · rw [balancedPhases_two, alpha_def_exp]
    ring

/-! ### Star connection: neutral current and total complex power -/

/-- **Zero neutral current.** Equally rotated balanced currents sum to zero at the star
point. -/
lemma neutralCurrent_balancedPhases (I : ℂ) : neutralCurrent (balancedPhases I) = 0 := by
  simp only [neutralCurrent]
  rw [sum_zmod3, balancedPhases_zero, balancedPhases_one, balancedPhases_two]
  linear_combination I * one_add_alpha

/-- The negative-sequence set also has zero neutral current. -/
lemma neutralCurrent_reversedPhases (I : ℂ) : neutralCurrent (reversedPhases I) = 0 := by
  simp only [neutralCurrent]
  rw [sum_zmod3, reversedPhases_zero, reversedPhases_one, reversedPhases_two]
  linear_combination I * one_add_alpha

/-- **Total complex power.** For balanced voltages and equally rotated currents the three
phase complex powers sum to `3 V conj I`. -/
lemma sum_complexPower_balancedPhases (V I : ℂ) :
    ∑ p, complexPower (balancedPhases V p) (balancedPhases I p) = 3 * (V * conj I) := by
  rw [sum_zmod3]
  simp only [complexPower, balancedPhases_zero, balancedPhases_one, balancedPhases_two,
    map_mul, conj_alpha, conj_alpha_sq]
  linear_combination (V * conj I) * alpha_cubed + (V * conj I) * alpha_cubed

/-! ### Line-to-line voltages: the `√3` factor and the phase-sequence sign -/

/-- Positive sequence: the line-to-line set is again balanced, `V_ab = √3 e^{iπ/6} V_a`. -/
lemma lineVoltage_balancedPhases (V : ℂ) :
    lineVoltage (balancedPhases V) =
      balancedPhases ((Real.sqrt 3 : ℂ) *
        Complex.exp (((Real.pi / 6 : ℝ) : ℂ) * Complex.I) * V) := by
  exact funext (lineVoltage_balancedPhases_apply V)

/-- **`√3` relation.** Every line-to-line magnitude is `√3` times the phase magnitude. -/
lemma norm_lineVoltage_balancedPhases (V : ℂ) (p : ZMod 3) :
    ‖lineVoltage (balancedPhases V) p‖ = Real.sqrt 3 * ‖V‖ := by
  rw [lineVoltage_balancedPhases, norm_balancedPhases, norm_mul, norm_mul,
    norm_sqrt3, norm_exp_pi_div_six, mul_one]

/-- **Balanced star, three clauses.** Zero neutral current, total complex power `3 V conj I`,
and line-to-line magnitudes `√3 ‖V‖`. -/
lemma balancedPhases_neutral_power_lineVoltage (V I : ℂ) :
    neutralCurrent (balancedPhases I) = 0 ∧
      ∑ p, complexPower (balancedPhases V p) (balancedPhases I p) = 3 * (V * conj I) ∧
      ∀ p, ‖lineVoltage (balancedPhases V) p‖ = Real.sqrt 3 * ‖V‖ := by
  exact ⟨neutralCurrent_balancedPhases I, sum_complexPower_balancedPhases V I,
    norm_lineVoltage_balancedPhases V⟩

/-- Negative sequence: `V_ab = √3 e^{-iπ/6} V_a`, the opposite rotation. -/
lemma lineVoltage_reversedPhases (V : ℂ) :
    lineVoltage (reversedPhases V) =
      reversedPhases ((Real.sqrt 3 : ℂ) *
        Complex.exp ((-(Real.pi / 6) : ℝ) * Complex.I) * V) := by
  exact funext (lineVoltage_reversedPhases_apply V)

/-- The phase-sequence sign is visible: for `V ≠ 0` the two sequences give different
`V_ab`. -/
lemma lineVoltage_balancedPhases_ne_reversed (V : ℂ) (hV : V ≠ 0) :
    lineVoltage (balancedPhases V) 0 ≠ lineVoltage (reversedPhases V) 0 := by
  have e1 : lineVoltage (balancedPhases V) 0
      = (Real.sqrt 3 : ℂ) * Complex.exp (((Real.pi / 6 : ℝ) : ℂ) * Complex.I) * V := by
    rw [lineVoltage_balancedPhases, balancedPhases_zero]
  have e2 : lineVoltage (reversedPhases V) 0
      = (Real.sqrt 3 : ℂ) * Complex.exp ((-(Real.pi / 6) : ℝ) * Complex.I) * V := by
    rw [lineVoltage_reversedPhases, reversedPhases_zero]
  rw [e1, e2]
  intro h
  have hsqrt : (Real.sqrt 3 : ℂ) ≠ 0 := by
    intro hcon
    have him0 := congrArg Complex.re hcon
    simp only [Complex.ofReal_re, Complex.zero_re] at him0
    have h3 : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    exact h3 him0
  have hcancel : Complex.exp (((Real.pi / 6 : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((-(Real.pi / 6) : ℝ) * Complex.I) := by
    have h2 : Complex.exp (((Real.pi / 6 : ℝ) : ℂ) * Complex.I)
          * ((Real.sqrt 3 : ℂ) * V)
        = Complex.exp ((-(Real.pi / 6) : ℝ) * Complex.I)
          * ((Real.sqrt 3 : ℂ) * V) := by
      linear_combination h
    exact mul_right_cancel₀ (mul_ne_zero hsqrt hV) h2
  have him := congrArg Complex.im hcancel
  simp only [Complex.exp_ofReal_mul_I_im, Real.sin_neg, Real.sin_pi_div_six] at him
  norm_num at him

/-- Star connection, line quantities: `|S| = √3 V_L I_L` with `V_L = ‖V_ab‖` and line current
`I_L = ‖I_a‖` (the phase current). -/
lemma norm_sum_complexPower_star (V I : ℂ) :
    ‖∑ p, complexPower (balancedPhases V p) (balancedPhases I p)‖ =
      Real.sqrt 3 * ‖lineVoltage (balancedPhases V) 0‖ * ‖balancedPhases I 0‖ := by
  rw [sum_complexPower_balancedPhases, norm_lineVoltage_balancedPhases,
    balancedPhases_zero, norm_three_mul_conj]
  have h33 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  generalize ‖V‖ = a
  generalize ‖I‖ = b
  linear_combination (-(a * b)) * h33

/-! ### Delta connection -/

/-- Delta line currents always sum to zero (there is no neutral path). -/
lemma sum_deltaLineCurrent (J : ZMod 3 → ℂ) : ∑ p, deltaLineCurrent J p = 0 := by
  rw [sum_zmod3]
  simp only [deltaLineCurrent, zmod3_sub1_0, zmod3_sub1_1, zmod3_sub1_2]
  ring

/-- Balanced delta: line currents are balanced, `I_a = √3 e^{-iπ/6} I_ab`. -/
lemma deltaLineCurrent_balancedPhases (J : ℂ) :
    deltaLineCurrent (balancedPhases J) =
      balancedPhases ((Real.sqrt 3 : ℂ) *
        Complex.exp ((-(Real.pi / 6) : ℝ) * Complex.I) * J) := by
  exact funext (deltaLineCurrent_balancedPhases_apply J)

/-- Balanced delta: every line current magnitude is `√3` times the branch magnitude. -/
lemma norm_deltaLineCurrent_balancedPhases (J : ℂ) (p : ZMod 3) :
    ‖deltaLineCurrent (balancedPhases J) p‖ = Real.sqrt 3 * ‖J‖ := by
  rw [deltaLineCurrent_balancedPhases, norm_balancedPhases, norm_mul, norm_mul,
    norm_sqrt3, norm_exp_neg_pi_div_six, mul_one]

/-- Balanced delta: branch `p` carries `J_p` under line-to-line voltage `V_LL,p`; the total
complex power is `3 V_ab conj I_ab`. -/
lemma sum_complexPower_delta (V J : ℂ) :
    ∑ p, complexPower (lineVoltage (balancedPhases V) p) (balancedPhases J p) =
      3 * (lineVoltage (balancedPhases V) 0 * conj J) := by
  rw [lineVoltage_balancedPhases, sum_complexPower_balancedPhases, balancedPhases_zero]

/-- Delta connection, line quantities: `|S| = √3 V_L I_L` with `V_L = ‖V_ab‖` and line current
`I_L = ‖I_a‖`. -/
lemma norm_sum_complexPower_delta (V J : ℂ) :
    ‖∑ p, complexPower (lineVoltage (balancedPhases V) p) (balancedPhases J p)‖ =
      Real.sqrt 3 * ‖lineVoltage (balancedPhases V) 0‖ *
        ‖deltaLineCurrent (balancedPhases J) 0‖ := by
  rw [sum_complexPower_delta, norm_deltaLineCurrent_balancedPhases, norm_three_mul_conj]
  have h33 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  generalize ‖lineVoltage (balancedPhases V) 0‖ = a
  generalize ‖J‖ = b
  linear_combination (-(a * b)) * h33

/-! ### Power factor -/

/-- With `V = Vm e^{iθ}`, `I = Im e^{i(θ - φ)}`, `Vm, Im ≥ 0`: real power `3 Vm Im cos φ`,
reactive power `3 Vm Im sin φ`, and in line quantities `P = √3 V_L I_L cos φ`. -/
lemma sum_complexPower_polar (Vm Im θ φ : ℝ) (hVm : 0 ≤ Vm) (hIm : 0 ≤ Im) :
    (∑ p, complexPower (balancedPhases ((Vm : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) p)
        (balancedPhases ((Im : ℂ) * Complex.exp (((θ - φ : ℝ) : ℂ) * Complex.I)) p)).re =
        3 * Vm * Im * Real.cos φ ∧
      (∑ p, complexPower (balancedPhases ((Vm : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) p)
        (balancedPhases ((Im : ℂ) * Complex.exp (((θ - φ : ℝ) : ℂ) * Complex.I)) p)).im =
        3 * Vm * Im * Real.sin φ ∧
      (∑ p, complexPower (balancedPhases ((Vm : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) p)
        (balancedPhases ((Im : ℂ) * Complex.exp (((θ - φ : ℝ) : ℂ) * Complex.I)) p)).re =
        Real.sqrt 3 *
          ‖lineVoltage (balancedPhases ((Vm : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) 0‖ *
          ‖balancedPhases ((Im : ℂ) * Complex.exp (((θ - φ : ℝ) : ℂ) * Complex.I)) 0‖ *
          Real.cos φ := by
  rw [sum_complexPower_balancedPhases, polar_mul_conj]
  refine ⟨?_, ?_, ?_⟩
  · have h3 : (3 : ℂ) = ((3 : ℝ) : ℂ) := by norm_cast
    rw [h3]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    ring
  · have h3 : (3 : ℂ) = ((3 : ℝ) : ℂ) := by norm_cast
    rw [h3]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    ring
  · rw [norm_lineVoltage_balancedPhases, balancedPhases_zero, norm_polar Vm θ hVm,
      norm_polar Im (θ - φ) hIm]
    have h3 : (3 : ℂ) = ((3 : ℝ) : ℂ) := by norm_cast
    rw [h3]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    have h33 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
    linear_combination (-(Vm * Im * Real.cos φ)) * h33

/-! ### Validation: balanced loads, an altered phase -/

/-- Balanced load `I_p = V_p / Z`, `Z ≠ 0`: total complex power `3 ‖V‖² / conj Z`. -/
lemma sum_complexPower_impedance (V Z : ℂ) (hZ : Z ≠ 0) :
    ∑ p, complexPower (balancedPhases V p) (balancedPhases V p / Z) =
      3 * ((‖V‖ ^ 2 : ℝ) : ℂ) / conj Z := by
  have _hz := hZ
  rw [sum_zmod3]
  simp only [complexPower_div, norm_balancedPhases]
  ring

/-- Resistive balanced load `Z = R > 0`: the total power is real, `3 ‖V‖² / R`. -/
lemma sum_complexPower_resistive (V : ℂ) (R : ℝ) (hR : 0 < R) :
    ∑ p, complexPower (balancedPhases V p) (balancedPhases V p / (R : ℂ)) =
      ((3 * ‖V‖ ^ 2 / R : ℝ) : ℂ) := by
  have hR0 : (R : ℂ) ≠ 0 := by
    have hR0' : R ≠ 0 := ne_of_gt hR
    exact_mod_cast hR0'
  have h := sum_complexPower_impedance V (R : ℂ) hR0
  have h3 : (3 : ℂ) = ((3 : ℝ) : ℂ) := by norm_cast
  rw [h, Complex.conj_ofReal, h3, ← Complex.ofReal_mul, ← Complex.ofReal_div]

/-- Reactive balanced load `Z = i X`, `X ≠ 0`: the total power is purely reactive,
`(3 ‖V‖² / X) i` (absorbed reactive power for an inductive `X > 0`). -/
lemma sum_complexPower_reactive (V : ℂ) (X : ℝ) (hX : X ≠ 0) :
    ∑ p, complexPower (balancedPhases V p) (balancedPhases V p / ((X : ℂ) * Complex.I)) =
      ((3 * ‖V‖ ^ 2 / X : ℝ) : ℂ) * Complex.I := by
  have hXc : (X : ℂ) ≠ 0 := by exact_mod_cast hX
  have hZ : (X : ℂ) * Complex.I ≠ 0 := mul_ne_zero hXc Complex.I_ne_zero
  have h := sum_complexPower_impedance V ((X : ℂ) * Complex.I) hZ
  rw [h, map_mul, Complex.conj_ofReal, Complex.conj_I]
  have hC : (X : ℂ) * -Complex.I ≠ 0 :=
    mul_ne_zero hXc (neg_ne_zero.mpr Complex.I_ne_zero)
  rw [div_eq_iff hC]
  have hD : ((3 * ‖V‖ ^ 2 / X : ℝ) : ℂ) * (X : ℂ) = 3 * ((‖V‖ ^ 2 : ℝ) : ℂ) := by
    have h3 : (3 : ℂ) = ((3 : ℝ) : ℂ) := by norm_cast
    rw [h3, ← Complex.ofReal_mul, ← Complex.ofReal_mul, div_mul_cancel₀ _ hX]
  linear_combination (((3 * ‖V‖ ^ 2 / X : ℝ) : ℂ) * (X : ℂ)) * Complex.I_mul_I - hD

/-- One altered phase: perturbing phase `c` by `δ` leaves neutral current `δ`. -/
lemma neutralCurrent_altered (I δ : ℂ) :
    neutralCurrent (alteredPhases I δ) = δ := by
  simp only [neutralCurrent]
  rw [sum_zmod3, alteredPhases_zero, alteredPhases_one, alteredPhases_two]
  linear_combination I * one_add_alpha

/-- One altered phase with `δ ≠ 0` gives a nonzero neutral sum. -/
lemma neutralCurrent_altered_ne (I δ : ℂ) (hδ : δ ≠ 0) :
    neutralCurrent (alteredPhases I δ) ≠ 0 := by
  rw [neutralCurrent_altered]
  exact hδ

end PhyslibExt.Circuits.BalancedThreePhase
