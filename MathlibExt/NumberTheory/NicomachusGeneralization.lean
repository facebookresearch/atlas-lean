/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# The Kim–Stolarsky integers

Seon-Hong Kim and Kenneth B. Stolarsky, "A Balanced Three or More-term Generalization of
Nicomachus' Identity", *INTEGERS* 26 (2026), Article A98, study the integers `u_k` given by the
power series expansion
`(1 + 502x + x²)/((1 - x)(1 - 398x + x²)) = ∑_{k ≥ 1} u_k x^{k-1} = 1 + 901x + 359101x² + ⋯`.
This file defines them and proves their closed form
`u_k = (5(10 - 3√11)^{2k-1} + 5(10 + 3√11)^{2k-1} - 56)/44` for `k ≥ 1`, and the nonlinear
recurrence `u_{k+1} = 252 + 199u_k + 30√((3 + 2u_k)(23 + 22u_k))` for `k ≥ 1`. In the preprint
arXiv:2511.15133v1 of the paper (titled "A Balanced Three-term Generalization of Nicomachus'
Identity") the closed form and the recurrence are equations (14) and (15) of Proposition 6.

## Main declarations

* `nicomachusU k`: the coefficient `u_k` of `x^{k-1}`, read as the constant coefficient when
  `k = 0`.
* `nicomachusU_eq_closedForm`: the closed form of `u_k` for `k ≥ 1`.
* `nicomachusU_succ_eq`: the recurrence expressing `u_{k+1}` in terms of `u_k` for `k ≥ 1`.

## Proof

The denominator is `(1 - x)(1 - 398x + x²) = 1 - 399x + 399x² - x³`, so multiplying the series by
it shows that the coefficients `c_n = u_{n+1}` satisfy `c_0 = 1`, `c_1 = 901`, `c_2 = 359101` and
`c_{n+3} = 399 c_{n+2} - 399 c_{n+1} + c_n`. The numbers `(10 ± 3√11)² = 199 ± 60√11` are the
roots of `t² - 398t + 1`, and `t³ - 399t² + 399t - 1 = (t - 1)(t² - 398t + 1)`, so the closed form
satisfies the same recurrence and has the same three initial values. The paper argues instead with
the partial sums of the series, which it computes from the closed form.

As in the paper, the nonlinear recurrence follows from the closed form. Put
`A = (10 - 3√11)^{2k-1}` and `B = (10 + 3√11)^{2k-1}`, so that `u_k = (5A + 5B - 56)/44`. Since
`(10 - 3√11)(10 + 3√11) = 1`, `AB = 1`, hence
`(3 + 2u_k)(23 + 22u_k) = 25((A + B)² - 4)/44 = 25(B - A)²/44`, whose square root is
`5√11 (B - A)/22` because `0 ≤ A ≤ B`. Passing from `k` to `k + 1` multiplies `A` by
`(10 - 3√11)² = 199 - 60√11` and `B` by `(10 + 3√11)² = 199 + 60√11`, which gives the recurrence.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.NicomachusGeneralizationWanted

/-- **The Kim–Stolarsky integers $u_k$.** For a natural number $k$, $u_k$ is the coefficient of
$x^{k-1}$ in the power series expansion over $\mathbb{Q}$ of
$$\frac{1 + 502x + x^2}{(1 - x)(1 - 398x + x^2)}.$$
For $k \ge 1$ these are the integers $u_k$ of Proposition 1 of Kim and Stolarsky; for $k = 0$ the
exponent $k - 1$ is read as $0$, so $u_0 = u_1 = 1$. -/
noncomputable def nicomachusU (k : ℕ) : ℚ :=
  PowerSeries.coeff (k - 1)
    ((1 + 502 * PowerSeries.X + PowerSeries.X ^ 2) *
      ((1 - PowerSeries.X) *
        (1 - 398 * PowerSeries.X + PowerSeries.X ^ 2))⁻¹)

open PowerSeries

/-! ### The coefficients of the generating function -/

/-- The generating function `(1 + 502X + X²)/((1 - X)(1 - 398X + X²))` of the integers `u_k`. -/
private noncomputable def generatingFunction : ℚ⟦X⟧ :=
  (1 + 502 * X + X ^ 2) * ((1 - X) * (1 - 398 * X + X ^ 2))⁻¹

/-- `u_{n+1}` is the coefficient of `X^n` in the generating function. -/
private lemma nicomachusU_add_one_eq_coeff (n : ℕ) :
    nicomachusU (n + 1) = coeff n generatingFunction :=
  rfl

/-- Multiplying the generating function by its denominator gives back its numerator. -/
private lemma generatingFunction_mul_den :
    generatingFunction * ((1 - X) * (1 - 398 * X + X ^ 2)) = 1 + 502 * X + X ^ 2 := by
  have hden : constantCoeff ((1 - X) * (1 - 398 * X + X ^ 2) : ℚ⟦X⟧) ≠ 0 := by simp
  rw [generatingFunction, mul_assoc, PowerSeries.inv_mul_cancel _ hden, mul_one]

/-- Multiplication by the denominator, expanded as `1 - 399X + 399X² - X³`. -/
private lemma mul_den_eq (φ : ℚ⟦X⟧) :
    φ * ((1 - X) * (1 - 398 * X + X ^ 2)) =
      φ - 399 * (X * φ) + 399 * (X ^ 2 * φ) - X ^ 3 * φ := by
  ring

private lemma coeff_generatingFunction_zero : coeff 0 generatingFunction = 1 := by
  have h := congrArg (coeff 0) generatingFunction_mul_den
  rw [mul_den_eq] at h
  simpa using h

private lemma coeff_generatingFunction_one : coeff 1 generatingFunction = 901 := by
  have h := congrArg (coeff 1) generatingFunction_mul_den
  rw [mul_den_eq] at h
  simp [coeff_X_pow_mul', coeff_X_pow, coeff_generatingFunction_zero] at h
  linarith

private lemma coeff_generatingFunction_two : coeff 2 generatingFunction = 359101 := by
  have h := congrArg (coeff 2) generatingFunction_mul_den
  rw [mul_den_eq] at h
  simp [coeff_X_pow_mul', coeff_X_pow, coeff_X, coeff_generatingFunction_zero,
    coeff_generatingFunction_one] at h
  linarith

/-- The coefficients of the generating function satisfy the linear recurrence with
characteristic polynomial `t³ - 399t² + 399t - 1`. -/
private lemma coeff_generatingFunction_add_three (n : ℕ) :
    coeff (n + 3) generatingFunction =
      399 * coeff (n + 2) generatingFunction - 399 * coeff (n + 1) generatingFunction +
        coeff n generatingFunction := by
  have h := congrArg (coeff (n + 3)) generatingFunction_mul_den
  have h₁ : coeff (n + 3) (X * generatingFunction) = coeff (n + 2) generatingFunction :=
    coeff_succ_X_mul (n + 2) generatingFunction
  have h₂ : coeff (n + 3) (X ^ 2 * generatingFunction) = coeff (n + 1) generatingFunction :=
    coeff_X_pow_mul generatingFunction 2 (n + 1)
  have h₃ : coeff (n + 3) (X ^ 3 * generatingFunction) = coeff n generatingFunction :=
    coeff_X_pow_mul generatingFunction 3 n
  rw [mul_den_eq, map_sub, map_add, map_sub, coeff_ofNat_mul, coeff_ofNat_mul, h₁, h₂, h₃] at h
  simp [coeff_X_pow, coeff_X, coeff_one] at h
  linarith

/-! ### The closed form -/

/-- The closed form `(5(10 - 3√11)^{2n+1} + 5(10 + 3√11)^{2n+1} - 56)/44` of `u_{n+1}`. -/
private noncomputable def closedForm (n : ℕ) : ℝ :=
  (5 * (10 - 3 * Real.sqrt 11) ^ (2 * n + 1) + 5 * (10 + 3 * Real.sqrt 11) ^ (2 * n + 1) - 56) /
    44

private lemma sqrt_eleven_sq : Real.sqrt 11 ^ 2 = 11 :=
  Real.sq_sqrt (by norm_num)

/-- If `a²` is a root of `t² - 398t + 1`, the odd powers of `a` satisfy the linear recurrence with
characteristic polynomial `(t - 1)(t² - 398t + 1) = t³ - 399t² + 399t - 1`. -/
private lemma pow_add_three_of_sq_root {a : ℝ} (ha : (a ^ 2) ^ 2 - 398 * a ^ 2 + 1 = 0) (n : ℕ) :
    a ^ (2 * (n + 3) + 1) =
      399 * a ^ (2 * (n + 2) + 1) - 399 * a ^ (2 * (n + 1) + 1) + a ^ (2 * n + 1) := by
  linear_combination (a ^ (2 * n + 1) * (a ^ 2 - 1)) * ha

private lemma closedForm_zero : closedForm 0 = 1 := by
  unfold closedForm
  ring

private lemma closedForm_one : closedForm 1 = 901 := by
  unfold closedForm
  linear_combination (2700 / 44 : ℝ) * sqrt_eleven_sq

private lemma closedForm_two : closedForm 2 = 359101 := by
  unfold closedForm
  linear_combination ((40500 * Real.sqrt 11 ^ 2 + 1345500) / 44) * sqrt_eleven_sq

private lemma closedForm_add_three (n : ℕ) :
    closedForm (n + 3) = 399 * closedForm (n + 2) - 399 * closedForm (n + 1) + closedForm n := by
  have hplus := pow_add_three_of_sq_root (a := 10 + 3 * Real.sqrt 11)
    (by linear_combination (81 * Real.sqrt 11 ^ 2 + 1080 * Real.sqrt 11 + 2709) * sqrt_eleven_sq) n
  have hminus := pow_add_three_of_sq_root (a := 10 - 3 * Real.sqrt 11)
    (by linear_combination (81 * Real.sqrt 11 ^ 2 - 1080 * Real.sqrt 11 + 2709) * sqrt_eleven_sq) n
  unfold closedForm
  rw [hplus, hminus]
  ring

/-- Every coefficient of the generating function equals the closed form. -/
private lemma cast_coeff_generatingFunction :
    ∀ n : ℕ, ((coeff n generatingFunction : ℚ) : ℝ) = closedForm n
  | 0 => by simp [coeff_generatingFunction_zero, closedForm_zero]
  | 1 => by simp [coeff_generatingFunction_one, closedForm_one]
  | 2 => by simp [coeff_generatingFunction_two, closedForm_two]
  | n + 3 => by
    rw [coeff_generatingFunction_add_three, closedForm_add_three]
    push_cast
    rw [cast_coeff_generatingFunction n, cast_coeff_generatingFunction (n + 1),
      cast_coeff_generatingFunction (n + 2)]

/-- **Closed form for the Kim–Stolarsky integers $u_k$.** Let $u_k$ be the coefficient of
$x^{k-1}$ in the power series expansion of $(1 + 502x + x^2)/((1 - x)(1 - 398x + x^2))$. For every
integer $k \ge 1$,
$$u_k = \frac{5(10 - 3\sqrt{11})^{2k-1} + 5(10 + 3\sqrt{11})^{2k-1} - 56}{44}.$$

Source: Seon-Hong Kim and Kenneth B. Stolarsky, "A Balanced
Three or More-term Generalization of Nicomachus' Identity", Proposition 1. -/
theorem nicomachusU_eq_closedForm (k : ℕ) (hk : 1 ≤ k) :
    (nicomachusU k : ℝ) =
      (5 * (10 - 3 * Real.sqrt 11) ^ (2 * k - 1) +
        5 * (10 + 3 * Real.sqrt 11) ^ (2 * k - 1) - 56) / 44 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega, nicomachusU_add_one_eq_coeff,
    cast_coeff_generatingFunction]
  rfl

/-! ### The recurrence -/

/-- Let `A ≤ B` with `AB = 1` (for instance `A = (10 - 3√11)^n` and `B = (10 + 3√11)^n`), and let
`u = (5A + 5B - 56)/44`. Then `(3 + 2u)(23 + 22u) = (5√11 (B - A)/22)²`, and multiplying `A` and
`B` by `(10 - 3√11)²` and `(10 + 3√11)²` turns `u` into `252 + 199u + 30 · 5√11 (B - A)/22`. -/
private lemma closedForm_recurrence {A B : ℝ} (hAB : A * B = 1) (hle : A ≤ B) :
    (5 * (A * (10 - 3 * Real.sqrt 11) ^ 2) + 5 * (B * (10 + 3 * Real.sqrt 11) ^ 2) - 56) / 44 =
      252 + 199 * ((5 * A + 5 * B - 56) / 44) +
        30 * Real.sqrt ((3 + 2 * ((5 * A + 5 * B - 56) / 44)) *
          (23 + 22 * ((5 * A + 5 * B - 56) / 44))) := by
  have hprod : (3 + 2 * ((5 * A + 5 * B - 56) / 44)) * (23 + 22 * ((5 * A + 5 * B - 56) / 44)) =
      (5 * Real.sqrt 11 * (B - A) / 22) ^ 2 := by
    linear_combination (25 / 11 : ℝ) * hAB - (25 / 484 : ℝ) * (B - A) ^ 2 * sqrt_eleven_sq
  have hnonneg : 0 ≤ 5 * Real.sqrt 11 * (B - A) / 22 :=
    div_nonneg (mul_nonneg (by positivity) (sub_nonneg.2 hle)) (by norm_num)
  rw [hprod, Real.sqrt_sq hnonneg]
  linear_combination (45 / 44 : ℝ) * (A + B) * sqrt_eleven_sq

/-- **Recurrence for the Kim–Stolarsky integers $u_k$.** Let $u_k$ be the coefficient of
$x^{k-1}$ in the power series expansion of $(1 + 502x + x^2)/((1 - x)(1 - 398x + x^2))$. For every
integer $k \ge 1$,
$$u_{k+1} = 252 + 199u_k + 30\sqrt{(3 + 2u_k)(23 + 22u_k)}.$$

Source: Seon-Hong Kim and Kenneth B. Stolarsky, "A Balanced
Three or More-term Generalization of Nicomachus' Identity", Proposition 1. -/
theorem nicomachusU_succ_eq (k : ℕ) (hk : 1 ≤ k) :
    (nicomachusU (k + 1) : ℝ) =
      252 + 199 * (nicomachusU k : ℝ) +
        30 * Real.sqrt ((3 + 2 * (nicomachusU k : ℝ)) *
          (23 + 22 * (nicomachusU k : ℝ))) := by
  have hmul : (10 - 3 * Real.sqrt 11) * (10 + 3 * Real.sqrt 11) = 1 := by
    linear_combination (-9 : ℝ) * sqrt_eleven_sq
  have hnonneg : 0 ≤ 10 - 3 * Real.sqrt 11 := by
    nlinarith [sqrt_eleven_sq, Real.sqrt_nonneg 11]
  rw [nicomachusU_eq_closedForm (k + 1) (by omega), nicomachusU_eq_closedForm k hk,
    show 2 * (k + 1) - 1 = 2 * k - 1 + 2 by omega, pow_add, pow_add]
  exact closedForm_recurrence (by rw [← mul_pow, hmul, one_pow])
    (pow_le_pow_left₀ hnonneg (by linarith [Real.sqrt_nonneg 11]) _)

end MathlibExt.NumberTheory.NicomachusGeneralizationWanted
