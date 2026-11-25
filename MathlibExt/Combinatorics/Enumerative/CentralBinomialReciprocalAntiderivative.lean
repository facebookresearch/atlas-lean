/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# An antiderivative of the power-weighted reciprocal central binomial series

We prove Lemma 5 of Rimer Zurita, *Elementary Functions Associated with Series Involving
Reciprocals of Central Binomial Coefficients*, Journal of Integer Sequences 27 (2024),
Article 24.6.8. The coefficient recurrence gives a polynomial differential identity for
`Q_l`; evaluating it at `4` makes the quotient in the definition of `P_l` a polynomial.
-/

namespace MetaMathlibExt

@[expose] public section

open Polynomial

/-- **Closed form of the reciprocal central binomial series.** For every real number $x$, let
$$
H(x) = \frac{4\sqrt{x}\,\arcsin(\sqrt{x}/2)}{(4 - x)\sqrt{4 - x}} + \frac{4}{4 - x}.
$$
The formula is meant for $0 \le x < 4$, where by the paper
$H(x) = \sum_{n \ge 0} x^n / \binom{2n}{n}$.

Source: Rimer Zurita, *Elementary Functions Associated with Series Involving Reciprocals of
Central Binomial Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.6.8,
Section 2. -/
noncomputable def centralBinomReciprocalH (x : ℝ) : ℝ :=
  4 * √x * Real.arcsin (√x / 2) / ((4 - x) * √(4 - x)) + 4 / (4 - x)

/-- **Coefficients of Zurita's Q-polynomials.** For natural numbers $l \ge 1$ and $k$, the rational
number $q_k = q_{l,k}$ is given by $q_l = -4/l$, by $q_k = \frac{4k + 6}{k} q_{k+1}$ for
$1 \le k < l$, by $q_0 = -12 q_1$, and by $q_k = 0$ for $k > l$. These are the coefficients of
Zurita's polynomial $Q_l$. For $l = 0$ the definition gives $q_{0,k} = 0$ for every $k$.

Source: Rimer Zurita, *Elementary Functions Associated with Series Involving Reciprocals of
Central Binomial Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.6.8,
Definition 1. -/
def arcsinAntiderivQCoeff (l k : ℕ) : ℚ :=
  if l < k then 0
  else if k = 0 then -12 * ((-4 / l) * ∏ i ∈ Finset.Ico 1 l, ((4 * i + 6 : ℚ) / i))
  else (-4 / l) * ∏ i ∈ Finset.Ico k l, ((4 * i + 6 : ℚ) / i)

/-- **Leading coefficient of a Q-polynomial.** For every natural number $l \ge 1$, the coefficient
$q_l = q_{l,l}$ of $x^l$ in Zurita's polynomial $Q_l$ equals $-4/l$.

Source: Rimer Zurita, *Elementary Functions Associated with Series Involving Reciprocals of
Central Binomial Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.6.8,
Definition 1. -/
theorem arcsinAntiderivQCoeff_self {l : ℕ} (hl : 1 ≤ l) : arcsinAntiderivQCoeff l l = -4 / l := by
  simp [arcsinAntiderivQCoeff, show l ≠ 0 by omega]

/-- **Recursion for the coefficients of a Q-polynomial.** Write $q_k = q_{l,k}$ for the coefficient
of $x^k$ in Zurita's polynomial $Q_l$. For all natural numbers $k$ and $l$ with $1 \le k < l$,
$$q_k = \frac{4k + 6}{k}\, q_{k+1}.$$

Source: Rimer Zurita, *Elementary Functions Associated with Series Involving Reciprocals of
Central Binomial Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.6.8,
Definition 1. -/
theorem arcsinAntiderivQCoeff_of_lt {l k : ℕ} (hk : 1 ≤ k) (hkl : k < l) :
    arcsinAntiderivQCoeff l k = (4 * k + 6) / k * arcsinAntiderivQCoeff l (k + 1) := by
  simp only [arcsinAntiderivQCoeff, show ¬ l < k by omega, show ¬ l < k + 1 by omega,
    show k ≠ 0 by omega, show k + 1 ≠ 0 by omega, ↓reduceIte,
    Finset.prod_eq_prod_Ico_succ_bot hkl]
  ring

/-- **Constant coefficient of a Q-polynomial.** For every natural number $l \ge 1$, the constant
coefficient $q_0$ and the coefficient $q_1$ of $x$ in Zurita's polynomial $Q_l$ satisfy
$q_0 = -12 q_1$.

Source: Rimer Zurita, *Elementary Functions Associated with Series Involving Reciprocals of
Central Binomial Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.6.8,
Definition 1. -/
theorem arcsinAntiderivQCoeff_zero {l : ℕ} (hl : 1 ≤ l) :
    arcsinAntiderivQCoeff l 0 = -12 * arcsinAntiderivQCoeff l 1 := by
  simp [arcsinAntiderivQCoeff, show ¬ l < 1 by omega]

/-- **Zurita's Q-polynomials.** For a natural number $l \ge 1$, $Q_l$ is the polynomial with
rational coefficients $Q_l(x) = \sum_{i=0}^{l} q_i x^i$, where $q_l = -4/l$,
$q_i = \frac{4i + 6}{i} q_{i+1}$ for $1 \le i < l$, and $q_0 = -12 q_1$. For $l = 0$ it is the
constant polynomial $Q_0 = 8$.

Source: Rimer Zurita, *Elementary Functions Associated with Series Involving Reciprocals of
Central Binomial Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.6.8,
Definition 1. -/
noncomputable def arcsinAntiderivQ (l : ℕ) : ℚ[X] :=
  if l = 0 then C 8 else ∑ k ∈ Finset.range (l + 1), C (arcsinAntiderivQCoeff l k) * X ^ k

/-- **Zurita's arcsine antiderivative constants.** For a natural number $l \ge 1$, the rational
constant $C_l$ is $C_l = -q_0/2$, where $q_0$ is the constant coefficient of Zurita's polynomial
$Q_l$. For $l = 0$ it is $C_0 = -4$.

Source: Rimer Zurita, *Elementary Functions Associated with Series Involving Reciprocals of
Central Binomial Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.6.8,
Definition 1. -/
def arcsinAntiderivC (l : ℕ) : ℚ :=
  if l = 0 then -4 else -arcsinAntiderivQCoeff l 0 / 2

private theorem coeff_arcsinAntiderivQ {l : ℕ} (hl : 1 ≤ l) (k : ℕ) :
    (arcsinAntiderivQ l).coeff k = arcsinAntiderivQCoeff l k := by
  classical
  rw [arcsinAntiderivQ, ite_eq_right (by omega), finsetSum_coeff]
  simp only [coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range]
  split_ifs with h
  · rfl
  · simp [arcsinAntiderivQCoeff, show l < k by omega]

-- Zurita's equation (3), with the denominators in the polynomial identity cleared.
private theorem arcsinAntiderivQ_mul_derivative {l : ℕ} (hl : 1 ≤ l) :
    X * (C 4 - X) * derivative (arcsinAntiderivQ l) + 2 * arcsinAntiderivQ l +
      C (arcsinAntiderivC l) * (C 4 - X) = C 4 * X ^ (l + 1) := by
  have hC : arcsinAntiderivC l = -arcsinAntiderivQCoeff l 0 / 2 := by
    simp [arcsinAntiderivC, show l ≠ 0 by omega]
  have h₀ := arcsinAntiderivQCoeff_zero hl
  have h₁ := arcsinAntiderivQCoeff_self hl
  have hAbove (k : ℕ) (hk : l < k) : arcsinAntiderivQCoeff l k = 0 := by
    simp [arcsinAntiderivQCoeff, hk]
  calc
    _ = C 4 * (X * derivative (arcsinAntiderivQ l)) - X * (X * derivative (arcsinAntiderivQ l)) +
          C 2 * arcsinAntiderivQ l + C (4 * arcsinAntiderivC l) - C (arcsinAntiderivC l) * X := by
        simp only [map_ofNat, map_mul]
        ring
    _ = _ := by
      ext k
      simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_C, coeff_X_pow,
        coeff_arcsinAntiderivQ hl]
      -- The constant and linear coefficients give the relation between C, q₀ and q₁.
      rcases k with _ | _ | k
      · simp [hC]
        ring
      · simp [coeff_X_mul, coeff_derivative, coeff_arcsinAntiderivQ hl, hC, h₀,
          show l ≠ 0 by omega]
        ring
      · simp only [coeff_X_mul, coeff_derivative, coeff_arcsinAntiderivQ hl,
          Nat.cast_add, Nat.cast_one, Nat.succ_ne_zero, ite_false, coeff_X,
          show 1 ≠ k + 1 + 1 by omega, mul_zero, add_zero, sub_zero]
        rcases lt_trichotomy (k + 1) l with hk | hk | hk
        · rw [ite_eq_right (by omega : k + 1 + 1 ≠ l + 1), mul_zero]
          have h := arcsinAntiderivQCoeff_of_lt (k := k + 1) (by omega) hk
          push_cast at h
          have hk₀ : (k : ℚ) + 1 ≠ 0 := by positivity
          field_simp [hk₀] at h
          linear_combination -h
        · subst l
          rw [ite_eq_left rfl, hAbove (k + 1 + 1) (by omega), h₁]
          push_cast
          have hk₀ : (k : ℚ) + 1 ≠ 0 := by positivity
          field_simp [hk₀]
          ring
        · rw [ite_eq_right (by omega : k + 1 + 1 ≠ l + 1),
            hAbove (k + 1 + 1) (by omega), hAbove (k + 1) hk]
          ring

/-- **Antiderivative of $x^l H(x)$.** Let $l \ge 1$, let $Q_l$ and $C_l$ be Zurita's polynomial and
constant, and let $H$ be the closed form of the reciprocal central binomial series. Then there
is a polynomial $P$ with rational coefficients such that $P(0) = 0$ and
$2(4 - x) P'(x) = 8x^l - Q_l(x)$ as polynomials. Moreover, for every such $P$ and every real
number $x$ with $0 < x < 4$, the real function
$$
F(y) = P(y) + C_l \arcsin(\sqrt{y}/2)^2 +
\frac{\arcsin(\sqrt{y}/2)\,\sqrt{y}}{\sqrt{4 - y}}\, Q_l(y)
$$
has derivative $x^l H(x)$ at $x$.

Such a $P$ is unique: it is the paper's polynomial $P_l$ (Definition 2), and $F$ is an
antiderivative of $x^l H(x)$ on $0 < x < 4$.

Source: Rimer Zurita, *Elementary Functions Associated with Series Involving Reciprocals of
Central Binomial Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.6.8,
Lemma 5 (`jis-2024-24.6.8-lem-5`). -/
theorem hasDerivAt_arcsinAntiderivP_pow_mul_centralBinomReciprocalH {l : ℕ}
    (hl : 1 ≤ l) :
    (∃ P : ℚ[X], P.eval 0 = 0 ∧
      2 * (C 4 - X) * derivative P = 8 * X ^ l - arcsinAntiderivQ l) ∧
    ∀ P : ℚ[X], P.eval 0 = 0 → 2 * (C 4 - X) * derivative P = 8 * X ^ l - arcsinAntiderivQ l →
      ∀ x : ℝ, 0 < x → x < 4 →
        HasDerivAt (fun y : ℝ => aeval y P + (arcsinAntiderivC l : ℝ) * Real.arcsin (√y / 2) ^ 2 +
            Real.arcsin (√y / 2) * √y / √(4 - y) * aeval y (arcsinAntiderivQ l))
          (x ^ l * centralBinomReciprocalH x) x := by
  have hQ := arcsinAntiderivQ_mul_derivative hl
  constructor
  · -- Evaluating the differential identity at 4 gives the root needed for divisibility.
    have h4 : (arcsinAntiderivQ l).eval 4 = 8 * 4 ^ l := by
      have h := congrArg (Polynomial.eval 4) hQ
      simp [eval_add, eval_mul, eval_sub, eval_pow, pow_succ] at h
      linarith only [h]
    have hRoot : IsRoot (8 * X ^ l - arcsinAntiderivQ l) 4 := by
      simp [IsRoot, eval_sub, eval_mul, eval_pow, h4]
    obtain ⟨V, hV⟩ := dvd_iff_isRoot.mpr hRoot
    let R : ℚ[X] := C (-1 / 2) * V
    -- Integrate the quotient coefficient by coefficient with zero constant term.
    let P : ℚ[X] := ∑ n ∈ R.support, monomial (n + 1) (R.coeff n / (n + 1))
    have hP : derivative P = R := by
      dsimp only [P]
      rw [derivative_sum]
      calc
        _ = ∑ n ∈ R.support, monomial n (R.coeff n) := by
          apply Finset.sum_congr rfl
          intro n _
          have hn : (n : ℚ) + 1 ≠ 0 := by positivity
          simp [div_mul_cancel₀ _ hn]
        _ = R := sum_monomial_eq R
    refine ⟨P, ?_, ?_⟩
    · simp [P, eval_finsetSum, eval_monomial, pow_succ]
    · rw [hP, hV]
      dsimp only [R]
      calc
        _ = C ((2 : ℚ) * (-1 / 2)) * (C 4 - X) * V := by
          simp only [map_mul, map_ofNat]
          ring
        _ = _ := by norm_num
  · intro P _ hP x hx hx4
    have hx' : 0 < 4 - x := sub_pos.mpr hx4
    let s := √x
    let t := √(4 - x)
    have hs₀ : s ≠ 0 := (Real.sqrt_pos.2 hx).ne'
    have ht₀ : t ≠ 0 := (Real.sqrt_pos.2 hx').ne'
    have hs₂ : s ^ 2 = x := Real.sq_sqrt hx.le
    have ht₂ : t ^ 2 = 4 - x := Real.sq_sqrt hx'.le
    have hs : HasDerivAt (fun y : ℝ => √y) (1 / (2 * s)) x := Real.hasDerivAt_sqrt hx.ne'
    have ht : HasDerivAt (fun y : ℝ => √(4 - y)) (-1 / (2 * t)) x := by
      refine ((Real.hasDerivAt_sqrt hx'.ne').comp x ((hasDerivAt_id x).const_sub 4)).congr_deriv ?_
      change 1 / (2 * t) * (-1) = -1 / (2 * t)
      ring
    have ha : HasDerivAt (fun y : ℝ => Real.arcsin (√y / 2)) (1 / (2 * s * t)) x := by
      have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg x
      have hs_lt : s < 2 := by nlinarith only [hs₂, hx4, hs_nonneg]
      have hrad : √(1 - (s / 2) ^ 2) = t / 2 := by
        rw [show 1 - (s / 2) ^ 2 = (4 - x) / 4 by nlinarith only [hs₂],
          Real.sqrt_div hx'.le]
        have htwo : √(4 : ℝ) = 2 := by
          convert Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num) using 1
          norm_num
        rw [htwo]
      refine ((Real.hasDerivAt_arcsin (x := s / 2) (by linarith) (by linarith)).comp x
        (hs.div_const 2)).congr_deriv ?_
      rw [hrad]
      field_simp
    have hratio : HasDerivAt (fun y : ℝ => √y / √(4 - y)) (2 / (s * t ^ 3)) x := by
      refine (hs.div ht ht₀).congr_deriv ?_
      change ((1 / (2 * s)) * t - s * (-1 / (2 * t))) / t ^ 2 = _
      field_simp
      nlinarith only [hs₂, ht₂]
    let a := Real.arcsin (s / 2)
    let c : ℝ := arcsinAntiderivC l
    let Q := arcsinAntiderivQ l
    let q := aeval x Q
    let q' := aeval x (derivative Q)
    let p' := aeval x (derivative P)
    -- The terms with and without arcsine cancel by equations (3) and (2), respectively.
    have hP_eval : 2 * t ^ 2 * p' = 8 * x ^ l - q := by
      simpa [ht₂, p', q, Q, map_ofNat] using congrArg (fun R : ℚ[X] => aeval x R) hP
    have hQ_eval : s ^ 2 * t ^ 2 * q' + 2 * q + c * t ^ 2 = 4 * x ^ l * s ^ 2 := by
      simpa [hs₂, ht₂, c, q, q', Q, pow_succ, mul_assoc, map_ofNat] using
        congrArg (fun R : ℚ[X] => aeval x R) hQ
    have hPlain : p' + q / (2 * t ^ 2) = 4 * x ^ l / t ^ 2 := by
      field_simp
      linear_combination hP_eval
    have hArc : c / (s * t) + 2 * q / (s * t ^ 3) + s / t * q' = 4 * x ^ l * s / t ^ 3 := by
      field_simp
      linear_combination hQ_eval
    have hF := ((P.hasDerivAt_aeval x).add ((ha.fun_pow 2).const_mul c)).add
      ((ha.mul hratio).mul (Q.hasDerivAt_aeval x))
    have hF' := hF.congr_deriv (g' := x ^ l * centralBinomReciprocalH x) (by
      change p' + c * (2 * a ^ 1 * (1 / (2 * s * t))) +
        ((1 / (2 * s * t) * (s / t) + a * (2 / (s * t ^ 3))) * q + a * (s / t) * q') = _
      calc
        _ = (p' + q / (2 * t ^ 2)) + a * (c / (s * t) + 2 * q / (s * t ^ 3) + s / t * q') := by
          field_simp
          ring
        _ = _ := by
          rw [hPlain, hArc, centralBinomReciprocalH]
          change 4 * x ^ l / t ^ 2 + a * (4 * x ^ l * s / t ^ 3) =
            x ^ l * (4 * s * a / ((4 - x) * t) + 4 / (4 - x))
          rw [← ht₂]
          ring)
    simp only [mul_div_assoc]
    exact hF'

end

end MetaMathlibExt
