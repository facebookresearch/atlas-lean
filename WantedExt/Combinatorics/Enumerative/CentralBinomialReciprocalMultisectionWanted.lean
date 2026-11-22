/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Data.Nat.Choose.Central

/-!
# Multisections of reciprocal central binomial series

Statements from Rimer Zurita, *Elementary Functions Associated with Series Involving Reciprocals
of Central Binomial Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.6.8.

For `m ≥ 1` and `|x| < 4^m` the series `H_m(x) = ∑_{k ≥ 0} x^k / binom(2mk, mk)`,
`L_m(x) = ∑_{k ≥ 1} x^k / (k binom(2mk, mk))` and `K_m(x) = ∑_{k ≥ 1} x^k / (k² binom(2mk, mk))`
are expressed through `H = H_1`, `L = L_1`, `K = K_1` at the points `w^j x^{1/m}`, where
`w = e^{2πi/m}` and `x^{1/m}` is the principal complex root (any `m`-th root gives the same sum).

Lemmas 5 and 6 are antiderivative formulas for `x^l H(x)` and `x^{l-1/2} H(x)`, stated on the real
interval `0 < x < 4` with the paper's polynomials `Q_l`, `S_l` and constants `C_l` (Definitions 1
and 3, by their coefficient recursions); `P_l` and `T_{l-1}` are pinned by their defining
integrals as the polynomial solutions of `2(4 - x) P_l' = 8x^l - Q_l`, `P_l(0) = 0` and
`(4 - x)(2x T_{l-1}' + T_{l-1}) = 8x^l - S_l` (both unique).
-/

namespace MetaMathlibExt

@[expose] public section

open Polynomial

/-- For `m ≥ 1` and `|x| < 4^m`,
`H_m(x) = ∑_{k ≥ 0} x^k / binom(2mk, mk) = (1/m) ∑_{j=0}^{m-1} H(w^j x^{1/m})` with
`H(y) = ∑_{n ≥ 0} y^n / binom(2n, n)` and `w = e^{2πi/m}`.

Source: Rimer Zurita, *Elementary Functions Associated with Series Involving Reciprocals of
Central Binomial Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.6.8,
Theorem 7 (`jis-2024-24.6.8-thm-7`). -/
public theorem_wanted tsum_div_centralBinom_mul_eq_multisection {m : ℕ} (hm : 1 ≤ m) {x : ℂ}
    (hx : ‖x‖ < 4 ^ m) :
    ∑' k : ℕ, x ^ k / (Nat.centralBinom (m * k) : ℂ) =
      (1 / m : ℂ) * ∑ j ∈ Finset.range m,
        ∑' n : ℕ, (Complex.exp (2 * Real.pi * Complex.I / m) ^ j * x ^ ((1 : ℂ) / m)) ^ n /
          (Nat.centralBinom n : ℂ)

/-- For `m ≥ 1` and `|x| < 4^m`,
`L_m(x) = ∑_{k ≥ 1} x^k / (k binom(2mk, mk)) = ∑_{j=0}^{m-1} L(w^j x^{1/m})` with
`L(y) = ∑_{n ≥ 1} y^n / (n binom(2n, n))` and `w = e^{2πi/m}`.

Source: Rimer Zurita, *Elementary Functions Associated with Series Involving Reciprocals of
Central Binomial Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.6.8,
Theorem 8 (`jis-2024-24.6.8-thm-8`). -/
public theorem_wanted tsum_div_mul_centralBinom_mul_eq_multisection {m : ℕ} (hm : 1 ≤ m)
    {x : ℂ} (hx : ‖x‖ < 4 ^ m) :
    ∑' k : ℕ, x ^ (k + 1) / (((k + 1 : ℕ) : ℂ) * Nat.centralBinom (m * (k + 1))) =
      ∑ j ∈ Finset.range m,
        ∑' n : ℕ, (Complex.exp (2 * Real.pi * Complex.I / m) ^ j * x ^ ((1 : ℂ) / m)) ^ (n + 1) /
          (((n + 1 : ℕ) : ℂ) * Nat.centralBinom (n + 1))

/-- For `m ≥ 1` and `|x| < 4^m`,
`K_m(x) = ∑_{k ≥ 1} x^k / (k² binom(2mk, mk)) = m ∑_{j=0}^{m-1} K(w^j x^{1/m})` with
`K(y) = ∑_{n ≥ 1} y^n / (n² binom(2n, n))` and `w = e^{2πi/m}`.

Source: Rimer Zurita, *Elementary Functions Associated with Series Involving Reciprocals of
Central Binomial Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.6.8,
Theorem 10 (`jis-2024-24.6.8-thm-10`). -/
public theorem_wanted tsum_div_sq_mul_centralBinom_mul_eq_multisection {m : ℕ} (hm : 1 ≤ m)
    {x : ℂ} (hx : ‖x‖ < 4 ^ m) :
    ∑' k : ℕ, x ^ (k + 1) / (((k + 1 : ℕ) : ℂ) ^ 2 * Nat.centralBinom (m * (k + 1))) =
      (m : ℂ) * ∑ j ∈ Finset.range m,
        ∑' n : ℕ, (Complex.exp (2 * Real.pi * Complex.I / m) ^ j * x ^ ((1 : ℂ) / m)) ^ (n + 1) /
          (((n + 1 : ℕ) : ℂ) ^ 2 * Nat.centralBinom (n + 1))

/-- The closed form `H(x) = 4√x arcsin(√x/2) / (4 - x)^{3/2} + 4/(4 - x)` of
`∑_{n ≥ 0} x^n / binom(2n, n)`, on the real interval `0 ≤ x < 4`.

Source: Rimer Zurita, *Elementary Functions Associated with Series Involving Reciprocals of
Central Binomial Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.6.8,
Section 2. -/
noncomputable def centralBinomReciprocalH (x : ℝ) : ℝ :=
  4 * √x * Real.arcsin (√x / 2) / ((4 - x) * √(4 - x)) + 4 / (4 - x)

/-- `H(0) = 1`.

Source: Rimer Zurita, *Elementary Functions Associated with Series Involving Reciprocals of
Central Binomial Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.6.8,
Section 2. -/
theorem centralBinomReciprocalH_zero : centralBinomReciprocalH 0 = 1 := by
  norm_num [centralBinomReciprocalH]

/-- Coefficient `q_k` of the paper's polynomial `Q_l` (`l ≥ 1`): `q_l = -4/l`,
`q_k = ((4k + 6)/k) q_{k+1}` for `1 ≤ k < l`, `q_0 = -12 q_1`, and `q_k = 0` for `k > l`.

Source: Rimer Zurita, *Elementary Functions Associated with Series Involving Reciprocals of
Central Binomial Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.6.8,
Definition 1. -/
def arcsinAntiderivQCoeff (l k : ℕ) : ℚ :=
  if l < k then 0
  else if k = 0 then -12 * ((-4 / l) * ∏ i ∈ Finset.Ico 1 l, ((4 * i + 6 : ℚ) / i))
  else (-4 / l) * ∏ i ∈ Finset.Ico k l, ((4 * i + 6 : ℚ) / i)

/-- `q_l = -4/l` for `l ≥ 1`.

Source: Rimer Zurita, *Elementary Functions Associated with Series Involving Reciprocals of
Central Binomial Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.6.8,
Definition 1. -/
theorem arcsinAntiderivQCoeff_self {l : ℕ} (hl : 1 ≤ l) : arcsinAntiderivQCoeff l l = -4 / l := by
  simp [arcsinAntiderivQCoeff, show l ≠ 0 by omega]

/-- `q_k = ((4k + 6)/k) q_{k+1}` for `1 ≤ k < l`.

Source: Rimer Zurita, *Elementary Functions Associated with Series Involving Reciprocals of
Central Binomial Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.6.8,
Definition 1. -/
theorem arcsinAntiderivQCoeff_of_lt {l k : ℕ} (hk : 1 ≤ k) (hkl : k < l) :
    arcsinAntiderivQCoeff l k = (4 * k + 6) / k * arcsinAntiderivQCoeff l (k + 1) := by
  simp only [arcsinAntiderivQCoeff, show ¬ l < k by omega, show ¬ l < k + 1 by omega,
    show k ≠ 0 by omega, show k + 1 ≠ 0 by omega, ↓reduceIte,
    Finset.prod_eq_prod_Ico_succ_bot hkl]
  ring

/-- `q_0 = -12 q_1` for `l ≥ 1`.

Source: Rimer Zurita, *Elementary Functions Associated with Series Involving Reciprocals of
Central Binomial Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.6.8,
Definition 1. -/
theorem arcsinAntiderivQCoeff_zero {l : ℕ} (hl : 1 ≤ l) :
    arcsinAntiderivQCoeff l 0 = -12 * arcsinAntiderivQCoeff l 1 := by
  simp [arcsinAntiderivQCoeff, show ¬ l < 1 by omega]

/-- The paper's polynomial `Q_l(x) = ∑_{i=0}^l q_i x^i` for `l ≥ 1`, and `Q_0 = 8`.

Source: Rimer Zurita, *Elementary Functions Associated with Series Involving Reciprocals of
Central Binomial Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.6.8,
Definition 1. -/
noncomputable def arcsinAntiderivQ (l : ℕ) : ℚ[X] :=
  if l = 0 then C 8 else ∑ k ∈ Finset.range (l + 1), C (arcsinAntiderivQCoeff l k) * X ^ k

/-- The paper's constant `C_l = -q_0/2` for `l ≥ 1`, and `C_0 = -4`.

Source: Rimer Zurita, *Elementary Functions Associated with Series Involving Reciprocals of
Central Binomial Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.6.8,
Definition 1. -/
def arcsinAntiderivC (l : ℕ) : ℚ :=
  if l = 0 then -4 else -arcsinAntiderivQCoeff l 0 / 2

/-- `C_1 = -24` and `C_2 = -120`, as in the paper's Table 1.

Source: Rimer Zurita, *Elementary Functions Associated with Series Involving Reciprocals of
Central Binomial Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.6.8,
Definition 1 and Table 1. -/
theorem arcsinAntiderivC_one_two : arcsinAntiderivC 1 = -24 ∧ arcsinAntiderivC 2 = -120 := by
  constructor <;> norm_num [arcsinAntiderivC, arcsinAntiderivQCoeff, Finset.prod_Ico_succ_top]

/-- Coefficient `s_k` of the paper's polynomial `S_l`: `s_l = 8/(1 - 2l)`,
`s_k = (8(k + 1)/(2k - 1)) s_{k+1}` for `0 ≤ k < l`, and `s_k = 0` for `k > l`.

Source: Rimer Zurita, *Elementary Functions Associated with Series Involving Reciprocals of
Central Binomial Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.6.8,
Definition 3. -/
def arcsinAntiderivSCoeff (l k : ℕ) : ℚ :=
  if l < k then 0
  else 8 / (1 - 2 * l) * ∏ i ∈ Finset.Ico k l, (8 * ((i : ℚ) + 1) / (2 * i - 1))

/-- `s_l = 8/(1 - 2l)`.

Source: Rimer Zurita, *Elementary Functions Associated with Series Involving Reciprocals of
Central Binomial Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.6.8,
Definition 3. -/
theorem arcsinAntiderivSCoeff_self (l : ℕ) : arcsinAntiderivSCoeff l l = 8 / (1 - 2 * l) := by
  simp [arcsinAntiderivSCoeff]

/-- `s_k = (8(k + 1)/(2k - 1)) s_{k+1}` for `k < l`.

Source: Rimer Zurita, *Elementary Functions Associated with Series Involving Reciprocals of
Central Binomial Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.6.8,
Definition 3. -/
theorem arcsinAntiderivSCoeff_of_lt {l k : ℕ} (hkl : k < l) :
    arcsinAntiderivSCoeff l k =
      8 * ((k : ℚ) + 1) / (2 * k - 1) * arcsinAntiderivSCoeff l (k + 1) := by
  simp only [arcsinAntiderivSCoeff, show ¬ l < k by omega, show ¬ l < k + 1 by omega,
    ↓reduceIte, Finset.prod_eq_prod_Ico_succ_bot hkl]
  ring

/-- The paper's polynomial `S_l(x) = ∑_{i=0}^l s_i x^i`.

Source: Rimer Zurita, *Elementary Functions Associated with Series Involving Reciprocals of
Central Binomial Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.6.8,
Definition 3. -/
noncomputable def arcsinAntiderivS (l : ℕ) : ℚ[X] :=
  ∑ k ∈ Finset.range (l + 1), C (arcsinAntiderivSCoeff l k) * X ^ k

/-- Lemma 5: for `l ≥ 1`, the paper's `P_l` (the polynomial with `P_l(0) = 0` and
`P_l' = (8x^l - Q_l(x)) / (2(4 - x))`, Definition 2) exists, and on `0 < x < 4`
`d/dx [P_l(x) + C_l arcsin(√x/2)^2 + arcsin(√x/2) √x Q_l(x) / √(4 - x)] = x^l H(x)`, i.e.
`∫ x^l H(x) dx = P_l(x) + C_l arcsin(√x/2)^2 + arcsin(√x/2) √x Q_l(x) / √(4 - x)`.

Source: Rimer Zurita, *Elementary Functions Associated with Series Involving Reciprocals of
Central Binomial Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.6.8,
Lemma 5 (`jis-2024-24.6.8-lem-5`). -/
public theorem_wanted hasDerivAt_arcsinAntiderivP_pow_mul_centralBinomReciprocalH {l : ℕ}
    (hl : 1 ≤ l) :
    (∃ P : ℚ[X], P.eval 0 = 0 ∧
      2 * (C 4 - X) * derivative P = 8 * X ^ l - arcsinAntiderivQ l) ∧
    ∀ P : ℚ[X], P.eval 0 = 0 → 2 * (C 4 - X) * derivative P = 8 * X ^ l - arcsinAntiderivQ l →
      ∀ x : ℝ, 0 < x → x < 4 →
        HasDerivAt (fun y : ℝ => aeval y P + (arcsinAntiderivC l : ℝ) * Real.arcsin (√y / 2) ^ 2 +
            Real.arcsin (√y / 2) * √y / √(4 - y) * aeval y (arcsinAntiderivQ l))
          (x ^ l * centralBinomReciprocalH x) x

/-- Lemma 6: for `l ≥ 0`, the paper's `T_{l-1}` (Definition 4: the polynomial with
`T_{l-1}(x) = (x^{-1/2}/2) ∫ (8x^l - S_l(x)) / (√x (4 - x)) dx`, equivalently
`(4 - x)(2x T_{l-1}' + T_{l-1}) = 8x^l - S_l`; `T_{-1} = 0`) exists, and on `0 < x < 4`
`d/dx [T_{l-1}(x) √x + arcsin(√x/2) S_l(x) / √(4 - x)] = x^{l-1/2} H(x)`.

Source: Rimer Zurita, *Elementary Functions Associated with Series Involving Reciprocals of
Central Binomial Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.6.8,
Lemma 6 (`jis-2024-24.6.8-lem-6`). -/
public theorem_wanted hasDerivAt_arcsinAntiderivT_pow_mul_centralBinomReciprocalH (l : ℕ) :
    (∃ T : ℚ[X], (C 4 - X) * (2 * X * derivative T + T) = 8 * X ^ l - arcsinAntiderivS l) ∧
    ∀ T : ℚ[X], (C 4 - X) * (2 * X * derivative T + T) = 8 * X ^ l - arcsinAntiderivS l →
      ∀ x : ℝ, 0 < x → x < 4 →
        HasDerivAt (fun y : ℝ => aeval y T * √y +
            Real.arcsin (√y / 2) / √(4 - y) * aeval y (arcsinAntiderivS l))
          (x ^ l / √x * centralBinomReciprocalH x) x

end

end MetaMathlibExt
