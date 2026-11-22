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

/-- **Multisection formula for $\sum_k x^k / \binom{2mk}{mk}$.** Let $m \ge 1$ be a natural number
and $x$ a complex number with $|x| < 4^m$. Write $H(y) = \sum_{n \ge 0} y^n / \binom{2n}{n}$,
$w = e^{2\pi i/m}$, and let $x^{1/m}$ be the principal $m$-th root of $x$. Then
$$
\sum_{k \ge 0} \frac{x^k}{\binom{2mk}{mk}} = \frac{1}{m} \sum_{j=0}^{m-1} H(w^j x^{1/m}).
$$

Source: Rimer Zurita, *Elementary Functions Associated with Series Involving Reciprocals of
Central Binomial Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.6.8,
Theorem 7 (`jis-2024-24.6.8-thm-7`). -/
public theorem_wanted tsum_div_centralBinom_mul_eq_multisection {m : ℕ} (hm : 1 ≤ m) {x : ℂ}
    (hx : ‖x‖ < 4 ^ m) :
    ∑' k : ℕ, x ^ k / (Nat.centralBinom (m * k) : ℂ) =
      (1 / m : ℂ) * ∑ j ∈ Finset.range m,
        ∑' n : ℕ, (Complex.exp (2 * Real.pi * Complex.I / m) ^ j * x ^ ((1 : ℂ) / m)) ^ n /
          (Nat.centralBinom n : ℂ)

/-- **Multisection formula for $\sum_k x^k / (k \binom{2mk}{mk})$.** Let $m \ge 1$ be a natural
number and $x$ a complex number with $|x| < 4^m$. Write
$L(y) = \sum_{n \ge 1} y^n / (n \binom{2n}{n})$, $w = e^{2\pi i/m}$, and let $x^{1/m}$ be the
principal $m$-th root of $x$. Then
$$
\sum_{k \ge 1} \frac{x^k}{k \binom{2mk}{mk}} = \sum_{j=0}^{m-1} L(w^j x^{1/m}).
$$

Source: Rimer Zurita, *Elementary Functions Associated with Series Involving Reciprocals of
Central Binomial Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.6.8,
Theorem 8 (`jis-2024-24.6.8-thm-8`). -/
public theorem_wanted tsum_div_mul_centralBinom_mul_eq_multisection {m : ℕ} (hm : 1 ≤ m)
    {x : ℂ} (hx : ‖x‖ < 4 ^ m) :
    ∑' k : ℕ, x ^ (k + 1) / (((k + 1 : ℕ) : ℂ) * Nat.centralBinom (m * (k + 1))) =
      ∑ j ∈ Finset.range m,
        ∑' n : ℕ, (Complex.exp (2 * Real.pi * Complex.I / m) ^ j * x ^ ((1 : ℂ) / m)) ^ (n + 1) /
          (((n + 1 : ℕ) : ℂ) * Nat.centralBinom (n + 1))

/-- **Multisection formula for $\sum_k x^k / (k^2 \binom{2mk}{mk})$.** Let $m \ge 1$ be a natural
number and $x$ a complex number with $|x| < 4^m$. Write
$K(y) = \sum_{n \ge 1} y^n / (n^2 \binom{2n}{n})$, $w = e^{2\pi i/m}$, and let $x^{1/m}$ be the
principal $m$-th root of $x$. Then
$$
\sum_{k \ge 1} \frac{x^k}{k^2 \binom{2mk}{mk}} = m \sum_{j=0}^{m-1} K(w^j x^{1/m}).
$$

Source: Rimer Zurita, *Elementary Functions Associated with Series Involving Reciprocals of
Central Binomial Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.6.8,
Theorem 10 (`jis-2024-24.6.8-thm-10`). -/
public theorem_wanted tsum_div_sq_mul_centralBinom_mul_eq_multisection {m : ℕ} (hm : 1 ≤ m)
    {x : ℂ} (hx : ‖x‖ < 4 ^ m) :
    ∑' k : ℕ, x ^ (k + 1) / (((k + 1 : ℕ) : ℂ) ^ 2 * Nat.centralBinom (m * (k + 1))) =
      (m : ℂ) * ∑ j ∈ Finset.range m,
        ∑' n : ℕ, (Complex.exp (2 * Real.pi * Complex.I / m) ^ j * x ^ ((1 : ℂ) / m)) ^ (n + 1) /
          (((n + 1 : ℕ) : ℂ) ^ 2 * Nat.centralBinom (n + 1))

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

/-- **The closed form $H$ equals $1$ at $0$.** The function
$H(x) = \frac{4\sqrt{x}\,\arcsin(\sqrt{x}/2)}{(4 - x)\sqrt{4 - x}} + \frac{4}{4 - x}$ of a real
variable satisfies $H(0) = 1$.

Source: Rimer Zurita, *Elementary Functions Associated with Series Involving Reciprocals of
Central Binomial Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.6.8,
Section 2. -/
theorem centralBinomReciprocalH_zero : centralBinomReciprocalH 0 = 1 := by
  norm_num [centralBinomReciprocalH]

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

/-- **The first two arcsine antiderivative constants.** Zurita's constants satisfy $C_1 = -24$
and $C_2 = -120$, as in Table 1 of the paper.

Source: Rimer Zurita, *Elementary Functions Associated with Series Involving Reciprocals of
Central Binomial Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.6.8,
Definition 1 and Table 1. -/
theorem arcsinAntiderivC_one_two : arcsinAntiderivC 1 = -24 ∧ arcsinAntiderivC 2 = -120 := by
  constructor <;> norm_num [arcsinAntiderivC, arcsinAntiderivQCoeff, Finset.prod_Ico_succ_top]

/-- **Coefficients of Zurita's polynomial $S_l$.** For natural numbers $l$ and $k$, the rational
number $s_k$ (which depends on $l$) is $0$ when $k > l$, and when $k \le l$ it is
$s_k = \frac{8}{1 - 2l} \prod_{i=k}^{l-1} \frac{8(i + 1)}{2i - 1}$. Equivalently, $s_l = 8/(1 - 2l)$
and $s_k = \frac{8(k + 1)}{2k - 1} s_{k+1}$ for $0 \le k < l$.

Source: Rimer Zurita, *Elementary Functions Associated with Series Involving Reciprocals of
Central Binomial Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.6.8,
Definition 3. -/
def arcsinAntiderivSCoeff (l k : ℕ) : ℚ :=
  if l < k then 0
  else 8 / (1 - 2 * l) * ∏ i ∈ Finset.Ico k l, (8 * ((i : ℚ) + 1) / (2 * i - 1))

/-- **Leading coefficient of an S-polynomial.** For every natural number $l$, the coefficient
$s_l = s_{l,l}$ of $x^l$ in Zurita's polynomial $S_l$ equals $8/(1 - 2l)$.

Source: Rimer Zurita, *Elementary Functions Associated with Series Involving Reciprocals of
Central Binomial Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.6.8,
Definition 3. -/
theorem arcsinAntiderivSCoeff_self (l : ℕ) : arcsinAntiderivSCoeff l l = 8 / (1 - 2 * l) := by
  simp [arcsinAntiderivSCoeff]

/-- **Recursion for the coefficients of an S-polynomial.** Write $s_k = s_{l,k}$ for the
coefficient of $x^k$ in Zurita's polynomial $S_l$. For all natural numbers $k$ and $l$ with
$k < l$,
$$s_k = \frac{8(k + 1)}{2k - 1}\, s_{k+1}.$$

Source: Rimer Zurita, *Elementary Functions Associated with Series Involving Reciprocals of
Central Binomial Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.6.8,
Definition 3. -/
theorem arcsinAntiderivSCoeff_of_lt {l k : ℕ} (hkl : k < l) :
    arcsinAntiderivSCoeff l k =
      8 * ((k : ℚ) + 1) / (2 * k - 1) * arcsinAntiderivSCoeff l (k + 1) := by
  simp only [arcsinAntiderivSCoeff, show ¬ l < k by omega, show ¬ l < k + 1 by omega,
    ↓reduceIte, Finset.prod_eq_prod_Ico_succ_bot hkl]
  ring

/-- **Zurita's S-polynomials.** For a natural number $l$, $S_l$ is the polynomial with rational
coefficients $S_l(x) = \sum_{i=0}^{l} s_i x^i$, where $s_l = 8/(1 - 2l)$ and
$s_i = \frac{8(i + 1)}{2i - 1} s_{i+1}$ for $0 \le i < l$.

Source: Rimer Zurita, *Elementary Functions Associated with Series Involving Reciprocals of
Central Binomial Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.6.8,
Definition 3. -/
noncomputable def arcsinAntiderivS (l : ℕ) : ℚ[X] :=
  ∑ k ∈ Finset.range (l + 1), C (arcsinAntiderivSCoeff l k) * X ^ k

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
public theorem_wanted hasDerivAt_arcsinAntiderivP_pow_mul_centralBinomReciprocalH {l : ℕ}
    (hl : 1 ≤ l) :
    (∃ P : ℚ[X], P.eval 0 = 0 ∧
      2 * (C 4 - X) * derivative P = 8 * X ^ l - arcsinAntiderivQ l) ∧
    ∀ P : ℚ[X], P.eval 0 = 0 → 2 * (C 4 - X) * derivative P = 8 * X ^ l - arcsinAntiderivQ l →
      ∀ x : ℝ, 0 < x → x < 4 →
        HasDerivAt (fun y : ℝ => aeval y P + (arcsinAntiderivC l : ℝ) * Real.arcsin (√y / 2) ^ 2 +
            Real.arcsin (√y / 2) * √y / √(4 - y) * aeval y (arcsinAntiderivQ l))
          (x ^ l * centralBinomReciprocalH x) x

/-- **Antiderivative of $x^{l - 1/2} H(x)$.** Let $l \ge 0$, let $S_l$ be Zurita's polynomial, and
let $H$ be the closed form of the reciprocal central binomial series. Then there is a polynomial
$T$ with rational coefficients such that $(4 - x)(2x T'(x) + T(x)) = 8x^l - S_l(x)$ as
polynomials. Moreover, for every such $T$ and every real number $x$ with $0 < x < 4$, the real
function
$$
G(y) = T(y)\sqrt{y} + \frac{\arcsin(\sqrt{y}/2)}{\sqrt{4 - y}}\, S_l(y)
$$
has derivative $\frac{x^l}{\sqrt{x}} H(x)$ at $x$.

Such a $T$ is unique: it is the paper's polynomial $T_{l-1}$ (Definition 4, with $T_{-1} = 0$).

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
