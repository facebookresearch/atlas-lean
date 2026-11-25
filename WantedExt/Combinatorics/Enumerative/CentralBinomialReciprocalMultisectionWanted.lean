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
public import MathlibExt.Combinatorics.Enumerative.CentralBinomialReciprocalAntiderivative
public import MathlibExt.Combinatorics.Enumerative.CentralBinomialReciprocalLinearMultisection
public import MathlibExt.Combinatorics.Enumerative.CentralBinomialReciprocalMultisection

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

/-- **The closed form $H$ equals $1$ at $0$.** The function
$H(x) = \frac{4\sqrt{x}\,\arcsin(\sqrt{x}/2)}{(4 - x)\sqrt{4 - x}} + \frac{4}{4 - x}$ of a real
variable satisfies $H(0) = 1$.

Source: Rimer Zurita, *Elementary Functions Associated with Series Involving Reciprocals of
Central Binomial Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.6.8,
Section 2. -/
theorem centralBinomReciprocalH_zero : centralBinomReciprocalH 0 = 1 := by
  norm_num [centralBinomReciprocalH]

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
