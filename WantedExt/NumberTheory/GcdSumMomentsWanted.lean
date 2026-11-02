/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Zeta
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import MathlibExt.NumberTheory.ArithmeticFunction.GcdSumTotient

/-!
# Moments of the mean gcd-sum function

Statements from M. S. Datt, Ekta Soni, and A. Sankaranarayanan, *On the Asymptotic Formula for
the Gcd-Sum Function*, INTEGERS 26 (2026), Article A70: asymptotic formulas for
`∑_{n ≤ x} A(n)^k`, where `A(n) = P(n)/n` and `P(n) = ∑_{j=1}^n gcd(j, n)` is Pillai's gcd-sum
function, the structure of the Dirichlet series `F_k(s) = ∑ A(n)^k n^{-s}`, and the quoted
moment and pointwise bounds for `ζ` the proofs use. Lemmas 1, 4 and 6 of the paper are stated in
`WantedExt/NumberTheory/ZetaSubconvexityBoundsWanted.lean`.

The paper's main term `M_k(x)` is the residue of `F_k(s) x^s / s` at the pole of order `2^k`
at `s = 1`, so it has the form `x P(log x)` for a real polynomial `P`; the asymptotic theorems
below assert the existence of such a `P`. Since every stated error term is `o(x)`, the
polynomial is unique, so the existential form loses nothing.
-/

namespace MetaMathlibExt

@[expose] public section

open Complex Filter Asymptotics Polynomial

/-- **The mean gcd-sum function.** For a natural number $n$, let $P(n) = \sum_{j=1}^{n} \gcd(j, n)$
be Pillai's gcd-sum function. The mean gcd-sum function is the real-valued function given by
$A(n) = P(n)/n$ for $n \ge 1$ and $A(0) = 0$.

Source: M. S. Datt, Ekta Soni, and A. Sankaranarayanan, *On the Asymptotic Formula for the
Gcd-Sum Function*, INTEGERS 26 (2026), Article A70, Section 1 (definition of `A(n)`). -/
noncomputable def gcdSumMean (n : ℕ) : ℝ :=
  (∑ j ∈ Finset.Icc 1 n, (Nat.gcd j n : ℝ)) / n

/-- **The mean gcd-sum function at $1$.** The mean gcd-sum function $A$ satisfies $A(1) = 1$.

Source: M. S. Datt, Ekta Soni, and A. Sankaranarayanan, *On the Asymptotic Formula for the
Gcd-Sum Function*, INTEGERS 26 (2026), Article A70, Section 1 (definition of `A(n)`). -/
theorem gcdSumMean_one : gcdSumMean 1 = 1 := by
  simp [gcdSumMean]

/-- **The mean gcd-sum function at $2$.** The mean gcd-sum function $A$ satisfies $A(2) = 3/2$,
since $A(2) = P(2)/2$, where $P(n) = \sum_{j=1}^{n} \gcd(j, n)$ is Pillai's gcd-sum function
and $P(2) = \gcd(1, 2) + \gcd(2, 2) = 3$.

Source: M. S. Datt, Ekta Soni, and A. Sankaranarayanan, *On the Asymptotic Formula for the
Gcd-Sum Function*, INTEGERS 26 (2026), Article A70, Section 1 (definition of `A(n)`). -/
theorem gcdSumMean_two : gcdSumMean 2 = 3 / 2 := by
  rw [gcdSumMean, show Finset.Icc 1 2 = {1, 2} by decide]
  norm_num

/-- **Divisor-sum formula for the mean gcd-sum function.** For every natural number $n \ge 1$,
the mean gcd-sum function $A$ satisfies $A(n) = \sum_{d \mid n} \varphi(d)/d$, where $\varphi$ is
Euler's totient function and the sum runs over the positive divisors $d$ of $n$.

Source: M. S. Datt, Ekta Soni, and A. Sankaranarayanan, *On the Asymptotic Formula for the
Gcd-Sum Function*, INTEGERS 26 (2026), Article A70, Section 1 (Pillai's identity). -/
theorem gcdSumMean_eq_sum_totient_div {n : ℕ} (hn : 0 < n) :
    gcdSumMean n = ∑ d ∈ n.divisors, (Nat.totient d : ℝ) / d := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (gcd_sum_eq_totient_sum n hn)
  push_cast at h
  rw [gcdSumMean, h]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

/-- **Asymptotic formula for the second moment of the mean gcd-sum function.** For $n \ge 1$ let
$A(n) = \frac{1}{n} \sum_{j=1}^{n} \gcd(j, n)$ be the mean gcd-sum function. There are a real
polynomial $P$ and a real constant $C$ such that, as $x \to \infty$,

$$\sum_{1 \le n \le x} A(n)^2 = x P(\log x) +
O\left(x^{1/2} \exp\left(C (\log \log x)^2\right)\right).$$

Source: M. S. Datt, Ekta Soni, and A. Sankaranarayanan, *On the Asymptotic Formula for the
Gcd-Sum Function*, INTEGERS 26 (2026), Article A70, Theorem 1 (`integers-2026-A70-thm-1`). -/
public theorem_wanted sum_gcdSumMean_sq_asymptotic :
    ∃ (P : ℝ[X]) (C : ℝ),
      (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, gcdSumMean n ^ 2 - x * P.eval (Real.log x))
        =O[atTop] fun x => x ^ (1 / 2 : ℝ) * Real.exp (C * Real.log (Real.log x) ^ 2)

/-- **Asymptotic formula for the third moment of the mean gcd-sum function.** For $n \ge 1$ let
$A(n) = \frac{1}{n} \sum_{j=1}^{n} \gcd(j, n)$ be the mean gcd-sum function. There are a real
polynomial $P$ and a real constant $C$ such that, as $x \to \infty$,

$$\sum_{1 \le n \le x} A(n)^3 = x P(\log x) +
O\left(x^{5/8} \exp\left(C (\log \log x)^2\right)\right).$$

Source: M. S. Datt, Ekta Soni, and A. Sankaranarayanan, *On the Asymptotic Formula for the
Gcd-Sum Function*, INTEGERS 26 (2026), Article A70, Theorem 2 (`integers-2026-A70-thm-2`). -/
public theorem_wanted sum_gcdSumMean_cube_asymptotic :
    ∃ (P : ℝ[X]) (C : ℝ),
      (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, gcdSumMean n ^ 3 - x * P.eval (Real.log x))
        =O[atTop] fun x => x ^ (5 / 8 : ℝ) * Real.exp (C * Real.log (Real.log x) ^ 2)

/-- **Asymptotic formula for the fourth moment of the mean gcd-sum function.** For $n \ge 1$ let
$A(n) = \frac{1}{n} \sum_{j=1}^{n} \gcd(j, n)$ be the mean gcd-sum function. There is a real
polynomial $P$ such that for every $\varepsilon > 0$, as $x \to \infty$,

$$\sum_{1 \le n \le x} A(n)^4 = x P(\log x) + O_\varepsilon\left(x^{157/199 + \varepsilon}\right).$$

Source: M. S. Datt, Ekta Soni, and A. Sankaranarayanan, *On the Asymptotic Formula for the
Gcd-Sum Function*, INTEGERS 26 (2026), Article A70, Theorem 3 (`integers-2026-A70-thm-3`). -/
public theorem_wanted sum_gcdSumMean_pow_four_asymptotic :
    ∃ P : ℝ[X], ∀ ε : ℝ, 0 < ε →
      (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, gcdSumMean n ^ 4 - x * P.eval (Real.log x))
        =O[atTop] fun x => x ^ (157 / 199 + ε)

/-- **Asymptotic formula for the higher moments of the mean gcd-sum function.** For $n \ge 1$ let
$A(n) = \frac{1}{n} \sum_{j=1}^{n} \gcd(j, n)$ be the mean gcd-sum function, and let $k \ge 5$ be
an integer. There is a real polynomial $P$ such that for every $\varepsilon > 0$, as
$x \to \infty$,

$$\sum_{1 \le n \le x} A(n)^k = x P(\log x) +
O_{k,\varepsilon}\left(x^{1 + 2\varepsilon - 42/(13 \cdot 2^k - 9)}\right).$$

Source: M. S. Datt, Ekta Soni, and A. Sankaranarayanan, *On the Asymptotic Formula for the
Gcd-Sum Function*, INTEGERS 26 (2026), Article A70, Theorem 4 (`integers-2026-A70-thm-4`). -/
public theorem_wanted sum_gcdSumMean_pow_asymptotic (k : ℕ) (hk : 5 ≤ k) :
    ∃ P : ℝ[X], ∀ ε : ℝ, 0 < ε →
      (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, gcdSumMean n ^ k - x * P.eval (Real.log x))
        =O[atTop] fun x => x ^ (1 + 2 * ε - 42 / (13 * 2 ^ k - 9))

/-- **Factorization of the Dirichlet series of powers of the mean gcd-sum function.** Let $k$ be a
natural number and let $A$ be the mean gcd-sum function. There are functions
$g, h \colon \mathbb{N} \to \mathbb{C}$ such that the Dirichlet series
$G_k(s) = \sum_{n \ge 1} g(n) n^{-s}$ converges absolutely for every complex $s$ with
$\operatorname{Re} s > 1/2$, the Dirichlet series $\tilde G_{k,2}(s) = \sum_{n \ge 1} h(n) n^{-s}$
converges absolutely for every complex $s$ with $\operatorname{Re} s > 1/3$, and for every complex
$s$ with $\operatorname{Re} s > 1$,
$$\sum_{n \ge 1} A(n)^k n^{-s} = \zeta(s)^{2^k} G_k(s)$$
and
$$G_k(s) \, \zeta(2s)^{4^k - 3^k - \binom{2^k}{2}} = \tilde G_{k,2}(s).$$

The exponent $4^k - 3^k - \binom{2^k}{2}$ is a nonnegative integer, since
$3^k + \binom{2^k}{2} \le 4^k$. The paper also gives an explicit Euler product for
$\tilde G_{k,2}$, which is not stated here.

Source: M. S. Datt, Ekta Soni, and A. Sankaranarayanan, *On the Asymptotic Formula for the
Gcd-Sum Function*, INTEGERS 26 (2026), Article A70, Lemma 8 (`integers-2026-A70-lem-8`). -/
public theorem_wanted LSeries_gcdSumMean_pow_eq_riemannZeta_pow_mul (k : ℕ) :
    ∃ g h : ℕ → ℂ, (∀ s : ℂ, 1 / 2 < s.re → LSeriesSummable g s) ∧
      (∀ s : ℂ, 1 / 3 < s.re → LSeriesSummable h s) ∧
      ∀ s : ℂ, 1 < s.re →
        LSeries (fun n => ((gcdSumMean n ^ k : ℝ) : ℂ)) s = riemannZeta s ^ (2 ^ k) * LSeries g s ∧
        LSeries g s * riemannZeta (2 * s) ^ (4 ^ k - 3 ^ k - (2 ^ k).choose 2) = LSeries h s

/-- **An alternating binomial sum vanishes.** Let $k$ and $m$ be natural numbers with $k \ge 2$
and $m \ge 2^k - 1$. Then, computed in the integers,
$$\sum_{r=0}^{\min(2^k,\, m+1)} (-1)^r \binom{2^k}{r} (m + 1 - r)^k = 0.$$
Since $m + 1 \ge 2^k$, the upper limit of the sum is $2^k$.

This sum is the exponent $\ell_m$ of the paper: the coefficient of $p^{-ms}$ in
$(1 - p^{-s})^{2^k} \sum_{a \ge 0} (a + 1)^k p^{-as}$, which is why it stops at $r = m + 1$. The
paper prints the sum up to $r = 2^k$ for every $m$; that sum vanishes for every $m$, being a
$2^k$-th difference of a polynomial of degree $k$, which contradicts the paper's own
$\ell_2 = 3^k - 4^k + \binom{2^k}{2}$: for $k = m = 2$ the truncated sum is $-1$. So with the
truncation the hypothesis $m \ge 2^k - 1$ is needed. The paper's hypothesis $k \ge 2$ is kept: for
$k = 0$ the term $r = m + 1$ contributes $0^0 = 1$ rather than the coefficient of a negative
index, so the truncated sum is no longer the coefficient read off from the paper's Euler product.

Source: M. S. Datt, Ekta Soni, and A. Sankaranarayanan, *On the Asymptotic Formula for the
Gcd-Sum Function*, INTEGERS 26 (2026), Article A70, Theorem 5 (`integers-2026-A70-thm-5`). -/
public theorem_wanted alternating_choose_two_pow_mul_pow_eq_zero (k m : ℕ) (hk : 2 ≤ k)
    (hm : 2 ^ k - 1 ≤ m) :
    ∑ r ∈ Finset.range (min (2 ^ k) (m + 1) + 1),
      (-1 : ℤ) ^ r * ((2 ^ k).choose r : ℤ) * ((m : ℤ) + 1 - r) ^ k = 0

/-- **Dirichlet series of the square of the mean gcd-sum function.** Let $A$ be the mean gcd-sum
function. There is a function $h \colon \mathbb{N} \to \mathbb{C}$ such that the Dirichlet series
$\tilde G_{2,2}(s) = \sum_{n \ge 1} h(n) n^{-s}$ converges absolutely for every complex $s$ with
$\operatorname{Re} s > 0$, and for every complex $s$ with $\operatorname{Re} s > 1$,
$$\sum_{n \ge 1} A(n)^2 n^{-s} = \frac{\zeta(s)^4}{\zeta(2s)} \, \tilde G_{2,2}(s).$$

This is the case $k = 2$ of the paper's Theorem 5, which gives the absolute convergence of
$\tilde G_{2,2}(s)$ in every half-plane $\operatorname{Re} s > 1/N$ with $N \ge 1$, that is, for
$\operatorname{Re} s > 0$.

Source: M. S. Datt, Ekta Soni, and A. Sankaranarayanan, *On the Asymptotic Formula for the
Gcd-Sum Function*, INTEGERS 26 (2026), Article A70, Theorem 5 (`integers-2026-A70-thm-5`). -/
public theorem_wanted LSeries_gcdSumMean_sq_eq_riemannZeta_pow_four_div :
    ∃ h : ℕ → ℂ, (∀ s : ℂ, 0 < s.re → LSeriesSummable h s) ∧
      ∀ s : ℂ, 1 < s.re →
        LSeries (fun n => ((gcdSumMean n ^ 2 : ℝ) : ℂ)) s =
          riemannZeta s ^ 4 / riemannZeta (2 * s) * LSeries h s

/-- **Ivić's eighth-moment bound on the line $\operatorname{Re} s = 5/8$.** There are real
constants $C$ and $T_0$ such that for every real $T \ge T_0$,
$$\int_{T/2}^{T} |\zeta(5/8 + it)|^8 \, dt \le C T (\log T)^{38}.$$

Source: M. S. Datt, Ekta Soni, and A. Sankaranarayanan, *On the Asymptotic Formula for the
Gcd-Sum Function*, INTEGERS 26 (2026), Article A70, Lemma 2 (`integers-2026-A70-lem-2`). -/
public theorem_wanted riemannZeta_eighth_moment_five_eighths_le :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ∫ t in T / 2..T, ‖riemannZeta (5 / 8 + t * I)‖ ^ 8 ≤ C * T * Real.log T ^ 38

/-- **Lemma 3** (quoted twelfth-moment asymptotic). For fixed `5/7 < σ < 1` and every `ε > 0`,
`∫_1^T |ζ(σ + i t)|^{12} dt = T ∑_{n ≥ 1} d_6(n)^2 n^{-2σ} + O(T^{(9 - 7σ)/4 + ε})`, where
`d_6 = ζ^{*6}` is the six-fold divisor function. The printed side condition `|t| ≥ 1` is implied
by the integration range and omitted.

Source: M. S. Datt, Ekta Soni, and A. Sankaranarayanan, *On the Asymptotic Formula for the
Gcd-Sum Function*, INTEGERS 26 (2026), Article A70, Lemma 3 (`integers-2026-A70-lem-3`). -/
public theorem_wanted riemannZeta_twelfth_moment_asymptotic {σ : ℝ} (hσ₁ : 5 / 7 < σ)
    (hσ₂ : σ < 1) {ε : ℝ} (hε : 0 < ε) :
    (fun T : ℝ => ∫ t in (1 : ℝ)..T, ‖riemannZeta (σ + t * I)‖ ^ 12 -
        T * ∑' n : ℕ,
          ((ArithmeticFunction.zeta ^ 6 : ArithmeticFunction ℕ) n : ℝ) ^ 2 / (n : ℝ) ^ (2 * σ))
      =O[atTop] fun T => T ^ ((9 - 7 * σ) / 4 + ε)

/-- **A weighted fourth-moment bound for $\zeta$ on the critical line.** There are real constants
$C$ and $T_0$ such that for every real $T \ge T_0$,
$$\int_{10}^{T} \frac{|\zeta(1/2 + it)|^4}{|\zeta(1 + 2it)|} \, dt \le C T (\log T)^5.$$

Source: M. S. Datt, Ekta Soni, and A. Sankaranarayanan, *On the Asymptotic Formula for the
Gcd-Sum Function*, INTEGERS 26 (2026), Article A70, Lemma 5 (`integers-2026-A70-lem-5`). -/
public theorem_wanted riemannZeta_fourth_moment_div_le :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ∫ t in (10 : ℝ)..T, ‖riemannZeta (1 / 2 + t * I)‖ ^ 4 / ‖riemannZeta (1 + 2 * t * I)‖ ≤
        C * T * Real.log T ^ 5

/-- **Ramachandra–Sankaranarayanan bound for $\zeta$ at a well-chosen height.** Let $\zeta$ be the
Riemann zeta function. There are real constants $C$ and $U_0$ such that for every real
$U \ge U_0$ there is a real number $T$ with $U < T < 2U$ such that for every real $\sigma \ge 1/2$,
$$
|\zeta(\sigma + iT)| \le \exp\bigl(C (\log \log U)^2\bigr) \quad \text{and} \quad
|\zeta(\sigma - iT)| \le \exp\bigl(C (\log \log U)^2\bigr).
$$

The source adds that this bound is $\ll U^{\varepsilon}$ for every $\varepsilon > 0$; that
consequence is not part of this statement.

Source: M. S. Datt, Ekta Soni, and A. Sankaranarayanan, *On the Asymptotic Formula for the
Gcd-Sum Function*, INTEGERS 26 (2026), Article A70, Lemma 7 (`integers-2026-A70-lem-7`). -/
public theorem_wanted exists_riemannZeta_norm_le_exp_loglog_sq :
    ∃ C U₀ : ℝ, ∀ U : ℝ, U₀ ≤ U → ∃ T ∈ Set.Ioo U (2 * U), ∀ σ : ℝ, 1 / 2 ≤ σ →
      ‖riemannZeta (σ + T * I)‖ ≤ Real.exp (C * Real.log (Real.log U) ^ 2) ∧
        ‖riemannZeta (σ - T * I)‖ ≤ Real.exp (C * Real.log (Real.log U) ^ 2)

end

end MetaMathlibExt
