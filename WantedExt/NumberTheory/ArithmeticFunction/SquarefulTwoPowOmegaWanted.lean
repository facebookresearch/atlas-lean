/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import MathlibExt.NumberTheory.KFull

/-!
# Venkatasubbareddy–Sankaranarayanan, `2^{ω(n)}` on squareful integers — wishlist

Statement-only records for the lemmas of Venkatasubbareddy and
Sankaranarayanan, INTEGERS 24 (2024), Article A110, that are stated over
explicit objects: the factorizations of `F(s) = ∑_{n squareful} 2^{ω(n)} n^{-s}`
(squareful is `Nat.IsKFull 2`)
through zeta products (Lemmas 1 and 2) and the classical zeta estimates the
paper quotes (Lemmas 4, 5, 6 and 8). A positive integer `n` is squareful when
`p ∣ n` implies `p^2 ∣ n` for every prime `p`; `n = 1` is squareful. The
paper's Lemma 7 (`N(T) ≪ T log T`) is implied by
`MetaMathlibExt.bellotti_wong_zero_count_bound`.
-/

open Complex

namespace MetaMathlibExt

@[expose] public section

open Classical in
/-- **Fine zeta factorization of the squareful $2^{\omega(n)}$ Dirichlet series.** Let
$\omega(n)$ be the number of distinct prime factors of $n$, call $n$ squareful when $n \ne 0$ and
$p^2 \mid n$ for every prime $p \mid n$ (that is, $n$ is $2$-full), and let
$F(s) = \sum_{n \text{ squareful}} 2^{\omega(n)} n^{-s}$. There is a sequence
$h : \mathbb{N} \to \mathbb{C}$ whose Dirichlet series $H(s) = \sum_{n \ge 1} h(n) n^{-s}$
converges absolutely for $\operatorname{Re} s > 1/15$, such that for every complex $s$ with
$\operatorname{Re} s > 1/2$,
$$F(s) = \frac{\zeta(2s)^2 \zeta(3s)^2 \zeta(7s)^2 \zeta(8s)^4 \zeta(12s)^5 \zeta(13s)^{14}
\zeta(14s)^5}{\zeta(4s) \zeta(5s)^2 \zeta(6s)^3 \zeta(10s)^5 \zeta(11s)^6} H(s).$$

Source: Kampamolla Venkatasubbareddy and Ayyadurai Sankaranarayanan, *On the
Distribution of the Restricted Sequence of Integers 2^{ω(n)}*, INTEGERS 24
(2024), Article A110, Lemma 1 (`integers-2024-A110-lem-1`). -/
public theorem_wanted squareful_two_pow_omega_LSeries_eq_zeta_quotient_fifteen :
    ∃ h : ℕ → ℂ, (∀ s : ℂ, 1 / 15 < s.re → LSeriesSummable h s) ∧
      ∀ s : ℂ, 1 / 2 < s.re →
        LSeries (fun n => if Nat.IsKFull 2 n then
            (2 : ℂ) ^ ArithmeticFunction.cardDistinctFactors n else 0) s =
          riemannZeta (2 * s) ^ 2 * riemannZeta (3 * s) ^ 2 * riemannZeta (7 * s) ^ 2 *
              riemannZeta (8 * s) ^ 4 * riemannZeta (12 * s) ^ 5 *
              riemannZeta (13 * s) ^ 14 * riemannZeta (14 * s) ^ 5 /
            (riemannZeta (4 * s) * riemannZeta (5 * s) ^ 2 * riemannZeta (6 * s) ^ 3 *
              riemannZeta (10 * s) ^ 5 * riemannZeta (11 * s) ^ 6) * LSeries h s

open Classical in
/-- **Coarse zeta factorization of the squareful $2^{\omega(n)}$ Dirichlet series.** Let
$\omega(n)$ be the number of distinct prime factors of $n$, call $n$ squareful when $n \ne 0$ and
$p^2 \mid n$ for every prime $p \mid n$ (that is, $n$ is $2$-full), and let
$F(s) = \sum_{n \text{ squareful}} 2^{\omega(n)} n^{-s}$. There is a sequence
$h : \mathbb{N} \to \mathbb{C}$ whose Dirichlet series $H(s) = \sum_{n \ge 1} h(n) n^{-s}$
converges absolutely for $\operatorname{Re} s > 1/5$, such that for every complex $s$ with
$\operatorname{Re} s > 1/2$,
$$F(s) = \frac{\zeta(2s)^2 \zeta(3s)^2}{\zeta(4s)} H(s).$$

Source: Kampamolla Venkatasubbareddy and Ayyadurai Sankaranarayanan, *On the
Distribution of the Restricted Sequence of Integers 2^{ω(n)}*, INTEGERS 24
(2024), Article A110, Lemma 2 (`integers-2024-A110-lem-2`). -/
public theorem_wanted squareful_two_pow_omega_LSeries_eq_zeta_quotient_five :
    ∃ h : ℕ → ℂ, (∀ s : ℂ, 1 / 5 < s.re → LSeriesSummable h s) ∧
      ∀ s : ℂ, 1 / 2 < s.re →
        LSeries (fun n => if Nat.IsKFull 2 n then
            (2 : ℂ) ^ ArithmeticFunction.cardDistinctFactors n else 0) s =
          riemannZeta (2 * s) ^ 2 * riemannZeta (3 * s) ^ 2 / riemannZeta (4 * s) * LSeries h s

/-- **Uniform fourth-moment bound for the Riemann zeta function.** There are real constants $C$
and $T_0$ such that for every real $\sigma$ with $1/2 \le \sigma \le 1$ and every real
$T \ge T_0$,
$$\int_1^T |\zeta(\sigma + it)|^4 \, dt \le C T (\log T)^4.$$

Source: Kampamolla Venkatasubbareddy and Ayyadurai Sankaranarayanan, *On the
Distribution of the Restricted Sequence of Integers 2^{ω(n)}*, INTEGERS 24
(2024), Article A110, Lemma 4 (`integers-2024-A110-lem-4`). -/
public theorem_wanted zeta_fourth_moment_le_uniform :
    ∃ C T₀ : ℝ, ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → ∀ T : ℝ, T₀ ≤ T →
      ∫ t in (1 : ℝ)..T, ‖riemannZeta (σ + t * I)‖ ^ 4 ≤ C * T * Real.log T ^ 4

/-- **Vinogradov–Korobov bound for $1/\zeta$.** Write $s = \sigma + it$ and
$g(T) = (\log T)^{2/3} (\log \log T)^{1/3}$. There are real constants $C > 0$, $K$ and
$T_0 \ge 3$ such that for every real $T$ and every complex $s$ with $T_0 < t \le T$ and
$\sigma \ge 1 - C / g(T)$, we have $\zeta(s) \ne 0$ and $|1/\zeta(s)| \le K g(T)$.

Source: Kampamolla Venkatasubbareddy and Ayyadurai Sankaranarayanan, *On the
Distribution of the Restricted Sequence of Integers 2^{ω(n)}*, INTEGERS 24
(2024), Article A110, Lemma 5 (`integers-2024-A110-lem-5`). -/
public theorem_wanted inv_zeta_le_vinogradov_korobov :
    ∃ C K T₀ : ℝ, 0 < C ∧ 3 ≤ T₀ ∧ ∀ T : ℝ, ∀ s : ℂ, T₀ < s.im → s.im ≤ T →
      1 - C / (Real.log T ^ ((2 : ℝ) / 3) * Real.log (Real.log T) ^ ((1 : ℝ) / 3)) ≤ s.re →
        riemannZeta s ≠ 0 ∧ ‖(riemannZeta s)⁻¹‖ ≤
          K * Real.log T ^ ((2 : ℝ) / 3) * Real.log (Real.log T) ^ ((1 : ℝ) / 3)

/-- **Vinogradov–Korobov zero-free region.** There are real constants $C > 0$ and $t_0 \ge 3$
such that $\zeta(\sigma + it) \ne 0$ for all real $\sigma$ and $t$ with $|t| \ge t_0$ and
$\sigma \ge 1 - C / \bigl((\log |t|)^{2/3} (\log \log |t|)^{1/3}\bigr)$.

Source: Kampamolla Venkatasubbareddy and Ayyadurai Sankaranarayanan, *On the
Distribution of the Restricted Sequence of Integers 2^{ω(n)}*, INTEGERS 24
(2024), Article A110, Lemma 6 (`integers-2024-A110-lem-6`). -/
public theorem_wanted zeta_ne_zero_vinogradov_korobov :
    ∃ C t₀ : ℝ, 0 < C ∧ 3 ≤ t₀ ∧ ∀ s : ℂ, t₀ ≤ |s.im| →
      1 - C / (Real.log |s.im| ^ ((2 : ℝ) / 3) *
          Real.log (Real.log |s.im|) ^ ((1 : ℝ) / 3)) ≤ s.re →
        riemannZeta s ≠ 0

/-- **Lindelöf bound from the Riemann hypothesis.** Assume the Riemann hypothesis, and let
$\varepsilon > 0$ be real. Then there are real constants $C$ and $t_0$ such that
$|\zeta(\sigma + it)| \le C |t|^{\varepsilon}$ for all real $\sigma$ and $t$ with
$1/2 \le \sigma \le 1$ and $|t| \ge t_0$.

Source: Kampamolla Venkatasubbareddy and Ayyadurai Sankaranarayanan, *On the
Distribution of the Restricted Sequence of Integers 2^{ω(n)}*, INTEGERS 24
(2024), Article A110, Lemma 8 (`integers-2024-A110-lem-8`). -/
public theorem_wanted zeta_le_rpow_of_riemannHypothesis (hRH : RiemannHypothesis)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C t₀ : ℝ, ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → t₀ ≤ |t| →
      ‖riemannZeta (σ + t * I)‖ ≤ C * |t| ^ ε

/-- **Bound for $1/\zeta$ from the Riemann hypothesis.** Assume the Riemann hypothesis, and let
$1/2 < \sigma \le 1$ and $\varepsilon > 0$ be real. Then there are real constants $C$ and $t_0$,
depending on $\sigma$ and $\varepsilon$, such that $|1/\zeta(\sigma + it)| \le C |t|^{\varepsilon}$
for every real $t$ with $|t| \ge t_0$.

Source: Kampamolla Venkatasubbareddy and Ayyadurai Sankaranarayanan, *On the
Distribution of the Restricted Sequence of Integers 2^{ω(n)}*, INTEGERS 24
(2024), Article A110, Lemma 8 (`integers-2024-A110-lem-8`). -/
public theorem_wanted inv_zeta_le_rpow_of_riemannHypothesis (hRH : RiemannHypothesis)
    (σ : ℝ) (hσ : 1 / 2 < σ) (hσ1 : σ ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ C t₀ : ℝ, ∀ t : ℝ, t₀ ≤ |t| → ‖(riemannZeta (σ + t * I))⁻¹‖ ≤ C * |t| ^ ε

open Classical in
/-- **Asymptotic for the sum of $2^{\omega(n)}$ over squareful $n$.** Let $\omega(n)$ be the
number of distinct prime factors of $n$, and let $f(n) = 2^{\omega(n)}$ if $n$ is squareful
($n \ne 0$ and $p^2 \mid n$ for every prime $p \mid n$; so $f(1) = 1$) and $f(n) = 0$ otherwise.
There are real constants $C_1$, $C_2$, $C_3$, $C_4$, $c > 0$, $K$ and $x_0$ such that for every
real $x \ge x_0$,
$$\Bigl|\sum_{1 \le n \le x} f(n) - \bigl(C_1 x^{1/2} \log x + C_2 x^{1/2} +
C_3 x^{1/3} \log x + C_4 x^{1/3}\bigr)\Bigr| \le
K x^{1/4} \exp\Bigl(c \Bigl(\frac{\log x}{\log \log x}\Bigr)^{1/3}\Bigr).$$

The paper writes the coefficient as $c_\varepsilon$, "for some $c > 0$", after "let
$\varepsilon > 0$": a constant chosen after $\varepsilon$, not a product with an arbitrarily small
factor. Its proof (equations (28)–(30)) produces, with $T$ the height parameter of its contour,
the exponent $(4 + \varepsilon) c (\log T / \log \log T)^{1/3}$ with $\varepsilon$ small and
$c > 0$ the fixed constant of its contour shift to $\operatorname{Re} s = 1/4 - c/g(T)$, where
$g(T) = (\log T)^{2/3} (\log \log T)^{1/3}$, chosen in terms of the Vinogradov–Korobov
zero-free region and the bound for $1/\zeta$ there (its Lemmas 5 and 6), so the coefficient
stays bounded away from $0$ and the statement is one existential $c > 0$.

Source: Kampamolla Venkatasubbareddy and Ayyadurai Sankaranarayanan, *On the
Distribution of the Restricted Sequence of Integers 2^{ω(n)}*, INTEGERS 24
(2024), Article A110, Theorem 1 (`integers-2024-A110-thm-1`). -/
public theorem_wanted squareful_two_pow_omega_sum_asymptotic :
    ∃ C₁ C₂ C₃ C₄ c K x₀ : ℝ, 0 < c ∧ ∀ x : ℝ, x₀ ≤ x →
      |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (if Nat.IsKFull 2 n then
            (2 : ℝ) ^ ArithmeticFunction.cardDistinctFactors n else 0) -
          (C₁ * x ^ ((1 : ℝ) / 2) * Real.log x + C₂ * x ^ ((1 : ℝ) / 2) +
            C₃ * x ^ ((1 : ℝ) / 3) * Real.log x + C₄ * x ^ ((1 : ℝ) / 3))| ≤
        K * x ^ ((1 : ℝ) / 4) *
          Real.exp (c * (Real.log x / Real.log (Real.log x)) ^ ((1 : ℝ) / 3))

end

end MetaMathlibExt
