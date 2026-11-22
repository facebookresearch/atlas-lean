/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import MathlibExt.Analysis.SpecialFunctions.DickmanDeBruijn
public import MathlibExt.NumberTheory.ArithmeticFunction.CompletelyMultiplicative
public import WantedExt.NumberTheory.PrimeCounting.DusartMertensReciprocalSumWanted

/-!
# Explicit prime-sum and mean-value estimates from Bordignon--Francis

Statement-only targets from Matteo Bordignon and Forrest J. Francis, *Explicit Improvements to
the Burgess Bound via Pólya--Vinogradov*, INTEGERS 24 (2024), Article A66. The statement texts
were checked against the preprint arXiv:2007.08119v1, whose numbering is shifted (Lemma 2.1,
Lemma 3.1, Propositions 4.4 and 4.5, Lemmas 4.7, 4.9 and 4.10).
-/

open Real

namespace MetaMathlibExt

@[expose] public section

/-- **Explicit lower bound for the Dickman function.** Let $\rho$ be a Dickman–de Bruijn
function. Then $\rho(x) \ge x^{-1.42 x}$ for every real $x \ge 1$.

Source: Matteo Bordignon and Forrest J. Francis, *Explicit Improvements to the Burgess Bound via
Pólya--Vinogradov*, INTEGERS 24 (2024), Article A66, Lemma 2 (`integers-2024-A66-lem-2`). -/
public theorem_wanted dickman_ge_rpow_neg_mul {ρ : ℝ → ℝ} (hρ : Real.IsDickmanDeBruijn ρ)
    {x : ℝ} (hx : 1 ≤ x) :
    x ^ (-(1.42 : ℝ) * x) ≤ ρ x

/-- **Logarithmic derivative of the zeta function near its pole.** Let $\zeta$ be the Riemann zeta
function. There are real numbers $C$ and $\alpha_0 > 0$ such that for all real $\alpha$ and $\tau$
with $0 < \alpha < \alpha_0$ and $|\tau| \le 1/2$, the point $s = 1 + \alpha + i\tau$ satisfies
$|\zeta'(s)/\zeta(s)| \le 1/|s - 1| + C$.

This is the estimate $|\zeta'(s)/\zeta(s)| \le 1/|s - 1| + O(1)$ as $\alpha \to 0^+$, uniformly
in $|\tau| \le 1/2$.

Source: Matteo Bordignon and Forrest J. Francis, *Explicit Improvements to the Burgess Bound via
Pólya--Vinogradov*, INTEGERS 24 (2024), Article A66, Lemma 3 (`integers-2024-A66-lem-3`). -/
public theorem_wanted exists_norm_logDeriv_riemannZeta_le_inv_norm_add :
    ∃ C α₀ : ℝ, 0 < α₀ ∧ ∀ α τ : ℝ, 0 < α → α < α₀ → |τ| ≤ 1 / 2 →
      ‖deriv riemannZeta (1 + α + τ * Complex.I) / riemannZeta (1 + α + τ * Complex.I)‖ ≤
        1 / ‖(α : ℂ) + τ * Complex.I‖ + C

/-- **Mertens' second theorem with the Rosser–Schoenfeld error term.** Let $M$ be the
Meissel–Mertens constant. Then $0.2614 \le M < 0.2615$, and for every real $x > 1$,
$\left|\sum_{p \le x} 1/p - \log \log x - M\right| \le 1/(\log x)^2$, where the sum runs over the
primes $p \le x$.

Source: Matteo Bordignon and Forrest J. Francis, *Explicit Improvements to the Burgess Bound via
Pólya--Vinogradov*, INTEGERS 24 (2024), Article A66, Proposition 1
(`integers-2024-A66-prop-1`). -/
public theorem_wanted abs_sum_inv_primes_sub_meisselMertensConstant_le :
    0.2614 ≤ meisselMertensConstant ∧ meisselMertensConstant < 0.2615 ∧ ∀ x : ℝ, 1 < x →
      |(∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / p) - log (log x) -
          meisselMertensConstant| ≤ 1 / log x ^ 2

/-- **Two-sided explicit Mertens bound.** For every real $x \ge 2$,
$\log \log x + 0.2614 \le \sum_{p \le x} 1/p \le \log \log x + 0.8666$, where the sum runs over
the primes $p \le x$.

Source: Matteo Bordignon and Forrest J. Francis, *Explicit Improvements to the Burgess Bound via
Pólya--Vinogradov*, INTEGERS 24 (2024), Article A66, Proposition 2
(`integers-2024-A66-prop-2`). -/
public theorem_wanted log_log_add_le_sum_inv_primes_le {x : ℝ} (hx : 2 ≤ x) :
    log (log x) + 0.2614 ≤ ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / p ∧
      ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / p ≤ log (log x) + 0.8666

/-- **Explicit bound for a cosine-weighted sum over primes.** Let $K$ be a real number with
$\frac{1}{2\pi} \int_0^{2\pi} |\cos t - K| \, dt = 1 - K$ (this equation has exactly one real
solution, $K \approx 0.3286$). Then for every real $\alpha$ with $0 < \alpha \le 1$ and every real
$\tau$, $\sum_{p \le e^{1/\alpha}} |\cos(\tau \log p) - K|/p \le (1 - K) \log(1/\alpha) +
(2 + 2K) \log \log(|\tau| + 3) + 7.28$, where the sum runs over the primes $p \le e^{1/\alpha}$.

Source: Matteo Bordignon and Forrest J. Francis, *Explicit Improvements to the Burgess Bound via
Pólya--Vinogradov*, INTEGERS 24 (2024), Article A66, Lemma 7 (`integers-2024-A66-lem-7`). -/
public theorem_wanted sum_abs_cos_sub_div_primes_le {K : ℝ}
    (hK : (2 * π)⁻¹ * ∫ t in (0 : ℝ)..(2 * π), |cos t - K| = 1 - K)
    {α : ℝ} (hα₀ : 0 < α) (hα₁ : α ≤ 1) (τ : ℝ) :
    ∑ p ∈ (Finset.Iic ⌊exp (1 / α)⌋₊).filter Nat.Prime, |cos (τ * log p) - K| / p ≤
      (1 - K) * log (1 / α) + (2 + 2 * K) * log (log (|τ| + 3)) + 7.28

/-- **Upper bound for twisted prime sums with real coefficients.** Throughout, sums over $p$ run
over primes. Let $K$ be a real number with
$\frac{1}{2\pi} \int_0^{2\pi} |\cos t - K| \, dt = 1 - K$. Let $g$ be a real-valued function on
the natural numbers with $|g(p)| \le 1$ for every prime $p$, let $\alpha$ be a real number with
$0 < \alpha \le 1$, put $x = e^{1/\alpha}$, and let $\lambda$ be a real number with
$\sum_{p \le x} (1 - g(p))/p = \lambda \sum_{p \le x} 1/p$. Let $M$ be the Meissel–Mertens
constant and $M'(x) = \sum_{p \le x} 1/p - \log \log x - M$. Then for every real $\tau$,
$\operatorname{Re} \sum_{p \le x} g(p)/p^{1 + i\tau}$ is at most
$(1 - K\lambda) \log(1/\alpha) + (2 + 2K) \log \log(|\tau| + 3) + 7.28 +
(K - K\lambda)(M + M'(x))$.

The paper prints $(2 + 2K)(\log \log |\tau| + 3)$; its proof applies Lemma 7, which has
$\log \log(|\tau| + 3)$, and the printed form fails at $\alpha = 1$, $g \equiv 1$,
$\tau = 1.0001$. The paper allows $\alpha \in [0, 1]$; here $\alpha > 0$, where $e^{1/\alpha}$
is defined.

Source: Matteo Bordignon and Forrest J. Francis, *Explicit Improvements to the Burgess Bound via
Pólya--Vinogradov*, INTEGERS 24 (2024), Article A66, Lemma 8 (`integers-2024-A66-lem-8`). -/
public theorem_wanted re_sum_div_primes_cpow_le {K : ℝ}
    (hK : (2 * π)⁻¹ * ∫ t in (0 : ℝ)..(2 * π), |cos t - K| = 1 - K)
    {g : ℕ → ℝ} (hg : ∀ p, p.Prime → |g p| ≤ 1) {α : ℝ} (hα₀ : 0 < α) (hα₁ : α ≤ 1) {lam : ℝ}
    (hlam : ∑ p ∈ (Finset.Iic ⌊exp (1 / α)⌋₊).filter Nat.Prime, (1 - g p) / p =
      lam * ∑ p ∈ (Finset.Iic ⌊exp (1 / α)⌋₊).filter Nat.Prime, (1 : ℝ) / p) (τ : ℝ) :
    (∑ p ∈ (Finset.Iic ⌊exp (1 / α)⌋₊).filter Nat.Prime,
        (g p : ℂ) / (p : ℂ) ^ (1 + τ * Complex.I)).re ≤
      (1 - K * lam) * log (1 / α) + (2 + 2 * K) * log (log (|τ| + 3)) + 7.28 +
        (K - K * lam) * (meisselMertensConstant +
          ((∑ p ∈ (Finset.Iic ⌊exp (1 / α)⌋₊).filter Nat.Prime, (1 : ℝ) / p) -
            log (log (exp (1 / α))) - meisselMertensConstant))

/-- **Bound for a Dirichlet series by its prime sum.** Let $g$ be a complex-valued completely
multiplicative arithmetic function with $g(1) = 1$ and $|g(n)| \le 1$ for every $n$, and let
$F(s) = \sum_{n \ge 1} g(n) n^{-s}$ be its Dirichlet series. Let
$\nu_2 = \sum_p (-\log(1 - 1/p) - 1/p)$, summed over all primes $p$. Then $\nu_2 \le 0.316$, and
for every complex $s$ with $\operatorname{Re} s > 1$,
$|F(s)| \le e^{\nu_2} \exp(\operatorname{Re} \sum_p g(p) p^{-s})$, where $p$ runs over the primes.

In the paper $\nu_2 = \gamma - M$, with $\gamma$ the Euler–Mascheroni constant and $M$ the
Meissel–Mertens constant; the prime series above is the form of $\nu_2$ used in its proof.

Source: Matteo Bordignon and Forrest J. Francis, *Explicit Improvements to the Burgess Bound via
Pólya--Vinogradov*, INTEGERS 24 (2024), Article A66, Lemma 9 (`integers-2024-A66-lem-9`). -/
public theorem_wanted norm_LSeries_le_exp_nu₂_mul_exp_re_sum_primes
    {g : ArithmeticFunction ℂ} (hg₁ : g 1 = 1) (hmul : g.IsCompletelyMultiplicative)
    (hg : ∀ n, ‖g n‖ ≤ 1) :
    (∑' p : Nat.Primes, (-log (1 - 1 / (p : ℝ)) - 1 / (p : ℝ))) ≤ 0.316 ∧
      ∀ s : ℂ, 1 < s.re →
        ‖LSeries (⇑g) s‖ ≤ exp (∑' p : Nat.Primes, (-log (1 - 1 / (p : ℝ)) - 1 / (p : ℝ))) *
          exp (∑' p : Nat.Primes, g p / (p : ℂ) ^ s).re

/-- **Uniform tail bound for the prime zeta series.** For every real $\alpha$ with
$0 < \alpha \le 1$, $\sum_{p > e^{1/\alpha}} p^{-(1 + \alpha)} \le 0.9235$, where the sum runs
over the primes $p > e^{1/\alpha}$.

Source: Matteo Bordignon and Forrest J. Francis, *Explicit Improvements to the Burgess Bound via
Pólya--Vinogradov*, INTEGERS 24 (2024), Article A66, Lemma 10 (`integers-2024-A66-lem-10`). -/
public theorem_wanted tsum_rpow_neg_primes_gt_exp_inv_le {α : ℝ} (hα₀ : 0 < α) (hα₁ : α ≤ 1) :
    ∑' p : {p : ℕ // p.Prime ∧ exp (1 / α) < p}, ((p : ℕ) : ℝ) ^ (-(1 + α)) ≤ 0.9235

end

end MetaMathlibExt
