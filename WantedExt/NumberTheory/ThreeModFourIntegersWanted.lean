/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# Integers whose prime factors are all `≡ 3 (mod 4)`

Statements from Gareth A. Jones and Alexander K. Zvonkin, *A Number-Theoretic Problem
Concerning Pseudo-Real Riemann Surfaces*, INTEGERS 25 (2025), Article A75
(arXiv:2401.00270).

`g(x)` counts the `n ≤ x` all of whose prime factors are `≡ -1 (mod 4)` (including
`n = 1`). The constant `C = C(4, 1)` of Languasco and Zaccagnini is defined in the paper
by `∏_{q ≤ x, q ≡ 1 (4)} (1 - 1/q) = C / (ln x)^{1/2} + O((ln x)^{-3/2})`; it enters
here as the limit of `(ln x)^{1/2} ∏_{q ≤ x, q ≡ 1 (4)} (1 - 1/q)`.
-/

namespace MetaMathlibExt

@[expose] public section

open Filter Asymptotics

/-- **Raikov's Tauberian theorem.** Let $a_1, a_2, \ldots$ be nonnegative real numbers whose
Dirichlet series $F(s) = \sum_{n \ge 1} a_n n^{-s}$ converges absolutely for $\mathrm{Re}\, s > 1$,
and let $\alpha < 1$ be real. Suppose that $H$ is a function holomorphic on an open set containing
the half-plane $\mathrm{Re}\, s \ge 1$ and nonzero on that half-plane, and that
$F(s) = H(s) / (s - 1)^{1 - \alpha}$ for $\mathrm{Re}\, s > 1$, with the principal branch of the
power. Then
$$\sum_{n=1}^{x} a_n \sim \frac{H(1)}{\Gamma(1 - \alpha)} \cdot \frac{x}{(\ln x)^\alpha}$$
as the natural number $x$ tends to infinity.

The paper allows any real $\alpha$; for $\alpha = 1$ the statement fails: $a_1 = 1$, $a_n = 0$
otherwise and $H = 1$ give $F = 1 = H / (s - 1)^0$, but $\Gamma$ has a pole at $0$ and
$\sum_{n \le x} a_n = 1$. The analytic continuation of $F$ across $\mathrm{Re}\, s = 1$,
$s \neq 1$, assumed in the paper, follows from the representation through $H$.

Source: Jones and Zvonkin, *A Number-Theoretic Problem Concerning Pseudo-Real Riemann
Surfaces*, INTEGERS 25 (2025), Article A75, Theorem 1 (`integers-2025-A75-thm-1`). -/
public theorem_wanted isEquivalent_sum_of_LSeries_eq_div_cpow {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    {α : ℝ} (hα : α < 1)
    (hconv : ∀ s : ℂ, 1 < s.re → LSeriesSummable (fun n => (a n : ℂ)) s)
    {H : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hUre : {s : ℂ | 1 ≤ s.re} ⊆ U)
    (hH : DifferentiableOn ℂ H U) (hH0 : ∀ s : ℂ, 1 ≤ s.re → H s ≠ 0)
    (hF : ∀ s : ℂ, 1 < s.re →
      LSeries (fun n => (a n : ℂ)) s = H s / (s - 1) ^ ((1 - α : ℝ) : ℂ)) :
    IsEquivalent atTop (fun x : ℕ => ∑ n ∈ Finset.Icc 1 x, (a n : ℂ))
      (fun x : ℕ => H 1 / Complex.Gamma (1 - α) * x / (Real.log x ^ α : ℝ))

/-- **Counting integers whose prime factors are all $\equiv 3 \pmod 4$.** Let $C$ be a real
number such that $\sqrt{\ln x} \prod_{q \le x} (1 - 1/q) \to C$ as the natural number $x$ tends
to infinity, where $q$ runs over the primes with $q \equiv 1 \pmod 4$. Let $g(x)$ be the number
of integers $n$ with $1 \le n \le x$ all of whose prime factors are $\equiv 3 \pmod 4$ (so
$n = 1$ is counted). Then
$$g(x) \sim \sqrt{e^\gamma / \pi} \cdot \frac{C}{2} \cdot \frac{x}{\sqrt{\ln x}}$$
as the natural number $x$ tends to infinity, where $\gamma$ is the Euler–Mascheroni constant.

In the source $C = C(4, 1)$ is the constant of Languasco and Zaccagnini; for $C = 1.29230\ldots$
the constant in front of $x / \sqrt{\ln x}$ is $0.48651\ldots$.

Source: Jones and Zvonkin, *A Number-Theoretic Problem Concerning Pseudo-Real Riemann
Surfaces*, INTEGERS 25 (2025), Article A75, Theorem 2 (`integers-2025-A75-thm-2`). -/
public theorem_wanted isEquivalent_card_primeFactors_three_mod_four {C : ℝ}
    (hC : Tendsto (fun x : ℕ => √(Real.log x) *
      ∏ q ∈ (Finset.range (x + 1)).filter (fun q => q.Prime ∧ q % 4 = 1), (1 - 1 / (q : ℝ)))
      atTop (nhds C)) :
    IsEquivalent atTop
      (fun x : ℕ => (((Finset.Icc 1 x).filter fun n => ∀ q ∈ n.primeFactors, q % 4 = 3).card : ℝ))
      (fun x : ℕ => √(Real.exp Real.eulerMascheroniConstant / Real.pi) * C / 2 * x /
        √(Real.log x))

end

end MetaMathlibExt
