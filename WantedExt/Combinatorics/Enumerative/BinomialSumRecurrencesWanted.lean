/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
public import MathlibExt.Combinatorics.Enumerative.BinomialSumRecurrences
public import MathlibExt.Combinatorics.Enumerative.CatalanTriangleStepFive

/-!
# Recurrences for step-`k` sums of binomial coefficients and Riordan arrays

Statements from Eduardo H. M. Brietzke, *Recurrence Relations for Sums of Binomial
Coefficients and Some Generalizations*, Journal of Integer Sequences 27 (2024),
Article 24.3.4. Corollary 3 is already proved as
`Polynomial.exists_polynomial_multiple_supported_on_multiples`
(`MathlibExt/Algebra/Polynomial/SupportedMultiple.lean`).
-/

namespace MetaMathlibExt

open Polynomial

@[expose] public section

/-- **Roots-of-unity products of integer polynomials.** Let $f \in \mathbb{Z}[x]$ have degree
$r$, let $k > 0$ be a natural number and let $\omega = e^{2\pi i/k}$. Then there are
$G, T \in \mathbb{Z}[x]$ such that $G(x) = f(\omega x) f(\omega^2 x) \cdots f(\omega^{k-1} x)$
as polynomials over $\mathbb{C}$, $T$ has degree $r$, and $f(x) G(x) = T(x^k)$.

Source: Eduardo H. M. Brietzke, *Recurrence Relations for Sums of Binomial Coefficients and
Some Generalizations*, Journal of Integer Sequences 27 (2024), Article 24.3.4, Proposition 2. -/
public theorem_wanted rootsOfUnity_product_mul_eq_comp_pow (f : ℤ[X]) (r k : ℕ) (hk : 0 < k)
    (hf : f.degree = r) :
    ∃ G T : ℤ[X],
      G.map (Int.castRingHom ℂ) =
        ∏ j ∈ Finset.Ico 1 k,
          (f.map (Int.castRingHom ℂ)).comp
            (C (Complex.exp (2 * Real.pi * Complex.I / k) ^ j) * X) ∧
      T.natDegree = r ∧ f * G = T.comp (X ^ k)

/-- **Window criterion for step sums of binomial coefficients.** Let $\alpha, k, \gamma, p, s$
be natural numbers with $\alpha > 1$, $k > 1$, $\gamma \ge 1$ and $p < k$, and let
$\delta_1, \delta_2, \ldots$ be integers. For $n \in \mathbb{N}$ let $c(n)$ be the sum of
$\binom{\alpha n}{m}$ over all $m$ with $0 \le m \le \alpha n$ and
$m \equiv \gamma n + p \pmod{k}$, that is, $c(n) = \sum_{j \in \mathbb{Z}}
\binom{\alpha n}{\gamma n + p + kj}$. If $c(n) = \sum_{i=1}^{s} \delta_i c(n - i)$ for all $n$
with $s \le n \le k^2 + s - 1$, then $c(n) = \sum_{i=1}^{s} \delta_i c(n - i)$ for all $n \ge s$.

The coefficients $\delta_i$ need only work for this one residue $p$; the source's hypothesis,
with one family $\delta_i$ for every $p$, is a special case.

Source: Eduardo H. M. Brietzke, *Recurrence Relations for Sums of Binomial Coefficients and
Some Generalizations*, Journal of Integer Sequences 27 (2024), Article 24.3.4, Proposition 8. -/
public theorem_wanted binomialStepSum_recurrence_of_window (α k γ p s : ℕ) (hα : 1 < α)
    (hk : 1 < k) (hγ : 1 ≤ γ) (hp : p < k) (δ : ℕ → ℤ) :
    let c : ℕ → ℤ := fun n =>
      ∑ m ∈ (Finset.range (α * n + 1)).filter (fun m => m % k = (γ * n + p) % k),
        ((α * n).choose m : ℤ)
    (∀ n, s ≤ n → n ≤ k ^ 2 + s - 1 → c n = ∑ i ∈ Finset.Icc 1 s, δ i * c (n - i)) →
      ∀ n, s ≤ n → c n = ∑ i ∈ Finset.Icc 1 s, δ i * c (n - i)

/-- **Window criterion for shifted step sums of binomial coefficients.** Let
$\alpha, \beta, k, \gamma, p, s$ be natural numbers with $\alpha > 1$, $k > 1$, $\gamma > 1$ and
$p < k$, and let $\delta_1, \delta_2, \ldots$ be integers. For $n \in \mathbb{N}$ let $c(n)$ be
the sum of $\binom{\alpha n + \beta}{m}$ over all $m$ with $0 \le m \le \alpha n + \beta$ and
$m \equiv \gamma n + p \pmod{k}$, that is,
$c(n) = \sum_{j \in \mathbb{Z}} \binom{\alpha n + \beta}{\gamma n + p + kj}$. If
$c(n) = \sum_{i=1}^{s} \delta_i c(n - i)$ for all $n$ with $s \le n \le k^2 + s - 1$, then
$c(n) = \sum_{i=1}^{s} \delta_i c(n - i)$ for all $n \ge s$.

The coefficients $\delta_i$ need only work for this one residue $p$; the source's hypothesis,
with one family $\delta_i$ for every $p$, is a special case.

Source: Eduardo H. M. Brietzke, *Recurrence Relations for Sums of Binomial Coefficients and
Some Generalizations*, Journal of Integer Sequences 27 (2024), Article 24.3.4, Theorem 9. -/
public theorem_wanted shiftedBinomialStepSum_recurrence_of_window (α β k γ p s : ℕ)
    (hα : 1 < α) (hk : 1 < k) (hγ : 1 < γ) (hp : p < k) (δ : ℕ → ℤ) :
    let c : ℕ → ℤ := fun n =>
      ∑ m ∈ (Finset.range (α * n + β + 1)).filter (fun m => m % k = (γ * n + p) % k),
        ((α * n + β).choose m : ℤ)
    (∀ n, s ≤ n → n ≤ k ^ 2 + s - 1 → c n = ∑ i ∈ Finset.Icc 1 s, δ i * c (n - i)) →
      ∀ n, s ≤ n → c n = ∑ i ∈ Finset.Icc 1 s, δ i * c (n - i)

end

end MetaMathlibExt
