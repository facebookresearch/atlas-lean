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
public import Mathlib.Data.Nat.Fib.Basic

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

/-- A finite window suffices to transfer a recurrence: if `x` satisfies an order-`r` linear
recurrence `x_n = ∑_{i=1}^r A_i x_{n-i}` for all `n ≥ r`, and an order-`s` recurrence
`x_n = ∑_{i=1}^s a_i x_{n-i}` holds for `s ≤ n ≤ N` with `N ≥ r + s - 1`, then the order-`s`
recurrence holds for all `n ≥ s`. Stated over an arbitrary commutative ring.

Source: Eduardo H. M. Brietzke, *Recurrence Relations for Sums of Binomial Coefficients and
Some Generalizations*, Journal of Integer Sequences 27 (2024), Article 24.3.4, Proposition 1. -/
public theorem_wanted linearRecurrence_of_finite_window {R : Type*} [CommRing R]
    (x A a : ℕ → R) (r s N : ℕ)
    (hA : ∀ n, r ≤ n → x n = ∑ i ∈ Finset.Icc 1 r, A i * x (n - i))
    (hN : r + s - 1 ≤ N)
    (ha : ∀ n, s ≤ n → n ≤ N → x n = ∑ i ∈ Finset.Icc 1 s, a i * x (n - i)) :
    ∀ n, s ≤ n → x n = ∑ i ∈ Finset.Icc 1 s, a i * x (n - i)

/-- Roots-of-unity product: for `f ∈ ℤ[x]` of degree `r`, `k > 0` and `ω = exp(2πi/k)`, the
product `F(x) = f(ωx) f(ω²x) ⋯ f(ω^{k-1}x)` has integer coefficients and
`f(x) F(x) = T(x^k)` for some `T ∈ ℤ[x]` of degree `r`.

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

/-- Step-`k` sums of a Riordan array. For a Riordan array `d(n, m) = [x^n] g(x) h(x)^m`
(`h(0) = 0`) over a field, `k > 1` and `p < k`,
`∑_{j ≥ 0} d(n, kj + p) = [x^n] g(x) h(x)^p / (1 - h(x)^k)`. The sum is over `j ≤ n`, since
`d(n, m) = 0` for `m > n`.

Source: Eduardo H. M. Brietzke, *Recurrence Relations for Sums of Binomial Coefficients and
Some Generalizations*, Journal of Integer Sequences 27 (2024), Article 24.3.4, Proposition 5. -/
public theorem_wanted riordan_stepSum_coeff {K : Type*} [Field K] (g h : PowerSeries K)
    (hh : PowerSeries.constantCoeff h = 0) (k p : ℕ) (hk : 1 < k) (hp : p < k) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), PowerSeries.coeff n (g * h ^ (k * j + p)) =
      PowerSeries.coeff n (g * h ^ p * (1 - h ^ k)⁻¹)

/-- Window criterion for step-`k` binomial sums. For integers `α, k > 1`, `γ ≥ 1` and
`0 ≤ p < k`, let `c(n) = ∑_{j ∈ ℤ} binom(αn, γn + p + kj)`, written as the sum of
`binom(αn, m)` over `0 ≤ m ≤ αn` with `m ≡ γn + p (mod k)`. If
`c(n) = ∑_{i=1}^s δ_i c(n - i)` with integers `δ_i` for `s ≤ n ≤ k² + s - 1`, then it holds
for all `n ≥ s`. The `δ_i` are only required to work for the given `p`; the printed hypothesis
(one `δ` for every `p`) is a special case.

Source: Eduardo H. M. Brietzke, *Recurrence Relations for Sums of Binomial Coefficients and
Some Generalizations*, Journal of Integer Sequences 27 (2024), Article 24.3.4, Proposition 8. -/
public theorem_wanted binomialStepSum_recurrence_of_window (α k γ p s : ℕ) (hα : 1 < α)
    (hk : 1 < k) (hγ : 1 ≤ γ) (hp : p < k) (δ : ℕ → ℤ) :
    let c : ℕ → ℤ := fun n =>
      ∑ m ∈ (Finset.range (α * n + 1)).filter (fun m => m % k = (γ * n + p) % k),
        ((α * n).choose m : ℤ)
    (∀ n, s ≤ n → n ≤ k ^ 2 + s - 1 → c n = ∑ i ∈ Finset.Icc 1 s, δ i * c (n - i)) →
      ∀ n, s ≤ n → c n = ∑ i ∈ Finset.Icc 1 s, δ i * c (n - i)

/-- Window criterion for shifted step-`k` binomial sums. For integers `α, k, γ > 1`, `β ≥ 0`
and `0 ≤ p < k`, let `c(n) = ∑_{j ∈ ℤ} binom(αn + β, γn + p + kj)`, written as the sum of
`binom(αn + β, m)` over `0 ≤ m ≤ αn + β` with `m ≡ γn + p (mod k)`. If
`c(n) = ∑_{i=1}^s δ_i c(n - i)` with integers `δ_i` for `s ≤ n ≤ k² + s - 1`, then it holds
for all `n ≥ s`. The `δ_i` are only required to work for the given `p`; the printed hypothesis
(one `δ` for every `p`) is a special case.

Source: Eduardo H. M. Brietzke, *Recurrence Relations for Sums of Binomial Coefficients and
Some Generalizations*, Journal of Integer Sequences 27 (2024), Article 24.3.4, Theorem 9. -/
public theorem_wanted shiftedBinomialStepSum_recurrence_of_window (α β k γ p s : ℕ)
    (hα : 1 < α) (hk : 1 < k) (hγ : 1 < γ) (hp : p < k) (δ : ℕ → ℤ) :
    let c : ℕ → ℤ := fun n =>
      ∑ m ∈ (Finset.range (α * n + β + 1)).filter (fun m => m % k = (γ * n + p) % k),
        ((α * n + β).choose m : ℤ)
    (∀ n, s ≤ n → n ≤ k ^ 2 + s - 1 → c n = ∑ i ∈ Finset.Icc 1 s, δ i * c (n - i)) →
      ∀ n, s ≤ n → c n = ∑ i ∈ Finset.Icc 1 s, δ i * c (n - i)

/-- Step-`k` sums of a rational Riordan array are C-finite, uniformly in the residue. Let
`g = g₁/g₂` and `h = x^ν h₁/h₂` with `g₁, g₂, h₁, h₂ ∈ ℤ[x]`, `g₂(0) = h₁(0) = h₂(0) = 1`,
`ν ≥ 1`, and `d(n, m) = [x^n] g h^m` (computed in `ℚ[[x]]`). For every `k ≥ 1` there are an
order `r` and integers `α_1, …, α_r`, independent of `p`, such that for every `p < k`,
`a_p(n) = ∑_j d(n, kj + p)` satisfies `a_p(n) = ∑_{i=1}^r α_i a_p(n - i)` for all `n ≥ r`.

Source: Eduardo H. M. Brietzke, *Recurrence Relations for Sums of Binomial Coefficients and
Some Generalizations*, Journal of Integer Sequences 27 (2024), Article 24.3.4,
Proposition 11. -/
public theorem_wanted rationalRiordan_stepSum_linearRecurrence (g₁ g₂ h₁ h₂ : ℤ[X]) (ν : ℕ)
    (hg₂ : g₂.eval 0 = 1) (hh₁ : h₁.eval 0 = 1) (hh₂ : h₂.eval 0 = 1) (hν : 1 ≤ ν)
    (k : ℕ) (hk : 0 < k) :
    let toQ : ℤ[X] → PowerSeries ℚ := fun q => ((q.map (Int.castRingHom ℚ)) : PowerSeries ℚ)
    let g : PowerSeries ℚ := toQ g₁ * (toQ g₂)⁻¹
    let h : PowerSeries ℚ := PowerSeries.X ^ ν * toQ h₁ * (toQ h₂)⁻¹
    let a : ℕ → ℕ → ℚ := fun p n =>
      ∑ j ∈ Finset.range (n + 1), PowerSeries.coeff n (g * h ^ (k * j + p))
    ∃ (r : ℕ) (αs : ℕ → ℤ), ∀ p < k, ∀ n, r ≤ n →
      a p n = ∑ i ∈ Finset.Icc 1 r, (αs i : ℚ) * a p (n - i)

/-- Step-five alternating sums of Catalan's triangle (OEIS A039598) give Fibonacci numbers.
For the Riordan array `(g, xg)` with `g(x) = (1 - 2x - √(1 - 4x)) / (2x²)`, whose entries are
`d(n, k) = (k + 1)/(n + 1) · C(2(n + 1), n - k)` for `k ≤ n` (and `0` for `k > n`),
`∑_{j ≥ 0} (d(n, 5j+1) - d(n, 5j+2)) = F_{2n}` and
`∑_{j ≥ 0} (d(n, 5j) - d(n, 5j+3)) = F_{2n+1}`. The array is given by the paper's displayed
closed form; the sums run over `j ≤ n`, since `d(n, m) = 0` for `m > n`.

Source: Eduardo H. M. Brietzke, *Recurrence Relations for Sums of Binomial Coefficients and
Some Generalizations*, Journal of Integer Sequences 27 (2024), Article 24.3.4,
Proposition 13. -/
public theorem_wanted catalanTriangle_stepFive_sub_eq_fib (n : ℕ) :
    let d : ℕ → ℕ → ℚ := fun n k =>
      if k ≤ n then (k + 1 : ℚ) / (n + 1) * ((2 * (n + 1)).choose (n - k) : ℚ) else 0
    ∑ j ∈ Finset.range (n + 1), (d n (5 * j + 1) - d n (5 * j + 2)) = Nat.fib (2 * n) ∧
      ∑ j ∈ Finset.range (n + 1), (d n (5 * j) - d n (5 * j + 3)) = Nat.fib (2 * n + 1)

end

end MetaMathlibExt
