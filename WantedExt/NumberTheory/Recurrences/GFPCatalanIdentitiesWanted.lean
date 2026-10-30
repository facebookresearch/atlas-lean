/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Catalan identities for generalized Fibonacci polynomials

Statements from Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero
Rojas, *Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62
(2024), Article florez11012023.

A generalized Fibonacci polynomial (GFP) of Fibonacci type is `F_0 = 0`, `F_1 = 1`,
`F_n = d F_{n-1} + g F_{n-2}`; one of Lucas type is `L_0 = p₀`, `L_1 = p₁`, same recurrence,
where `α p₀ = 2` for an integer `α` (so `|p₀| ∈ {1, 2}`) and `d = α p₁` (paper, (2.1), (2.2)).
Both are the existing `generalizedFibonacciPolynomial` over `ℤ[X]`, so the paper's `ℚ[x]`
coefficients are restricted to `ℤ[x]`; the identities hold without the paper's nonzero
assumptions on `p₁`, `d`, `g`, except Proposition 5.2, whose negative-index terms need
`g(x) ≠ 0`. Identities with a factor `1/2^{n-1}` or `1/α` are stated with
cleared denominators. Section 5 evaluates the polynomials at a real `x` with
`d(x)² + 4 g(x) ≥ 0`, so that the square root is real.

Section 4 uses the sums `T_ℓ(n; t) = ∑_i C(n, i) t^{⌊i/ℓ⌋}` and
`T_{ℓ,s}(n; t) = ∑_i C(n, ℓ i + s) t^i` ((4.1), (4.2)) for `t` in a commutative ring; they are
written inline, with `i` ranging over `0, …, n`.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.RingTheory.Binomial
public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.NumberTheory.GeneralizedFibonacciPolynomial

namespace MetaMathlibExt

open Polynomial Finset

@[expose] public section

/-- Lemma 3.1 (1) (quoted from Flórez and Saunders): for `n ≥ 1`, the Fibonacci-type GFP is
`F_n = ∑_{i=0}^{⌊(n-1)/2⌋} C(n-i-1, i) d^{n-2i-1} g^i`.

Source: Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas,
*Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024),
Article florez11012023, Lemma 3.1 (1) (`fq-2024-florez11012023-lem-3.1`). -/
public theorem_wanted gfp_fib_eq_sum_choose (d g : ℤ[X]) {n : ℕ} (hn : 1 ≤ n) :
    generalizedFibonacciPolynomial 0 1 d g n =
      ∑ i ∈ range ((n - 1) / 2 + 1), ((n - i - 1).choose i : ℤ[X]) * d ^ (n - 2 * i - 1) * g ^ i

/-- Lemma 3.1 (2) (quoted from Flórez and Saunders): for `n ≥ 1`, the Lucas-type GFP satisfies
`α L_n = ∑_{i=0}^{⌊n/2⌋} (n/(n-i)) C(n-i, i) d^{n-2i} g^i`. The integer `n/(n-i) · C(n-i, i)`
is written as an exact `ℕ` quotient.

Source: Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas,
*Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024),
Article florez11012023, Lemma 3.1 (2) (`fq-2024-florez11012023-lem-3.1`). -/
public theorem_wanted gfp_lucas_eq_sum_choose {α p₀ : ℤ} (hα : α * p₀ = 2) {p₁ d : ℤ[X]}
    (hd : d = C α * p₁) (g : ℤ[X]) {n : ℕ} (hn : 1 ≤ n) :
    C α * generalizedFibonacciPolynomial (C p₀) p₁ d g n =
      ∑ i ∈ range (n / 2 + 1),
        ((n * (n - i).choose i / (n - i) : ℕ) : ℤ[X]) * d ^ (n - 2 * i) * g ^ i

/-- Lemma 3.2 (1) (Webb and Parberry): for `0 ≤ m < n`,
`C(n-m-1, m) = 2^{2m-n+1} ∑_{j=m}^{⌊(n-1)/2⌋} C(j, m) C(n, 2j+1)`.

Source: Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas,
*Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024),
Article florez11012023, Lemma 3.2 (1) (`fq-2024-florez11012023-lem-3.2`). -/
public theorem_wanted choose_sub_sub_one_eq_two_zpow_mul_sum {m n : ℕ} (hmn : m < n) :
    ((n - m - 1).choose m : ℚ) =
      (2 : ℚ) ^ (2 * (m : ℤ) - n + 1) *
        ∑ j ∈ Icc m ((n - 1) / 2), (j.choose m : ℚ) * (n.choose (2 * j + 1) : ℚ)

/-- Lemma 3.2 (2): for `0 ≤ k < ⌊(n-1)/2⌋`,
`C(n, 2k+1) = ∑_{i=k}^{⌊(n-1)/2⌋} (-1)^{i-k} 2^{n-2i-1} C(n-i-1, i) C(i, k)`.

Source: Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas,
*Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024),
Article florez11012023, Lemma 3.2 (2) (`fq-2024-florez11012023-lem-3.2`). -/
public theorem_wanted choose_two_mul_add_one_eq_alternating_sum {n k : ℕ}
    (hk : k < (n - 1) / 2) :
    (n.choose (2 * k + 1) : ℤ) =
      ∑ i ∈ Icc k ((n - 1) / 2),
        (-1) ^ (i - k) * 2 ^ (n - 2 * i - 1) * ((n - i - 1).choose i : ℤ) * (i.choose k : ℤ)

/-- Lemma 3.2 (3): for `0 ≤ k < ⌊n/2⌋`,
`C(n, 2k) = n ∑_{i=k}^{⌊n/2⌋} ((-1)^{i-k}/(n-i)) 2^{n-2i-1} C(n-i, i) C(i, k)`.

Source: Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas,
*Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024),
Article florez11012023, Lemma 3.2 (3) (`fq-2024-florez11012023-lem-3.2`). -/
public theorem_wanted choose_two_mul_eq_alternating_sum {n k : ℕ} (hk : k < n / 2) :
    (n.choose (2 * k) : ℚ) =
      n * ∑ i ∈ Icc k (n / 2),
        (-1) ^ (i - k) / ((n : ℚ) - i) * (2 : ℚ) ^ ((n : ℤ) - 2 * i - 1) *
          ((n - i).choose i : ℚ) * (i.choose k : ℚ)

/-- Theorem 3.3 (1) (Catalan identity for GFPs of Fibonacci type): for `n ≥ 0`,
`2^{n-1} F_n = ∑_{i=0}^{⌊(n-1)/2⌋} C(n, 2i+1) d^{n-2i-1} (4g + d²)^i`.

Source: Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas,
*Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024),
Article florez11012023, Theorem 3.3 (1) (`fq-2024-florez11012023-thm-3.3`). -/
public theorem_wanted gfp_fib_catalan (d g : ℤ[X]) (n : ℕ) :
    2 ^ (n - 1) * generalizedFibonacciPolynomial 0 1 d g n =
      ∑ i ∈ range ((n - 1) / 2 + 1),
        (n.choose (2 * i + 1) : ℤ[X]) * d ^ (n - 2 * i - 1) * (4 * g + d ^ 2) ^ i

/-- Theorem 3.3 (2) (Catalan identity for GFPs of Lucas type): for `n ≥ 0`,
`α 2^{n-1} L_n = ∑_{i=0}^{⌊n/2⌋} C(n, 2i) d^{n-2i} (4g + d²)^i`, stated as
`2^n α L_n = 2 ∑ …` so that `n = 0` is included.

Source: Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas,
*Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024),
Article florez11012023, Theorem 3.3 (2) (`fq-2024-florez11012023-thm-3.3`). -/
public theorem_wanted gfp_lucas_catalan {α p₀ : ℤ} (hα : α * p₀ = 2) {p₁ d : ℤ[X]}
    (hd : d = C α * p₁) (g : ℤ[X]) (n : ℕ) :
    2 ^ n * C α * generalizedFibonacciPolynomial (C p₀) p₁ d g n =
      2 * ∑ i ∈ range (n / 2 + 1), (n.choose (2 * i) : ℤ[X]) * d ^ (n - 2 * i) * (4 * g + d ^ 2) ^ i

/-- Lemma 4.1: for `1 ≤ ℓ ≤ n`, `s ≥ 0` and `j ≤ ⌊(n-s)/ℓ⌋`,
`∑_i C(ℓ, i) (-1)^i C(n-i, ℓj+s) = C(n-ℓ, ℓ(j-1)+s)`. Stated for `j ≥ 1` (the paper's range
also admits `⌊(1-s)/ℓ⌋ ≤ j ≤ 0`, where the right side can have a negative lower index), with
`j ≤ ⌊(n-s)/ℓ⌋` written as `ℓ j + s ≤ n`; the sum runs over `i ≤ ℓ`.

Source: Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas,
*Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024),
Article florez11012023, Lemma 4.1 (`fq-2024-florez11012023-lem-4.1`). -/
public theorem_wanted alternating_sum_choose_mul_choose_sub {ℓ n j s : ℕ} (hℓ : 1 ≤ ℓ)
    (hℓn : ℓ ≤ n) (hj : 1 ≤ j) (hjn : ℓ * j + s ≤ n) :
    ∑ i ∈ range (ℓ + 1), (ℓ.choose i : ℤ) * (-1) ^ i * ((n - i).choose (ℓ * j + s) : ℤ) =
      ((n - ℓ).choose (ℓ * (j - 1) + s) : ℤ)

/-- Theorem 4.2: for `n ≥ 0` and `ℓ ≥ 1`, the sums `T_ℓ(n; t) = ∑_i C(n, i) t^{⌊i/ℓ⌋}` satisfy
`∑_{i=0}^{ℓ} C(ℓ, i) (-1)^i T_ℓ(n+ℓ-i; t) - t T_ℓ(n; t) = 0`.

Source: Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas,
*Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024),
Article florez11012023, Theorem 4.2 (`fq-2024-florez11012023-thm-4.2`). -/
public theorem_wanted floorPowBinomialSum_recurrence {R : Type*} [CommRing R] (t : R) {ℓ : ℕ}
    (hℓ : 1 ≤ ℓ) (n : ℕ) :
    ∑ i ∈ range (ℓ + 1), (ℓ.choose i : R) * (-1) ^ i *
        ∑ j ∈ range (n + ℓ - i + 1), ((n + ℓ - i).choose j : R) * t ^ (j / ℓ) -
      t * ∑ j ∈ range (n + 1), (n.choose j : R) * t ^ (j / ℓ) = 0

/-- Lemma 4.3: for `n ≥ 0`,
`∑_{i=0}^{n} C(ℓ, i) (-1)^i ∑_{j=0}^{n-i} C(n-i, j) = ∑_{i=0}^{n} (-1)^i C(i+ℓ-n-1, i)`.
The right side has an integer upper index, read as the generalized binomial coefficient
`Ring.choose`; it is the ordinary one for `n < ℓ`, the case used in Theorem 4.4.

Source: Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas,
*Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024),
Article florez11012023, Lemma 4.3 (`fq-2024-florez11012023-lem-4.3`). -/
public theorem_wanted alternating_choose_mul_sum_choose (ℓ n : ℕ) :
    ∑ i ∈ range (n + 1), (ℓ.choose i : ℤ) * (-1) ^ i *
        ∑ j ∈ range (n - i + 1), ((n - i).choose j : ℤ) =
      ∑ i ∈ range (n + 1), (-1) ^ i * Ring.choose ((i : ℤ) + ℓ - n - 1) i

/-- Theorem 4.4: for `ℓ ≥ 1`, the generating function of `T_ℓ(n; t) = ∑_i C(n, i) t^{⌊i/ℓ⌋}` is
`(∑_{k=0}^{ℓ-1} ∑_{i=0}^{k} (-1)^i C(i+ℓ-k-1, i) x^k) / ((1-x)^ℓ - t x^ℓ)`, stated as a
product identity of formal power series.

Source: Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas,
*Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024),
Article florez11012023, Theorem 4.4 (`fq-2024-florez11012023-thm-4.4`). -/
public theorem_wanted floorPowBinomialSum_generatingFunction {R : Type*} [CommRing R] (t : R)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    PowerSeries.mk (fun n => ∑ i ∈ range (n + 1), (n.choose i : R) * t ^ (i / ℓ)) *
        ((1 - PowerSeries.X) ^ ℓ - PowerSeries.C t * PowerSeries.X ^ ℓ) =
      ∑ k ∈ range ℓ, PowerSeries.C (∑ i ∈ range (k + 1),
        (-1 : R) ^ i * ((i + ℓ - k - 1).choose i : R)) * PowerSeries.X ^ k

/-- Theorem 4.5: for `0 ≤ s < ℓ`, the generating function of
`T_{ℓ,s}(n; t) = ∑_i C(n, ℓ i + s) t^i` is
`(∑_{k=0}^{ℓ-1} ∑_{i=0}^{k} (-1)^i C(ℓ, i) ∑_{r=0}^{k} C(k-i, rℓ+s) t^r x^k) / ((1-x)^ℓ - t x^ℓ)`,
stated as a product identity of formal power series. The printed numerator has `t^t`, a typo
for `t^r` (the summation index); the range `s < ℓ` is the one of (4.4). For `s ≥ ℓ` the identity
fails (`ℓ = 1`, `s = 1`, `t = 2`: the left side is `x/(1 - x)`, the right side `0`).

Source: Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas,
*Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024),
Article florez11012023, Theorem 4.5 (`fq-2024-florez11012023-thm-4.5`). -/
public theorem_wanted sectionBinomialSum_generatingFunction {R : Type*} [CommRing R] (t : R)
    {ℓ s : ℕ} (hs : s < ℓ) :
    PowerSeries.mk (fun n => ∑ i ∈ range (n + 1), (n.choose (ℓ * i + s) : R) * t ^ i) *
        ((1 - PowerSeries.X) ^ ℓ - PowerSeries.C t * PowerSeries.X ^ ℓ) =
      ∑ k ∈ range ℓ, PowerSeries.C (∑ i ∈ range (k + 1), (-1 : R) ^ i * (ℓ.choose i : R) *
        ∑ r ∈ range (k + 1), ((k - i).choose (r * ℓ + s) : R) * t ^ r) * PowerSeries.X ^ k

/-- Proposition 5.1: for `n ≥ 2` and a real `x` with `d(x)² + 4 g(x) ≥ 0`,
`F_n(x) = (n / 2^n) ∫_{-1}^{1} (d(x) + y √(d(x)² + 4 g(x)))^{n-1} dy`.

Source: Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas,
*Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024),
Article florez11012023, Proposition 5.1 (`fq-2024-florez11012023-prop-5.1`). -/
public theorem_wanted gfp_fib_eval_eq_integral (d g : ℤ[X]) (x : ℝ)
    (hx : 0 ≤ aeval x d ^ 2 + 4 * aeval x g) {n : ℕ} (hn : 2 ≤ n) :
    aeval x (generalizedFibonacciPolynomial 0 1 d g n) =
      n / 2 ^ n * ∫ y in (-1 : ℝ)..1,
        (aeval x d + y * Real.sqrt (aeval x d ^ 2 + 4 * aeval x g)) ^ (n - 1)

/-- Corollary 5.1 (Stewart): `F_n = (n / 2^n) ∫_{-1}^{1} (1 + y √5)^{n-1} dy`. The corollary
states no range; it is stated for `n ≥ 1`, where the exponent `n - 1` is a natural number.

Source: Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas,
*Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024),
Article florez11012023, Corollary 5.1 (`fq-2024-florez11012023-cor-5.1`). -/
public theorem_wanted fib_eq_integral_one_add_mul_sqrt_five {n : ℕ} (hn : 1 ≤ n) :
    (Nat.fib n : ℝ) = n / 2 ^ n * ∫ y in (-1 : ℝ)..1, (1 + y * Real.sqrt 5) ^ (n - 1)

/-- Proposition 5.2: for real `k ≥ 2`, `n ≥ 1` and a real `x` with `d(x)² + 4 g(x) ≥ 0`,
`∑_{i=0}^{n} (-1)^{n+1} C(n, i) (k+1)^i (k-1)^{n-i} g^i F_{n-2i}
  = n ∫_{-k}^{k} (y √(d² + 4g) + d)^{n-1} dy`.
The indices `n - 2i < 0` use the extension `F : ℤ → ℝ` of `m ↦ F_m(x)` by the same recurrence
(the Binet formula of the paper's proof). This extension exists only when `g(x) ≠ 0` (if
`g(x) = 0`, the recurrence at `m = -1` forces `F_1 = d(x) F_0 = 0`), so the paper's assumption
`g ≠ 0` is kept as `g(x) ≠ 0`. The paper states no range for `n`; `n ≥ 1` makes the exponent
`n - 1` a natural number.

Source: Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas,
*Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024),
Article florez11012023, Proposition 5.2 (`fq-2024-florez11012023-prop-5.2`). -/
public theorem_wanted gfp_fib_binomial_sum_eq_integral (d g : ℤ[X]) (x : ℝ)
    (hx : 0 ≤ aeval x d ^ 2 + 4 * aeval x g) (hg : aeval x g ≠ 0) (F : ℤ → ℝ)
    (hF : ∀ m : ℕ, F m = aeval x (generalizedFibonacciPolynomial 0 1 d g m))
    (hrec : ∀ m : ℤ, F (m + 2) = aeval x d * F (m + 1) + aeval x g * F m)
    {k : ℝ} (hk : 2 ≤ k) {n : ℕ} (hn : 1 ≤ n) :
    ∑ i ∈ range (n + 1), (-1) ^ (n + 1) * (n.choose i : ℝ) * (k + 1) ^ i * (k - 1) ^ (n - i) *
        aeval x g ^ i * F ((n : ℤ) - 2 * i) =
      n * ∫ y in -k..k, (y * Real.sqrt (aeval x d ^ 2 + 4 * aeval x g) + aeval x d) ^ (n - 1)

/-- Corollary 5.2: for real `k ≥ 2` and `n ≥ 1`,
`∑_{i=0}^{n} (-1)^{n+1} C(n, i) (k+1)^i (k-1)^{n-i} F_{n-2i} = n ∫_{-k}^{k} (√5 y + 1)^{n-1} dy`,
where `F : ℤ → ℝ` is the Fibonacci sequence extended to negative indices by its recurrence. The
paper states no range for `n`; `n ≥ 1` makes the exponent `n - 1` a natural number.

Source: Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas,
*Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024),
Article florez11012023, Corollary 5.2 (`fq-2024-florez11012023-cor-5.2`). -/
public theorem_wanted fib_binomial_sum_eq_integral (F : ℤ → ℝ) (hF : ∀ m : ℕ, F m = Nat.fib m)
    (hrec : ∀ m : ℤ, F (m + 2) = F (m + 1) + F m) {k : ℝ} (hk : 2 ≤ k) {n : ℕ} (hn : 1 ≤ n) :
    ∑ i ∈ range (n + 1), (-1) ^ (n + 1) * (n.choose i : ℝ) * (k + 1) ^ i * (k - 1) ^ (n - i) *
        F ((n : ℤ) - 2 * i) =
      n * ∫ y in -k..k, (Real.sqrt 5 * y + 1) ^ (n - 1)

end

end MetaMathlibExt
