/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Infinite sums involving powers of gibonacci polynomials

Statements from Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024.

The Fibonacci polynomials `f_n(x)` (`f_0 = 0`, `f_1 = 1`) and Lucas polynomials `ℓ_n(x)`
(`ℓ_0 = 2`, `ℓ_1 = x`), both with `g_{n+2} = x g_{n+1} + g_n`, are the existing
`generalizedFibonacciPolynomial` sequences over `ℤ[X]`; `Δ² = x² + 4`. Real-variable statements
evaluate them with `Polynomial.aeval`.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import MathlibExt.NumberTheory.GeneralizedFibonacciPolynomial
public import MathlibExt.NumberTheory.LucasSequence

namespace MetaMathlibExt

open Polynomial

@[expose] public section

/-- The Fibonacci polynomials `f_n(x)`. -/
local notation "𝔣" => generalizedFibonacciPolynomial 0 1 X 1

/-- The Lucas polynomials `ℓ_n(x)`. -/
local notation "𝔩" => generalizedFibonacciPolynomial 2 X X 1

/-- The paper's lower summation limit `L`: `(k + 1)/2` for odd `k`, `k/2 + 1` for even `k`. -/
local notation "𝔏[" k "]" => ite (Odd k) ((k + 1) / 2) (k / 2 + 1)

/-- The paper's lower summation limit `M`: `(k + 1)/2` for odd `k`, `k/2` for even `k`. -/
local notation "𝔐[" k "]" => ite (Odd k) ((k + 1) / 2) (k / 2)

/-- The paper's index `s`: `2r - 1` for odd `k`, `2r` for even `k`. -/
local notation "𝔰[" k ", " r "]" => ite (Odd k) (2 * r - 1) (2 * r)

/-- The paper's index `t`: `2r` for odd `k`, `2r - 1` for even `k`. -/
local notation "𝔱[" k ", " r "]" => ite (Odd k) (2 * r) (2 * r - 1)

/-- Lemma 2.1 (quoted from Koshy): for `k ≤ n`,
`f_{n+k} f_{n-k} - f_n² = (-1)^{n+k+1} f_k²` and `ℓ_{n+k} ℓ_{n-k} - ℓ_n² = (-1)^{n+k} Δ² f_k²`.

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Lemma 2.1 (`fq-2024-linzhou02172024-lem-2.1`). -/
public theorem_wanted gibonacciPoly_mul_sub_sq {n k : ℕ} (hk : k ≤ n) :
    𝔣 (n + k) * 𝔣 (n - k) - 𝔣 n ^ 2 = (-1) ^ (n + k + 1) * 𝔣 k ^ 2 ∧
      𝔩 (n + k) * 𝔩 (n - k) - 𝔩 n ^ 2 = (-1) ^ (n + k) * (X ^ 2 + 4) * 𝔣 k ^ 2

/-- Lemma 2.2 (quoted from Koshy): for `x > 0`, `g ∈ {f, ℓ}`, odd `k` and a positive integer `λ`,
`Σ_{n ≥ (k + 1)/2} (1/g_{2n-k}^λ - 1/g_{2n+k}^λ) = Σ_{r=1}^k 1/g_{2r-1}^λ`
(summation index shifted to start at `0`).

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Lemma 2.2 (`fq-2024-linzhou02172024-lem-2.2`). -/
public theorem_wanted tsum_inv_pow_gibonacciPoly_sub_odd {x : ℝ} (hx : 0 < x)
    {g : ℕ → ℤ[X]} (hg : g = 𝔣 ∨ g = 𝔩) {k lam : ℕ} (hk : Odd k) (hlam : 0 < lam) :
    ∑' n : ℕ, (1 / aeval x (g (2 * n + 1)) ^ lam - 1 / aeval x (g (2 * n + 1 + 2 * k)) ^ lam) =
      ∑ r ∈ Finset.Icc 1 k, 1 / aeval x (g (2 * r - 1)) ^ lam

/-- Lemma 2.3 (quoted from Koshy): for `x > 0`, `g ∈ {f, ℓ}`, even `k` and a positive integer `λ`,
`Σ_{n ≥ k/2 + 1} (1/g_{2n-k}^λ - 1/g_{2n+k}^λ) = Σ_{r=1}^k 1/g_{2r}^λ`
(summation index shifted to start at `0`).

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Lemma 2.3 (`fq-2024-linzhou02172024-lem-2.3`). -/
public theorem_wanted tsum_inv_pow_gibonacciPoly_sub_even {x : ℝ} (hx : 0 < x)
    {g : ℕ → ℤ[X]} (hg : g = 𝔣 ∨ g = 𝔩) {k lam : ℕ} (hk : Even k) (hlam : 0 < lam) :
    ∑' n : ℕ, (1 / aeval x (g (2 * n + 2)) ^ lam - 1 / aeval x (g (2 * n + 2 + 2 * k)) ^ lam) =
      ∑ r ∈ Finset.Icc 1 k, 1 / aeval x (g (2 * r)) ^ lam

/-- Lemma 2.4 (quoted from Koshy): for `x > 0`, `g ∈ {f, ℓ}`, odd `k` and a positive integer `λ`,
`Σ_{n ≥ (k + 1)/2} (1/g_{2n+1-k}^λ - 1/g_{2n+1+k}^λ) = Σ_{r=1}^k 1/g_{2r}^λ`
(summation index shifted to start at `0`).

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Lemma 2.4 (`fq-2024-linzhou02172024-lem-2.4`). -/
public theorem_wanted tsum_inv_pow_gibonacciPoly_succ_sub_odd {x : ℝ} (hx : 0 < x)
    {g : ℕ → ℤ[X]} (hg : g = 𝔣 ∨ g = 𝔩) {k lam : ℕ} (hk : Odd k) (hlam : 0 < lam) :
    ∑' n : ℕ, (1 / aeval x (g (2 * n + 2)) ^ lam - 1 / aeval x (g (2 * n + 2 + 2 * k)) ^ lam) =
      ∑ r ∈ Finset.Icc 1 k, 1 / aeval x (g (2 * r)) ^ lam

/-- Lemma 2.5 (quoted from Koshy): for `x > 0`, `g ∈ {f, ℓ}`, even `k` and a positive integer `λ`,
`Σ_{n ≥ k/2} (1/g_{2n+1-k}^λ - 1/g_{2n+1+k}^λ) = Σ_{r=1}^k 1/g_{2r-1}^λ`
(summation index shifted to start at `0`).

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Lemma 2.5 (`fq-2024-linzhou02172024-lem-2.5`). -/
public theorem_wanted tsum_inv_pow_gibonacciPoly_succ_sub_even {x : ℝ} (hx : 0 < x)
    {g : ℕ → ℤ[X]} (hg : g = 𝔣 ∨ g = 𝔩) {k lam : ℕ} (hk : Even k) (hlam : 0 < lam) :
    ∑' n : ℕ, (1 / aeval x (g (2 * n + 1)) ^ lam - 1 / aeval x (g (2 * n + 1 + 2 * k)) ^ lam) =
      ∑ r ∈ Finset.Icc 1 k, 1 / aeval x (g (2 * r - 1)) ^ lam

/-- Lemma 3.1: for `k ≤ n`,
`Δ^{2(m-1)}(f_{n+k}^{2m} - f_{n-k}^{2m})
  = Σ_{j=0}^{m-1} C(2m, j)(-1)^{(n+k+1)j} f_{2k(m-j)} f_{2n(m-j)}`.

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Lemma 3.1 (`fq-2024-linzhou02172024-lem-3.1`). -/
public theorem_wanted fibPoly_pow_even_sub {n k : ℕ} (hk : k ≤ n) (m : ℕ) :
    (X ^ 2 + 4) ^ (m - 1) * (𝔣 (n + k) ^ (2 * m) - 𝔣 (n - k) ^ (2 * m)) =
      ∑ j ∈ Finset.range m, ((2 * m).choose j : ℤ[X]) * (-1) ^ ((n + k + 1) * j) *
        𝔣 (2 * k * (m - j)) * 𝔣 (2 * n * (m - j))

/-- Lemma 3.2: for `k ≤ n`,
`ℓ_{n+k}^{2m} - ℓ_{n-k}^{2m} = Δ² Σ_{j=0}^{m-1} C(2m, j)(-1)^{(n+k)j} f_{2k(m-j)} f_{2n(m-j)}`.

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Lemma 3.2 (`fq-2024-linzhou02172024-lem-3.2`). -/
public theorem_wanted lucasPoly_pow_even_sub {n k : ℕ} (hk : k ≤ n) (m : ℕ) :
    𝔩 (n + k) ^ (2 * m) - 𝔩 (n - k) ^ (2 * m) =
      (X ^ 2 + 4) * ∑ j ∈ Finset.range m, ((2 * m).choose j : ℤ[X]) * (-1) ^ ((n + k) * j) *
        𝔣 (2 * k * (m - j)) * 𝔣 (2 * n * (m - j))

/-- Lemma 4.1: for `k ≤ n` and `m ∈ ℕ`, `Δ^{2m}(f_{n+k}^{2m+1} - f_{n-k}^{2m+1})` equals
`Σ_{j=0}^m C(2m+1, j)(-1)^{nj} f_{n(2m+1-2j)} ℓ_{k(2m+1-2j)}` if `k` is odd and
`Σ_{j=0}^m C(2m+1, j)(-1)^{(n+1)j} ℓ_{n(2m+1-2j)} f_{k(2m+1-2j)}` otherwise.

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Lemma 4.1 (`fq-2024-linzhou02172024-lem-4.1`). -/
public theorem_wanted fibPoly_pow_odd_sub {n k : ℕ} (hk : k ≤ n) (m : ℕ) :
    (Odd k → (X ^ 2 + 4) ^ m * (𝔣 (n + k) ^ (2 * m + 1) - 𝔣 (n - k) ^ (2 * m + 1)) =
      ∑ j ∈ Finset.range (m + 1), ((2 * m + 1).choose j : ℤ[X]) * (-1) ^ (n * j) *
        𝔣 (n * (2 * m + 1 - 2 * j)) * 𝔩 (k * (2 * m + 1 - 2 * j))) ∧
    (Even k → (X ^ 2 + 4) ^ m * (𝔣 (n + k) ^ (2 * m + 1) - 𝔣 (n - k) ^ (2 * m + 1)) =
      ∑ j ∈ Finset.range (m + 1), ((2 * m + 1).choose j : ℤ[X]) * (-1) ^ ((n + 1) * j) *
        𝔩 (n * (2 * m + 1 - 2 * j)) * 𝔣 (k * (2 * m + 1 - 2 * j)))

/-- Lemma 4.2: for `k ≤ n` and `m ∈ ℕ`, `ℓ_{n+k}^{2m+1} - ℓ_{n-k}^{2m+1}` equals
`Σ_{j=0}^m C(2m+1, j)(-1)^{(n+1)j} ℓ_{n(2m+1-2j)} ℓ_{k(2m+1-2j)}` if `k` is odd and
`Δ² Σ_{j=0}^m C(2m+1, j)(-1)^{nj} f_{n(2m+1-2j)} f_{k(2m+1-2j)}` otherwise.

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Lemma 4.2 (`fq-2024-linzhou02172024-lem-4.2`). -/
public theorem_wanted lucasPoly_pow_odd_sub {n k : ℕ} (hk : k ≤ n) (m : ℕ) :
    (Odd k → 𝔩 (n + k) ^ (2 * m + 1) - 𝔩 (n - k) ^ (2 * m + 1) =
      ∑ j ∈ Finset.range (m + 1), ((2 * m + 1).choose j : ℤ[X]) * (-1) ^ ((n + 1) * j) *
        𝔩 (n * (2 * m + 1 - 2 * j)) * 𝔩 (k * (2 * m + 1 - 2 * j))) ∧
    (Even k → 𝔩 (n + k) ^ (2 * m + 1) - 𝔩 (n - k) ^ (2 * m + 1) =
      (X ^ 2 + 4) * ∑ j ∈ Finset.range (m + 1), ((2 * m + 1).choose j : ℤ[X]) *
        (-1) ^ (n * j) * 𝔣 (n * (2 * m + 1 - 2 * j)) * 𝔣 (k * (2 * m + 1 - 2 * j)))

/-- Corollary 4.3: for real `x > 0`,
`Σ_{n≥1} ((x³ + 3x)f_{6n} + 3x f_{2n})/(f_{2n}² + 1)³ = x² + 4` and
`Σ_{n≥2} (x(x⁴ + 4x² + 3)ℓ_{6n} - 3x ℓ_{2n})/(f_{2n}² - x²)³
  = (x² + 4)((x² + 2)³ + 1)/(x³(x² + 2)³)`.

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Corollary 4.3 (`fq-2024-linzhou02172024-cor-4.3`). -/
public theorem_wanted tsum_fibPoly_cube_even_index {x : ℝ} (hx : 0 < x) :
    ∑' n : ℕ, ((x ^ 3 + 3 * x) * aeval x (𝔣 (6 * (n + 1))) + 3 * x * aeval x (𝔣 (2 * (n + 1)))) /
        (aeval x (𝔣 (2 * (n + 1))) ^ 2 + 1) ^ 3 =
      x ^ 2 + 4 ∧
      ∑' n : ℕ, (x * (x ^ 4 + 4 * x ^ 2 + 3) * aeval x (𝔩 (6 * (n + 2))) -
          3 * x * aeval x (𝔩 (2 * (n + 2)))) /
          (aeval x (𝔣 (2 * (n + 2))) ^ 2 - x ^ 2) ^ 3 =
        (x ^ 2 + 4) * ((x ^ 2 + 2) ^ 3 + 1) / (x ^ 3 * (x ^ 2 + 2) ^ 3)

/-- Corollary 4.5: for real `x > 0`,
`Σ_{n≥1} ((x³ + 3x)ℓ_{6n} - 3x ℓ_{2n})/(ℓ_{2n}² - Δ²)³ = 1/x³` and
`Σ_{n≥2} (x(x⁴ + 4x² + 3)f_{6n} + 3x f_{2n})/(ℓ_{2n}² + (x² + 4)x²)³
  = (1/(x² + 4))(1/(x² + 2)³ + 1/(x⁴ + 4x² + 2)³)`.

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Corollary 4.5 (`fq-2024-linzhou02172024-cor-4.5`). -/
public theorem_wanted tsum_lucasPoly_cube_even_index {x : ℝ} (hx : 0 < x) :
    ∑' n : ℕ, ((x ^ 3 + 3 * x) * aeval x (𝔩 (6 * (n + 1))) - 3 * x * aeval x (𝔩 (2 * (n + 1)))) /
        (aeval x (𝔩 (2 * (n + 1))) ^ 2 - (x ^ 2 + 4)) ^ 3 =
      1 / x ^ 3 ∧
      ∑' n : ℕ, (x * (x ^ 4 + 4 * x ^ 2 + 3) * aeval x (𝔣 (6 * (n + 2))) +
          3 * x * aeval x (𝔣 (2 * (n + 2)))) /
          (aeval x (𝔩 (2 * (n + 2))) ^ 2 + (x ^ 2 + 4) * x ^ 2) ^ 3 =
        1 / (x ^ 2 + 4) * (1 / (x ^ 2 + 2) ^ 3 + 1 / (x ^ 4 + 4 * x ^ 2 + 2) ^ 3)

/-- Corollary 4.7: for real `x > 0`,
`Σ_{n≥1} ((x³ + 3x)f_{6n+3} - 3x f_{2n+1})/(f_{2n+1}² - 1)³ = (x² + 4)/x³` and
`Σ_{n≥1} (x(x⁴ + 4x² + 3)ℓ_{6n+3} + 3x ℓ_{2n+1})/(f_{2n+1}² + x²)³
  = (x² + 4)((x² + 1)³ + 1)/(x² + 1)³`.

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Corollary 4.7 (`fq-2024-linzhou02172024-cor-4.7`). -/
public theorem_wanted tsum_fibPoly_cube_odd_index {x : ℝ} (hx : 0 < x) :
    ∑' n : ℕ, ((x ^ 3 + 3 * x) * aeval x (𝔣 (6 * (n + 1) + 3)) -
          3 * x * aeval x (𝔣 (2 * (n + 1) + 1))) /
        (aeval x (𝔣 (2 * (n + 1) + 1)) ^ 2 - 1) ^ 3 =
      (x ^ 2 + 4) / x ^ 3 ∧
      ∑' n : ℕ, (x * (x ^ 4 + 4 * x ^ 2 + 3) * aeval x (𝔩 (6 * (n + 1) + 3)) +
          3 * x * aeval x (𝔩 (2 * (n + 1) + 1))) /
          (aeval x (𝔣 (2 * (n + 1) + 1)) ^ 2 + x ^ 2) ^ 3 =
        (x ^ 2 + 4) * ((x ^ 2 + 1) ^ 3 + 1) / (x ^ 2 + 1) ^ 3

/-- Corollary 4.9: for real `x > 0`,
`Σ_{n≥1} ((x³ + 3x)ℓ_{6n+3} + 3x ℓ_{2n+1})/(ℓ_{2n+1}² + x² + 4)³ = 1/(x² + 2)³` and
`Σ_{n≥1} (x(x⁴ + 4x² + 3)f_{6n+3} - 3x f_{2n+1})/(ℓ_{2n+1}² - x²(x² + 4))³
  = ((x² + 3)³ + 1)/(x³(x² + 4)(x² + 3)³)`.

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Corollary 4.9 (`fq-2024-linzhou02172024-cor-4.9`). -/
public theorem_wanted tsum_lucasPoly_cube_odd_index {x : ℝ} (hx : 0 < x) :
    ∑' n : ℕ, ((x ^ 3 + 3 * x) * aeval x (𝔩 (6 * (n + 1) + 3)) +
          3 * x * aeval x (𝔩 (2 * (n + 1) + 1))) /
        (aeval x (𝔩 (2 * (n + 1) + 1)) ^ 2 + x ^ 2 + 4) ^ 3 =
      1 / (x ^ 2 + 2) ^ 3 ∧
      ∑' n : ℕ, (x * (x ^ 4 + 4 * x ^ 2 + 3) * aeval x (𝔣 (6 * (n + 1) + 3)) -
          3 * x * aeval x (𝔣 (2 * (n + 1) + 1))) /
          (aeval x (𝔩 (2 * (n + 1) + 1)) ^ 2 - x ^ 2 * (x ^ 2 + 4)) ^ 3 =
        ((x ^ 2 + 3) ^ 3 + 1) / (x ^ 3 * (x ^ 2 + 4) * (x ^ 2 + 3) ^ 3)

/-- Corollary 4.4: `Σ_{n≥1} (4F_{6n} + 3F_{2n})/(F_{2n}² + 1)³ = 5` and
`Σ_{n≥2} (8L_{6n} - 3L_{2n})/(F_{2n}² - 1)³ = 140/27`.

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Corollary 4.4 (`fq-2024-linzhou02172024-cor-4.4`). -/
public theorem_wanted tsum_fib_cube_even_index :
    ∑' n : ℕ, (4 * (Nat.fib (6 * (n + 1)) : ℝ) + 3 * (Nat.fib (2 * (n + 1)) : ℝ)) /
        ((Nat.fib (2 * (n + 1)) : ℝ) ^ 2 + 1) ^ 3 = 5 ∧
      ∑' n : ℕ, (8 * (lucasNumber (6 * (n + 2)) : ℝ) - 3 * (lucasNumber (2 * (n + 2)) : ℝ)) /
          ((Nat.fib (2 * (n + 2)) : ℝ) ^ 2 - 1) ^ 3 = 140 / 27

/-- Corollary 4.6: `Σ_{n≥1} (4L_{6n} - 3L_{2n})/(L_{2n}² - 5)³ = 1` and
`Σ_{n≥2} (8F_{6n} + 3F_{2n})/(L_{2n}² + 5)³ = 74/9261`.

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Corollary 4.6 (`fq-2024-linzhou02172024-cor-4.6`). -/
public theorem_wanted tsum_lucas_cube_even_index :
    ∑' n : ℕ, (4 * (lucasNumber (6 * (n + 1)) : ℝ) - 3 * (lucasNumber (2 * (n + 1)) : ℝ)) /
        ((lucasNumber (2 * (n + 1)) : ℝ) ^ 2 - 5) ^ 3 = 1 ∧
      ∑' n : ℕ, (8 * (Nat.fib (6 * (n + 2)) : ℝ) + 3 * (Nat.fib (2 * (n + 2)) : ℝ)) /
          ((lucasNumber (2 * (n + 2)) : ℝ) ^ 2 + 5) ^ 3 = 74 / 9261

/-- Corollary 4.8: `Σ_{n≥1} (4F_{6n+3} - 3F_{2n+1})/(F_{2n+1}² - 1)³ = 5` and
`Σ_{n≥1} (8L_{6n+3} + 3L_{2n+1})/(F_{2n+1}² + 1)³ = 45/8` (the case `x = 1` of Corollary 4.7; the
extracted record prints the second lower limit as `n = 2`, under which the sum is
`45/8 - 124/25 = 133/200`).

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Corollary 4.8 (`fq-2024-linzhou02172024-cor-4.8`). -/
public theorem_wanted tsum_fib_cube_odd_index :
    ∑' n : ℕ, (4 * (Nat.fib (6 * (n + 1) + 3) : ℝ) - 3 * (Nat.fib (2 * (n + 1) + 1) : ℝ)) /
        ((Nat.fib (2 * (n + 1) + 1) : ℝ) ^ 2 - 1) ^ 3 = 5 ∧
      ∑' n : ℕ, (8 * (lucasNumber (6 * (n + 1) + 3) : ℝ) +
          3 * (lucasNumber (2 * (n + 1) + 1) : ℝ)) /
          ((Nat.fib (2 * (n + 1) + 1) : ℝ) ^ 2 + 1) ^ 3 = 45 / 8

/-- Corollary 4.10: `Σ_{n≥1} (4L_{6n+3} + 3L_{2n+1})/(L_{2n+1}² + 5)³ = 1/27` and
`Σ_{n≥1} (8F_{6n+3} - 3F_{2n+1})/(L_{2n+1}² - 5)³ = 13/64`.

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Corollary 4.10 (`fq-2024-linzhou02172024-cor-4.10`). -/
public theorem_wanted tsum_lucas_cube_odd_index :
    ∑' n : ℕ, (4 * (lucasNumber (6 * (n + 1) + 3) : ℝ) + 3 * (lucasNumber (2 * (n + 1) + 1) : ℝ)) /
        ((lucasNumber (2 * (n + 1) + 1) : ℝ) ^ 2 + 5) ^ 3 = 1 / 27 ∧
      ∑' n : ℕ, (8 * (Nat.fib (6 * (n + 1) + 3) : ℝ) - 3 * (Nat.fib (2 * (n + 1) + 1) : ℝ)) /
          ((lucasNumber (2 * (n + 1) + 1) : ℝ) ^ 2 - 5) ^ 3 = 13 / 64

/-- Theorem 1.1: for real `x > 0` and positive integers `k`, `m`,
`Σ_{n≥L} Σ_{j=0}^{m-1} C(2m, j)(-1)^{(k+1)j} f_{2k(m-j)} f_{4n(m-j)} / [f_{2n}² - (-1)^k f_k²]^{2m}
  = Δ^{2(m-1)} Σ_{r=1}^k 1/f_s^{2m}` (summation index shifted to start at `0`).

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Theorem 1.1 (`fq-2024-linzhou02172024-thm-1.1`). -/
public theorem_wanted tsum_fibPoly_even_pow_even_index {x : ℝ} (hx : 0 < x) {k m : ℕ}
    (hk : 0 < k) (hm : 0 < m) :
    ∑' n : ℕ, (∑ j ∈ Finset.range m, ((2 * m).choose j : ℝ) * (-1) ^ ((k + 1) * j) *
          aeval x (𝔣 (2 * k * (m - j))) * aeval x (𝔣 (4 * (n + 𝔏[k]) * (m - j)))) /
        (aeval x (𝔣 (2 * (n + 𝔏[k]))) ^ 2 - (-1) ^ k * aeval x (𝔣 k) ^ 2) ^ (2 * m) =
      (x ^ 2 + 4) ^ (m - 1) * ∑ r ∈ Finset.Icc 1 k, 1 / aeval x (𝔣 𝔰[k, r]) ^ (2 * m)

/-- Theorem 1.2: for real `x > 0` and positive integers `k`, `m`,
`Σ_{n≥L} Σ_{j=0}^{m-1} C(2m, j)(-1)^{kj} f_{2k(m-j)} f_{4n(m-j)} / [ℓ_{2n}² + (-1)^k Δ² f_k²]^{2m}
  = (1/Δ²) Σ_{r=1}^k 1/ℓ_s^{2m}` (summation index shifted to start at `0`).

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Theorem 1.2 (`fq-2024-linzhou02172024-thm-1.2`). -/
public theorem_wanted tsum_lucasPoly_even_pow_even_index {x : ℝ} (hx : 0 < x) {k m : ℕ}
    (hk : 0 < k) (hm : 0 < m) :
    ∑' n : ℕ, (∑ j ∈ Finset.range m, ((2 * m).choose j : ℝ) * (-1) ^ (k * j) *
          aeval x (𝔣 (2 * k * (m - j))) * aeval x (𝔣 (4 * (n + 𝔏[k]) * (m - j)))) /
        (aeval x (𝔩 (2 * (n + 𝔏[k]))) ^ 2 + (-1) ^ k * (x ^ 2 + 4) * aeval x (𝔣 k) ^ 2) ^ (2 * m) =
      1 / (x ^ 2 + 4) * ∑ r ∈ Finset.Icc 1 k, 1 / aeval x (𝔩 𝔰[k, r]) ^ (2 * m)

/-- Theorem 1.3: for real `x > 0` and positive integers `k`, `m`,
`Σ_{n≥M} Σ_{j=0}^{m-1} C(2m, j)(-1)^{kj} f_{2k(m-j)} f_{(4n+2)(m-j)} /
  [f_{2n+1}² + (-1)^k f_k²]^{2m} = Δ^{2(m-1)} Σ_{r=1}^k 1/f_t^{2m}`
(summation index shifted to start at `0`).

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Theorem 1.3 (`fq-2024-linzhou02172024-thm-1.3`). -/
public theorem_wanted tsum_fibPoly_even_pow_odd_index {x : ℝ} (hx : 0 < x) {k m : ℕ}
    (hk : 0 < k) (hm : 0 < m) :
    ∑' n : ℕ, (∑ j ∈ Finset.range m, ((2 * m).choose j : ℝ) * (-1) ^ (k * j) *
          aeval x (𝔣 (2 * k * (m - j))) * aeval x (𝔣 ((4 * (n + 𝔐[k]) + 2) * (m - j)))) /
        (aeval x (𝔣 (2 * (n + 𝔐[k]) + 1)) ^ 2 + (-1) ^ k * aeval x (𝔣 k) ^ 2) ^ (2 * m) =
      (x ^ 2 + 4) ^ (m - 1) * ∑ r ∈ Finset.Icc 1 k, 1 / aeval x (𝔣 𝔱[k, r]) ^ (2 * m)

/-- Theorem 1.4: for real `x > 0` and positive integers `k`, `m`,
`Σ_{n≥M} Σ_{j=0}^{m-1} C(2m, j)(-1)^{(k+1)j} f_{2k(m-j)} f_{(4n+2)(m-j)} /
  [ℓ_{2n+1}² - (-1)^k Δ² f_k²]^{2m} = (1/Δ²) Σ_{r=1}^k 1/ℓ_t^{2m}`
(summation index shifted to start at `0`).

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Theorem 1.4 (`fq-2024-linzhou02172024-thm-1.4`). -/
public theorem_wanted tsum_lucasPoly_even_pow_odd_index {x : ℝ} (hx : 0 < x) {k m : ℕ}
    (hk : 0 < k) (hm : 0 < m) :
    ∑' n : ℕ, (∑ j ∈ Finset.range m, ((2 * m).choose j : ℝ) * (-1) ^ ((k + 1) * j) *
          aeval x (𝔣 (2 * k * (m - j))) * aeval x (𝔣 ((4 * (n + 𝔐[k]) + 2) * (m - j)))) /
        (aeval x (𝔩 (2 * (n + 𝔐[k]) + 1)) ^ 2 - (-1) ^ k * (x ^ 2 + 4) * aeval x (𝔣 k) ^ 2) ^
          (2 * m) =
      1 / (x ^ 2 + 4) * ∑ r ∈ Finset.Icc 1 k, 1 / aeval x (𝔩 𝔱[k, r]) ^ (2 * m)

/-- Theorem 1.5: for real `x > 0`, a positive integer `k` and `m ∈ ℕ`,
`Σ_{n≥L} Σ_{j=0}^m C(2m+1, j) f_{2n(2m+1-2j)} ℓ_{k(2m+1-2j)} / (f_{2n}² + f_k²)^{2m+1}
  = Δ^{2m} Σ_{r=1}^k 1/f_{2r-1}^{2m+1}` if `k` is odd, and
`Σ_{n≥L} Σ_{j=0}^m C(2m+1, j)(-1)^j ℓ_{2n(2m+1-2j)} f_{k(2m+1-2j)} / (f_{2n}² - f_k²)^{2m+1}
  = Δ^{2m} Σ_{r=1}^k 1/f_{2r}^{2m+1}` if `k` is even (summation index shifted to start at `0`).

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Theorem 1.5 (`fq-2024-linzhou02172024-thm-1.5`). -/
public theorem_wanted tsum_fibPoly_odd_pow_even_index {x : ℝ} (hx : 0 < x) {k : ℕ}
    (hk : 0 < k) (m : ℕ) :
    (Odd k → ∑' n : ℕ, (∑ j ∈ Finset.range (m + 1), ((2 * m + 1).choose j : ℝ) *
          aeval x (𝔣 (2 * (n + 𝔏[k]) * (2 * m + 1 - 2 * j))) *
            aeval x (𝔩 (k * (2 * m + 1 - 2 * j)))) /
        (aeval x (𝔣 (2 * (n + 𝔏[k]))) ^ 2 + aeval x (𝔣 k) ^ 2) ^ (2 * m + 1) =
      (x ^ 2 + 4) ^ m * ∑ r ∈ Finset.Icc 1 k, 1 / aeval x (𝔣 (2 * r - 1)) ^ (2 * m + 1)) ∧
    (Even k → ∑' n : ℕ, (∑ j ∈ Finset.range (m + 1), ((2 * m + 1).choose j : ℝ) * (-1) ^ j *
          aeval x (𝔩 (2 * (n + 𝔏[k]) * (2 * m + 1 - 2 * j))) *
            aeval x (𝔣 (k * (2 * m + 1 - 2 * j)))) /
        (aeval x (𝔣 (2 * (n + 𝔏[k]))) ^ 2 - aeval x (𝔣 k) ^ 2) ^ (2 * m + 1) =
      (x ^ 2 + 4) ^ m * ∑ r ∈ Finset.Icc 1 k, 1 / aeval x (𝔣 (2 * r)) ^ (2 * m + 1))

/-- Theorem 1.6: for real `x > 0`, a positive integer `k` and `m ∈ ℕ`,
`Σ_{n≥L} Σ_{j=0}^m C(2m+1, j)(-1)^j ℓ_{2n(2m+1-2j)} ℓ_{k(2m+1-2j)} / (ℓ_{2n}² - Δ² f_k²)^{2m+1}
  = Σ_{r=1}^k 1/ℓ_{2r-1}^{2m+1}` if `k` is odd, and
`Σ_{n≥L} Σ_{j=0}^m C(2m+1, j) f_{2n(2m+1-2j)} f_{k(2m+1-2j)} / (ℓ_{2n}² + Δ² f_k²)^{2m+1}
  = (1/Δ²) Σ_{r=1}^k 1/ℓ_{2r}^{2m+1}` if `k` is even (summation index shifted to start at `0`).

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Theorem 1.6 (`fq-2024-linzhou02172024-thm-1.6`). -/
public theorem_wanted tsum_lucasPoly_odd_pow_even_index {x : ℝ} (hx : 0 < x) {k : ℕ}
    (hk : 0 < k) (m : ℕ) :
    (Odd k → ∑' n : ℕ, (∑ j ∈ Finset.range (m + 1), ((2 * m + 1).choose j : ℝ) * (-1) ^ j *
          aeval x (𝔩 (2 * (n + 𝔏[k]) * (2 * m + 1 - 2 * j))) *
            aeval x (𝔩 (k * (2 * m + 1 - 2 * j)))) /
        (aeval x (𝔩 (2 * (n + 𝔏[k]))) ^ 2 - (x ^ 2 + 4) * aeval x (𝔣 k) ^ 2) ^ (2 * m + 1) =
      ∑ r ∈ Finset.Icc 1 k, 1 / aeval x (𝔩 (2 * r - 1)) ^ (2 * m + 1)) ∧
    (Even k → ∑' n : ℕ, (∑ j ∈ Finset.range (m + 1), ((2 * m + 1).choose j : ℝ) *
          aeval x (𝔣 (2 * (n + 𝔏[k]) * (2 * m + 1 - 2 * j))) *
            aeval x (𝔣 (k * (2 * m + 1 - 2 * j)))) /
        (aeval x (𝔩 (2 * (n + 𝔏[k]))) ^ 2 + (x ^ 2 + 4) * aeval x (𝔣 k) ^ 2) ^ (2 * m + 1) =
      1 / (x ^ 2 + 4) * ∑ r ∈ Finset.Icc 1 k, 1 / aeval x (𝔩 (2 * r)) ^ (2 * m + 1))

/-- Theorem 1.7: for real `x > 0`, a positive integer `k` and `m ∈ ℕ`,
`Σ_{n≥M} Σ_{j=0}^m C(2m+1, j)(-1)^j f_{(2n+1)(2m+1-2j)} ℓ_{k(2m+1-2j)} / (f_{2n+1}² - f_k²)^{2m+1}
  = Δ^{2m} Σ_{r=1}^k 1/f_{2r}^{2m+1}` if `k` is odd, and
`Σ_{n≥M} Σ_{j=0}^m C(2m+1, j) ℓ_{(2n+1)(2m+1-2j)} f_{k(2m+1-2j)} / (f_{2n+1}² + f_k²)^{2m+1}
  = Δ^{2m} Σ_{r=1}^k 1/f_{2r-1}^{2m+1}` if `k` is even (summation index shifted to start at `0`).

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Theorem 1.7 (`fq-2024-linzhou02172024-thm-1.7`). -/
public theorem_wanted tsum_fibPoly_odd_pow_odd_index {x : ℝ} (hx : 0 < x) {k : ℕ}
    (hk : 0 < k) (m : ℕ) :
    (Odd k → ∑' n : ℕ, (∑ j ∈ Finset.range (m + 1), ((2 * m + 1).choose j : ℝ) * (-1) ^ j *
          aeval x (𝔣 ((2 * (n + 𝔐[k]) + 1) * (2 * m + 1 - 2 * j))) *
            aeval x (𝔩 (k * (2 * m + 1 - 2 * j)))) /
        (aeval x (𝔣 (2 * (n + 𝔐[k]) + 1)) ^ 2 - aeval x (𝔣 k) ^ 2) ^ (2 * m + 1) =
      (x ^ 2 + 4) ^ m * ∑ r ∈ Finset.Icc 1 k, 1 / aeval x (𝔣 (2 * r)) ^ (2 * m + 1)) ∧
    (Even k → ∑' n : ℕ, (∑ j ∈ Finset.range (m + 1), ((2 * m + 1).choose j : ℝ) *
          aeval x (𝔩 ((2 * (n + 𝔐[k]) + 1) * (2 * m + 1 - 2 * j))) *
            aeval x (𝔣 (k * (2 * m + 1 - 2 * j)))) /
        (aeval x (𝔣 (2 * (n + 𝔐[k]) + 1)) ^ 2 + aeval x (𝔣 k) ^ 2) ^ (2 * m + 1) =
      (x ^ 2 + 4) ^ m * ∑ r ∈ Finset.Icc 1 k, 1 / aeval x (𝔣 (2 * r - 1)) ^ (2 * m + 1))

/-- Theorem 1.8: for real `x > 0`, a positive integer `k` and `m ∈ ℕ`,
`Σ_{n≥M} Σ_{j=0}^m C(2m+1, j) ℓ_{(2n+1)(2m+1-2j)} ℓ_{k(2m+1-2j)} / (ℓ_{2n+1}² + Δ² f_k²)^{2m+1}
  = Σ_{r=1}^k 1/ℓ_{2r}^{2m+1}` if `k` is odd, and
`Σ_{n≥M} Σ_{j=0}^m C(2m+1, j)(-1)^j f_{(2n+1)(2m+1-2j)} f_{k(2m+1-2j)} /
  (ℓ_{2n+1}² - Δ² f_k²)^{2m+1} = (1/Δ²) Σ_{r=1}^k 1/ℓ_{2r-1}^{2m+1}` if `k` is even
(summation index shifted to start at `0`).

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Theorem 1.8 (`fq-2024-linzhou02172024-thm-1.8`). -/
public theorem_wanted tsum_lucasPoly_odd_pow_odd_index {x : ℝ} (hx : 0 < x) {k : ℕ}
    (hk : 0 < k) (m : ℕ) :
    (Odd k → ∑' n : ℕ, (∑ j ∈ Finset.range (m + 1), ((2 * m + 1).choose j : ℝ) *
          aeval x (𝔩 ((2 * (n + 𝔐[k]) + 1) * (2 * m + 1 - 2 * j))) *
            aeval x (𝔩 (k * (2 * m + 1 - 2 * j)))) /
        (aeval x (𝔩 (2 * (n + 𝔐[k]) + 1)) ^ 2 + (x ^ 2 + 4) * aeval x (𝔣 k) ^ 2) ^
          (2 * m + 1) =
      ∑ r ∈ Finset.Icc 1 k, 1 / aeval x (𝔩 (2 * r)) ^ (2 * m + 1)) ∧
    (Even k → ∑' n : ℕ, (∑ j ∈ Finset.range (m + 1), ((2 * m + 1).choose j : ℝ) * (-1) ^ j *
          aeval x (𝔣 ((2 * (n + 𝔐[k]) + 1) * (2 * m + 1 - 2 * j))) *
            aeval x (𝔣 (k * (2 * m + 1 - 2 * j)))) /
        (aeval x (𝔩 (2 * (n + 𝔐[k]) + 1)) ^ 2 - (x ^ 2 + 4) * aeval x (𝔣 k) ^ 2) ^ (2 * m + 1) =
      1 / (x ^ 2 + 4) * ∑ r ∈ Finset.Icc 1 k, 1 / aeval x (𝔩 (2 * r - 1)) ^ (2 * m + 1))

end

end MetaMathlibExt
