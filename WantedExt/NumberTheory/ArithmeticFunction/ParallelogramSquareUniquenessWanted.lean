/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# Parallelogram uniqueness of square numbers for multiplicative functions

Statement from Poo-Sung Park, *On the Parallelogram Uniqueness of Square Numbers for
Multiplicative Functions*, INTEGERS 24 (2024), Article A108. Multiplicative functions are
`ArithmeticFunction ℂ` with `IsMultiplicative`.
-/

namespace MetaMathlibExt

@[expose] public section

open ArithmeticFunction

/-- A multiplicative function with
`f (m² + n²) + f (m² - n²) = 2 f (m²) + 2 f (n²)` for all positive integers `m > n` and
`f 4 ≠ 0` is `f n = n²`.

Source: Poo-Sung Park, *On the Parallelogram Uniqueness of Square Numbers for Multiplicative
Functions*, INTEGERS 24 (2024), Article A108, Theorem 1 (`integers-2024-A108-thm-1`). -/
public theorem_wanted multiplicative_parallelogram_squares_eq_sq (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))
    (h4 : f 4 ≠ 0) :
    ∀ n : ℕ, f n = (n : ℂ) ^ 2

/-- Theorem 2: a multiplicative function with
`f (m² + n²) + f (m² - n²) = 2 f (m²) + 2 f (n²)` for all positive integers `m > n` and
`f 4 = 0` is one of two functions: (1) `f n = 0, 4, 1` for `n ≡ 0`, `2 (mod 4)`, otherwise;
(2) `f 2 = 4`, `f (2^r) = 0` for `r ≥ 2`, and `f (p^r) = (-1 / p)^r p^r` (Jacobi symbol) for
odd primes `p` and `r ≥ 1`.

Source: Poo-Sung Park, *On the Parallelogram Uniqueness of Square Numbers for Multiplicative
Functions*, INTEGERS 24 (2024), Article A108, Theorem 2 (`integers-2024-A108-thm-2`). -/
public theorem_wanted multiplicative_parallelogram_squares_of_f_four_eq_zero
    (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))
    (h4 : f 4 = 0) :
    (∀ n : ℕ, f n = if n % 4 = 0 then 0 else if n % 4 = 2 then 4 else 1) ∨
      (f 2 = 4 ∧ (∀ r : ℕ, 2 ≤ r → f (2 ^ r) = 0) ∧
        ∀ p r : ℕ, p.Prime → p ≠ 2 → 1 ≤ r →
          f (p ^ r) = ((jacobiSym (-1) p : ℤ) : ℂ) ^ r * (p : ℂ) ^ r)

/-- Theorem 3: for `f` multiplicative with `f (m² + n²) + f (m² - n²) = 2 f (m²) + 2 f (n²)`
(`m > n ≥ 1`), if `f 4 = 0` then `f (2^r) = 0` for `r ≥ 2`; otherwise `f (2^r) = 2^{2r}` for
`r ≥ 1`.

Source: Poo-Sung Park, *On the Parallelogram Uniqueness of Square Numbers for Multiplicative
Functions*, INTEGERS 24 (2024), Article A108, Theorem 3 (`integers-2024-A108-thm-3`). -/
public theorem_wanted parallelogram_multiplicative_two_pow (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2)) :
    (f 4 = 0 → ∀ r : ℕ, 2 ≤ r → f (2 ^ r) = 0) ∧
      (f 4 ≠ 0 → ∀ r : ℕ, 1 ≤ r → f (2 ^ r) = (2 : ℂ) ^ (2 * r))

/-- Lemma 1.
Setting: `f` is multiplicative with `f (m² + n²) + f (m² - n²) = 2 f (m²) + 2 f (n²)`
for `m > n ≥ 1`
(the setting of Theorems 1 and 2), and `f (q^s) = q^{2s}` for all primes `q < p`, `s ≥ 1`.
If `p` is odd and `f p = p²`, then `f (p² + 1) = (p² + 1)²`. (`p ≠ 2` is
added: for `p = 2` the solution `f n = 0, 4, 1` for `n ≡ 0`, `2 (mod 4)`, otherwise, of
Theorem 2 has `f 2 = 4` but `f 5 = 1`.)

Source: Poo-Sung Park, *On the Parallelogram Uniqueness of Square Numbers for Multiplicative
Functions*, INTEGERS 24 (2024), Article A108, Lemma 1 (`integers-2024-A108-lem-1`). -/
public theorem_wanted parallelogram_multiplicative_sq_add_one (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))
    {p : ℕ} (hp : p.Prime)
    (hind : ∀ q s : ℕ, q.Prime → q < p → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s))
    (hp2 : p ≠ 2) (hfp : f p = (p : ℂ) ^ 2) :
    f (p ^ 2 + 1) = ((p ^ 2 + 1 : ℕ) : ℂ) ^ 2

/-- Lemma 2.
Setting: `f` is multiplicative with `f (m² + n²) + f (m² - n²) = 2 f (m²) + 2 f (n²)`
for `m > n ≥ 1`
(the setting of Theorems 1 and 2), and `f (q^s) = q^{2s}` for all primes `q < p`, `s ≥ 1`.
If `p ≡ 3 (mod 4)`, then `f (p + 2) = (p + 2)²` and
`f ((p + 2)²) = (p + 2)⁴`.

Source: Poo-Sung Park, *On the Parallelogram Uniqueness of Square Numbers for Multiplicative
Functions*, INTEGERS 24 (2024), Article A108, Lemma 2 (`integers-2024-A108-lem-2`). -/
public theorem_wanted parallelogram_multiplicative_add_two (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))
    {p : ℕ} (hp : p.Prime)
    (hind : ∀ q s : ℕ, q.Prime → q < p → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s))
    (hp4 : p % 4 = 3) :
    f (p + 2) = ((p + 2 : ℕ) : ℂ) ^ 2 ∧ f ((p + 2) ^ 2) = ((p + 2 : ℕ) : ℂ) ^ 4

/-- Lemma 3.
Setting: `f` is multiplicative with `f (m² + n²) + f (m² - n²) = 2 f (m²) + 2 f (n²)`
for `m > n ≥ 1`
(the setting of Theorems 1 and 2), and `f (q^s) = q^{2s}` for all primes `q < p`, `s ≥ 1`.
If `p = 4k - 1`, then `f (k² + 1) = (k² + 1)²` and
`f (4k² + 1) = (4k² + 1)²`.

Source: Poo-Sung Park, *On the Parallelogram Uniqueness of Square Numbers for Multiplicative
Functions*, INTEGERS 24 (2024), Article A108, Lemma 3 (`integers-2024-A108-lem-3`). -/
public theorem_wanted parallelogram_multiplicative_k_sq_add_one (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))
    {p : ℕ} (hp : p.Prime)
    (hind : ∀ q s : ℕ, q.Prime → q < p → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s))
    {k : ℕ} (hpk : p = 4 * k - 1) :
    f (k ^ 2 + 1) = ((k ^ 2 + 1 : ℕ) : ℂ) ^ 2 ∧ f (4 * k ^ 2 + 1) = ((4 * k ^ 2 + 1 : ℕ) : ℂ) ^ 2

/-- Lemma 4.
Setting: `f` is multiplicative with `f (m² + n²) + f (m² - n²) = 2 f (m²) + 2 f (n²)`
for `m > n ≥ 1`
(the setting of Theorems 1 and 2), and `f (q^s) = q^{2s}` for all primes `q < p`, `s ≥ 1`.
If `p = 4k - 1 ≥ 19` and `4 ∤ k`, then `f (5k + 3) = (5k + 3)²`.

Source: Poo-Sung Park, *On the Parallelogram Uniqueness of Square Numbers for Multiplicative
Functions*, INTEGERS 24 (2024), Article A108, Lemma 4 (`integers-2024-A108-lem-4`). -/
public theorem_wanted parallelogram_multiplicative_five_k_add_three (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))
    {p : ℕ} (hp : p.Prime)
    (hind : ∀ q s : ℕ, q.Prime → q < p → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s))
    {k : ℕ} (hpk : p = 4 * k - 1) (h19 : 19 ≤ p) (hk : ¬ 4 ∣ k) :
    f (5 * k + 3) = ((5 * k + 3 : ℕ) : ℂ) ^ 2

/-- Lemma 5.
Setting: `f` is multiplicative with `f (m² + n²) + f (m² - n²) = 2 f (m²) + 2 f (n²)`
for `m > n ≥ 1`
(the setting of Theorems 1 and 2), and `f (q^s) = q^{2s}` for all primes `q < p`, `s ≥ 1`.
If `p = 4k - 1 ≥ 19` and `k ≢ 3 (mod 4)`, then `f (6k + 1) = (6k + 1)²`.

Source: Poo-Sung Park, *On the Parallelogram Uniqueness of Square Numbers for Multiplicative
Functions*, INTEGERS 24 (2024), Article A108, Lemma 5 (`integers-2024-A108-lem-5`). -/
public theorem_wanted parallelogram_multiplicative_six_k_add_one (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))
    {p : ℕ} (hp : p.Prime)
    (hind : ∀ q s : ℕ, q.Prime → q < p → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s))
    {k : ℕ} (hpk : p = 4 * k - 1) (h19 : 19 ≤ p) (hk : k % 4 ≠ 3) :
    f (6 * k + 1) = ((6 * k + 1 : ℕ) : ℂ) ^ 2

/-- Theorem 4.
Setting: `f` is multiplicative with `f (m² + n²) + f (m² - n²) = 2 f (m²) + 2 f (n²)`
for `m > n ≥ 1`
(the setting of Theorems 1 and 2), and `f (q^s) = q^{2s}` for all primes `q < p`, `s ≥ 1`.
If `p` is odd and `f p = p²`, then `f (p^r) = p^{2r}` for `r ≥ 2`.
(`p ≠ 2` is added: for `p = 2` the solution `f n = 0, 4, 1` for `n ≡ 0`, `2 (mod 4)`,
otherwise, of Theorem 2 has `f 2 = 4` but `f 4 = 0`.)

Source: Poo-Sung Park, *On the Parallelogram Uniqueness of Square Numbers for Multiplicative
Functions*, INTEGERS 24 (2024), Article A108, Theorem 4 (`integers-2024-A108-thm-4`). -/
public theorem_wanted parallelogram_multiplicative_prime_pow (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))
    {p : ℕ} (hp : p.Prime)
    (hind : ∀ q s : ℕ, q.Prime → q < p → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s))
    (hp2 : p ≠ 2) (hfp : f p = (p : ℂ) ^ 2) :
    ∀ r : ℕ, 2 ≤ r → f (p ^ r) = (p : ℂ) ^ (2 * r)

/-- Theorem 5.
Setting: `f` is multiplicative with `f (m² + n²) + f (m² - n²) = 2 f (m²) + 2 f (n²)`
for `m > n ≥ 1`
(the setting of Theorems 1 and 2), and `f (q^s) = q^{2s}` for all primes `q < p`, `s ≥ 1`.
If `p ≡ 1 (mod 4)`, then `f p = p²`.

Source: Poo-Sung Park, *On the Parallelogram Uniqueness of Square Numbers for Multiplicative
Functions*, INTEGERS 24 (2024), Article A108, Theorem 5 (`integers-2024-A108-thm-5`). -/
public theorem_wanted parallelogram_multiplicative_prime_one_mod_four (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))
    {p : ℕ} (hp : p.Prime)
    (hind : ∀ q s : ℕ, q.Prime → q < p → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s))
    (hp4 : p % 4 = 1) :
    f p = (p : ℂ) ^ 2

/-- Theorem 6.
Setting: `f` is multiplicative with `f (m² + n²) + f (m² - n²) = 2 f (m²) + 2 f (n²)`
for `m > n ≥ 1`
(the setting of Theorems 1 and 2), and `f (q^s) = q^{2s}` for all primes `q < p`, `s ≥ 1`.
If `p = 4k - 1 ≥ 19`, then `f p = p²`.

Source: Poo-Sung Park, *On the Parallelogram Uniqueness of Square Numbers for Multiplicative
Functions*, INTEGERS 24 (2024), Article A108, Theorem 6 (`integers-2024-A108-thm-6`). -/
public theorem_wanted parallelogram_multiplicative_prime_three_mod_four (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))
    {p : ℕ} (hp : p.Prime)
    (hind : ∀ q s : ℕ, q.Prime → q < p → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s))
    {k : ℕ} (hpk : p = 4 * k - 1) (h19 : 19 ≤ p) :
    f p = (p : ℂ) ^ 2

end

end MetaMathlibExt
