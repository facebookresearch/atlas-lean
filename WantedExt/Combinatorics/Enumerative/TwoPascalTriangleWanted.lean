/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Substitution
public import MathlibExt.NumberTheory.LucasSequence
public import MathlibExt.NumberTheory.TribonacciSequenceWithInitialValues001
public import MathlibExt.NumberTheory.TrinomialCoefficient

/-!
# The 2-Pascal triangle (Otmani)

Statements from Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*,
Journal of Integer Sequences 28 (2025), Article 25.3.5.

The paper's 2-binomial coefficient `binom(n, k)_2` (the entries of the 2-Pascal triangle) is
the coefficient of `X^k` in `(1 + X + X^2)^n`, i.e. `MetaMathlibExt.trinomialCoefficient n k`;
the record of Theorem 3 identifies it through its extraction formula, formalized below as
`trinomialCoefficient_eq_coeff`. Where the paper lets an integer lower index be negative,
the coefficient is `0`; statements spell this out with an `if`.
-/

open PowerSeries

namespace MetaMathlibExt

@[expose] public section

/-- **Theorem 1** (Sprugnoli, fundamental theorem of Riordan arrays). For the Riordan
array `d_{n,k} = [t^n] d(t) h(t)^k` with `h(0) = 0` and any series `f`,
`∑_{k=0}^{n} d_{n,k} f_k = [t^n] d(t) f(h(t))`.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 1 (`jis-2025-25.3.5-thm-1`). -/
public theorem_wanted riordan_array_sum_eq_coeff_subst {R : Type*} [CommRing R]
    (d h f : PowerSeries R) (hh : constantCoeff h = 0) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), coeff n (d * h ^ k) * coeff k f = coeff n (d * f.subst h)

/-- **Theorem 3.** `binom(n, k)_2 = [t^{2n}] (1 - t + t^2)^n (1 - t)⁻¹ (t / (1 - t))^k`,
for `k ∈ ℕ` (the record allows `k ∈ ℤ`; negative `k` is omitted).

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 3 (`jis-2025-25.3.5-thm-3`). -/
public theorem_wanted trinomialCoefficient_eq_coeff (n k : ℕ) :
    (trinomialCoefficient n k : ℚ) =
      coeff (2 * n) ((1 - X + X ^ 2) ^ n * (1 - X)⁻¹ * (X * (1 - X)⁻¹) ^ k)

/-- **Theorem 9.** For `0 ≤ x < b` and `z ≠ 0`, with `w_b = exp(2πi/b)`,
`∑_{k=0}^{⌊(2n-x)/b⌋} binom(n, x+bk)_2 z^{x+bk} = z^n (1/b) ∑_{j=1}^{b} w_b^{j(n-x)} (1 + z w_b^j + (z w_b^j)⁻¹)^n`.
The hypothesis `z ≠ 0` is implicit in the paper's `(z w_b^j)⁻¹`.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 9 (`jis-2025-25.3.5-thm-9`). -/
public theorem_wanted sum_trinomialCoefficient_arith_prog (n x b : ℕ) (hxb : x < b) (z : ℂ)
    (hz : z ≠ 0) :
    let w := Complex.exp (2 * Real.pi * Complex.I / b)
    ∑ k ∈ Finset.range ((2 * n - x) / b + 1), (trinomialCoefficient n (x + b * k) : ℂ) *
        z ^ (x + b * k) =
      z ^ n * (1 / b) * ∑ j ∈ Finset.Icc 1 b,
        w ^ ((j : ℤ) * ((n : ℤ) - x)) * (1 + z * w ^ j + (z * w ^ j)⁻¹) ^ n

/-- **Corollary 10.** Alternating sums of `binom(n, 3k+x)_2` and `binom(n, 5k+x)_2`, with
`L_n` the Lucas numbers. The residue `x` is restricted to `x < 3`, resp. `x < 5` (the record
leaves `x` unbounded), and the case `n ≡ x ± 2 (mod 5)` assumes `n ≥ 1` (at `n = 0` it
needs `L_{-1}`).

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Corollary 10 (`jis-2025-25.3.5-cor-10`). -/
public theorem_wanted trinomialCoefficient_alternating_sums_mod_three_five (n x : ℕ) :
    (x < 3 →
      3 * ∑ k ∈ Finset.range (2 * n + 1),
          (trinomialCoefficient n (3 * k + x) : ℤ) * (-1) ^ (k + x) =
        if n ≡ x [MOD 3] then (-1) ^ n * 2 ^ (n + 1) + 1 else (-1) ^ (n + 1) * 2 ^ n + 1) ∧
    (x < 5 →
      let S := 5 * ∑ k ∈ Finset.range (2 * n + 1),
          (trinomialCoefficient n (5 * k + x) : ℤ) * (-1) ^ (k + x)
      (n ≡ x [MOD 5] → S = 2 * (-1) ^ n * lucasNumber (2 * n) + 1) ∧
        (n ≡ x + 1 [MOD 5] ∨ x ≡ n + 1 [MOD 5] → S = (-1) ^ (n + 1) * lucasNumber (2 * n + 1) + 1) ∧
        (1 ≤ n → n ≡ x + 2 [MOD 5] ∨ x ≡ n + 2 [MOD 5] →
          S = (-1) ^ n * lucasNumber (2 * n - 1) + 1))

/-- **Corollary 11.** For even `b` and `x < b`,
`∑_{k≥0} binom(n, x+bk)_2 (-1)^k = (1/b) ∑_{j=1}^{b} cos(π(n-x)(1+2j)/b) (1 + 2cos(π(2j+1)/b))^n`.
The hypothesis `x < b` (from Theorem 9) is added: for `n = 3`, `b = x = 2` the left side is
`1` and the right side is `0`.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Corollary 11 (`jis-2025-25.3.5-cor-11`). -/
public theorem_wanted sum_trinomialCoefficient_arith_prog_alternating (n x b : ℕ)
    (hb : Even b) (hxb : x < b) :
    ∑ k ∈ Finset.range (2 * n + 1), (trinomialCoefficient n (x + b * k) : ℝ) * (-1) ^ k =
      1 / b * ∑ j ∈ Finset.Icc 1 b,
        Real.cos (Real.pi * ((n : ℝ) - x) * (1 + 2 * j) / b) *
          (1 + 2 * Real.cos (Real.pi * (2 * j + 1) / b)) ^ n

/-- **Corollary 13.** `∑_{k≥0} binom(n, 2k)_2 z^k = ((1 + √z + z)^n + (1 - √z + z)^n)/2`,
stated for complex `z` and any `s` with `s^2 = z` in place of the indeterminate `z` and `√z`.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Corollary 13 (`jis-2025-25.3.5-cor-13`). -/
public theorem_wanted sum_trinomialCoefficient_even (n : ℕ) (z s : ℂ) (hs : s ^ 2 = z) :
    ∑ k ∈ Finset.range (n + 1), (trinomialCoefficient n (2 * k) : ℂ) * z ^ k =
      ((1 + s + z) ^ n + (1 - s + z) ^ n) / 2

/-- **Corollary 15.** `q_n(z) = ∑_{k≥0} binom(n, 2k+1)_2 z^k = ((1 + √z + z)^n - (1 - √z + z)^n)/(2√z)`,
stated for complex `z` and any `s ≠ 0` with `s^2 = z`.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Corollary 15 (`jis-2025-25.3.5-cor-15`). -/
public theorem_wanted sum_trinomialCoefficient_odd (n : ℕ) (z s : ℂ) (hs : s ^ 2 = z)
    (hs0 : s ≠ 0) :
    ∑ k ∈ Finset.range (n + 1), (trinomialCoefficient n (2 * k + 1) : ℂ) * z ^ k =
      ((1 + s + z) ^ n - (1 - s + z) ^ n) / (2 * s)

/-- **Theorem 16.** `∑_{k=m}^{2n} binom(n, k)_2 binom(k, m) (-1)^k = binom(n, m)_2`.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 16 (`jis-2025-25.3.5-thm-16`). -/
public theorem_wanted sum_trinomialCoefficient_mul_choose_alternating (n m : ℕ) :
    ∑ k ∈ Finset.Icc m (2 * n), (trinomialCoefficient n k : ℤ) * k.choose m * (-1) ^ k =
      (trinomialCoefficient n m : ℤ)

/-- **Theorem 17.** `∑_{k=0}^{m} binom(n, k)_2 binom(m, k) = ∑_{k=0}^{2n} binom(n, k)_2 binom(m+k, k) (-1)^k`.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 17 (`jis-2025-25.3.5-thm-17`). -/
public theorem_wanted sum_trinomialCoefficient_mul_choose_eq (n m : ℕ) :
    ∑ k ∈ Finset.range (m + 1), (trinomialCoefficient n k : ℤ) * m.choose k =
      ∑ k ∈ Finset.range (2 * n + 1),
        (trinomialCoefficient n k : ℤ) * (m + k).choose k * (-1) ^ k

/-- **Theorem 18.** For `n ≤ m`, `∑_{k=0}^{n} binom(n-k, m)_2 binom(n, k) (-1)^k = binom(n, m-n)`.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 18 (`jis-2025-25.3.5-thm-18`). -/
public theorem_wanted sum_trinomialCoefficient_sub_mul_choose (n m : ℕ) (h : n ≤ m) :
    ∑ k ∈ Finset.range (n + 1), (trinomialCoefficient (n - k) m : ℤ) * n.choose k * (-1) ^ k =
      (n.choose (m - n) : ℤ)

/-- **Theorem 19.** `∑_{k=0}^{n} binom(2n-2k, n)_2 binom(n, k) (-1)^k = 2^n`.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 19 (`jis-2025-25.3.5-thm-19`). -/
public theorem_wanted sum_trinomialCoefficient_two_mul_sub (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (trinomialCoefficient (2 * n - 2 * k) n : ℤ) * n.choose k * (-1) ^ k = 2 ^ n

/-- **Theorem 20** (Vandermonde-type convolution). For `l ∈ ℤ`,
`∑_{k=0}^{2m} binom(n, l+k)_2 binom(m, k)_2 = binom(n+m, 2m+l)_2`, a negative lower index
giving `0`.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 20 (`jis-2025-25.3.5-thm-20`). -/
public theorem_wanted sum_trinomialCoefficient_convolution (n m : ℕ) (l : ℤ) :
    ∑ k ∈ Finset.range (2 * m + 1),
        (if 0 ≤ l + k then trinomialCoefficient n (l + k).toNat else 0) *
          trinomialCoefficient m k =
      if 0 ≤ 2 * m + l then trinomialCoefficient (n + m) (2 * m + l).toNat else 0

/-- **Theorem 24.** `∑_{k=0}^{2n} binom(n, k)_2^2 (-1)^k = binom(n, n)_2`.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 24 (`jis-2025-25.3.5-thm-24`). -/
public theorem_wanted sum_trinomialCoefficient_sq_alternating (n : ℕ) :
    ∑ k ∈ Finset.range (2 * n + 1), (trinomialCoefficient n k : ℤ) ^ 2 * (-1) ^ k =
      (trinomialCoefficient n n : ℤ)

/-- **Theorem 26.** `∑_{k=0}^{n} binom(n, 2k)_2^2 = binom(2n, 2n)_2/2 + binom(n, n)_2/2` and
`∑_{k=0}^{⌊n/2⌋} binom(n, n-2k)_2 binom(n, 2k)_2 = binom(2n, n)_2/2 + binom(n, n/2)_2/2`,
where `binom(n, n/2)_2` is read as `0` for odd `n` (the floor reading fails, e.g. at
`n = 1`: left side `1`, `binom(2, 1)_2/2 + binom(1, 0)_2/2 = 3/2`).

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 26 (`jis-2025-25.3.5-thm-26`). -/
public theorem_wanted sum_trinomialCoefficient_even_sq (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (trinomialCoefficient n (2 * k) : ℚ) ^ 2 =
        (trinomialCoefficient (2 * n) (2 * n) : ℚ) / 2 + (trinomialCoefficient n n : ℚ) / 2 ∧
      ∑ k ∈ Finset.range (n / 2 + 1),
          (trinomialCoefficient n (n - 2 * k) : ℚ) * trinomialCoefficient n (2 * k) =
        (trinomialCoefficient (2 * n) n : ℚ) / 2 +
          (if Even n then (trinomialCoefficient n (n / 2) : ℚ) else 0) / 2

/-- **Lemma 31.** For `n > 0`, `(k/n) binom(n, k)_2 = binom(n-1, k-1)_2 + 2 binom(n-1, k-2)_2`,
negative lower indices giving `0`.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Lemma 31 (`jis-2025-25.3.5-lem-31`). -/
public theorem_wanted trinomialCoefficient_absorption (n k : ℕ) (hn : 0 < n) :
    (k : ℚ) / n * trinomialCoefficient n k =
      (if 1 ≤ k then (trinomialCoefficient (n - 1) (k - 1) : ℚ) else 0) +
        2 * (if 2 ≤ k then (trinomialCoefficient (n - 1) (k - 2) : ℚ) else 0)

/-- **Theorem 32.** For `n > 0` and any series `f`,
`∑_{k=0}^{⌊2n/3⌋} binom(n-k, k)_2 (n/(n-k)) f_k = [t^{2n}] (1-t+t^2)^{n-1}(3-4t+2t^2)/(1-t) · f(t^3/((1-t+t^2)(1-t)))`.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 32 (`jis-2025-25.3.5-thm-32`). -/
public theorem_wanted sum_trinomialCoefficient_diagonal_weighted (n : ℕ) (hn : 0 < n)
    (f : PowerSeries ℚ) :
    ∑ k ∈ Finset.range (2 * n / 3 + 1),
        (trinomialCoefficient (n - k) k : ℚ) * n / (n - k : ℕ) * coeff k f =
      coeff (2 * n) ((1 - X + X ^ 2) ^ (n - 1) * (3 - 4 * X + 2 * X ^ 2) * (1 - X)⁻¹ *
        f.subst (X ^ 3 * ((1 - X + X ^ 2) * (1 - X))⁻¹))

/-- **Corollary 35.** For `n > 0`, `∑_{k=0}^{⌊2n/3⌋} binom(n-k, k)_2 (n/(n-k)) (-1)^k` is
`1` for `n ≡ ±1`, `-1` for `n ≡ 2`, and `3` for `n ≡ 0 (mod 4)`.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Corollary 35 (`jis-2025-25.3.5-cor-35`). -/
public theorem_wanted sum_trinomialCoefficient_diagonal_alternating (n : ℕ) (hn : 0 < n) :
    let S := ∑ k ∈ Finset.range (2 * n / 3 + 1),
      (trinomialCoefficient (n - k) k : ℚ) * n / (n - k : ℕ) * (-1) ^ k
    (n % 4 = 1 ∨ n % 4 = 3 → S = 1) ∧ (n % 4 = 2 → S = -1) ∧ (n % 4 = 0 → S = 3)

/-- **Corollary 40.** For complex `w`,
`∑_{k=0}^{n} binom(n, n-k)_2 w^{n+k} = (1+w+w^2)^n/2 + binom(n, n)_2 w^n/2 + ((w^2-1)/2) ∑_{k=0}^{n-1} binom(k, k)_2 (1+w+w^2)^{n-1-k} w^k`.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Corollary 40 (`jis-2025-25.3.5-cor-40`). -/
public theorem_wanted sum_trinomialCoefficient_upper_half (n : ℕ) (w : ℂ) :
    ∑ k ∈ Finset.range (n + 1), (trinomialCoefficient n (n - k) : ℂ) * w ^ (n + k) =
      (1 + w + w ^ 2) ^ n / 2 + (trinomialCoefficient n n : ℂ) * w ^ n / 2 +
        (w ^ 2 - 1) / 2 * ∑ k ∈ Finset.range n,
          (trinomialCoefficient k k : ℂ) * (1 + w + w ^ 2) ^ (n - 1 - k) * w ^ k


/-- **Theorem 38.** For `b ≥ 2a`, `binom(n + ak, n + bk)_2 = [t^n] S⁻¹ ((1 - t - S)^{b-a} / (2^{b-a} t^b))^k`,
where `S = √(1 - 2t - 3t^2)` is the square root with constant term `1`; the factor `t^{-bk}`
is moved into the coefficient index and `2^{(b-a)k}` to the left side. Stated for natural
`a, b, k` (the record has integers `a, b` and leaves `k` free).

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 38 (`jis-2025-25.3.5-thm-38`). -/
public theorem_wanted trinomialCoefficient_eq_coeff_sqrt (n a b k : ℕ) (hab : 2 * a ≤ b)
    (S : PowerSeries ℚ) (hS : S ^ 2 = 1 - 2 * X - 3 * X ^ 2) (hS0 : constantCoeff S = 1) :
    2 ^ ((b - a) * k) * (trinomialCoefficient (n + a * k) (n + b * k) : ℚ) =
      coeff (n + b * k) (S⁻¹ * (1 - X - S) ^ ((b - a) * k))

/-- **Theorem 47** (inverse of an implicit Riordan array sum). Let `ψ(0) ≠ 0` and
`h = t g(t)` with `g(0) = h'(0) ≠ 0`. If `a_m = [t^m] f(t) ψ(t)^m b(h(t))` for all `m`, then
`b_n = ∑_{k=0}^{n} ([t^{n-k}] (ψ - tψ') h' / (f ψ^{k+1}) · t^{n+1} / h^{n+1}) a_k`. The
hypothesis `f(0) ≠ 0`, needed for `1 / f`, is added; `t^{n+1} / h^{n+1}` is written
`(g⁻¹)^{n+1}`.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 47 (`jis-2025-25.3.5-thm-47`). -/
public theorem_wanted implicit_riordan_sum_inverse {K : Type*} [Field K]
    (f ψ g b : PowerSeries K) (hf : constantCoeff f ≠ 0) (hψ : constantCoeff ψ ≠ 0)
    (hg : constantCoeff g ≠ 0) (n : ℕ) :
    let h := X * g
    let a : ℕ → K := fun m => coeff m (f * ψ ^ m * b.subst h)
    coeff n b = ∑ k ∈ Finset.range (n + 1),
      coeff (n - k) ((ψ - X * derivative ψ) * derivative h * (f * ψ ^ (k + 1))⁻¹ *
        g⁻¹ ^ (n + 1)) * a k


/-- **Theorem 2** (Sprugnoli). For `a < b`,
`∑_k binom(n+ak, x+bk) f_k = [t^n] t^x (1-t)^{-(x+1)} f(t^{b-a} (1-t)^{-b})`; and for
`b = -c < 0`, complex `y` and integer `a'`,
`∑_k binom(y+a'k, m-ck) f_k = [t^m] (1+t)^y f(t^c (1+t)^{a'})`, where `(1+t)^u` is the binomial
series `∑_j binom(u, j) t^j`. The first identity is stated for natural `x` and `a` (the record
allows integers); in both, `k` runs over the indices with a nonnegative lower index
(`k ≤ n`, resp. `k ≤ m/c`), all other terms being `0` by the paper's convention.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 2 (`jis-2025-25.3.5-thm-2`). -/
public theorem_wanted sum_choose_mul_coeff_eq_coeff_subst (n x a b m c : ℕ) (hab : a < b)
    (hc : 0 < c) (y : ℂ) (a' : ℤ) (f : PowerSeries ℂ) :
    ∑ k ∈ Finset.range (n + 1), ((n + a * k).choose (x + b * k) : ℂ) * coeff k f =
        coeff n (X ^ x * ((1 - X) ^ (x + 1))⁻¹ * f.subst (X ^ (b - a) * ((1 - X) ^ b)⁻¹)) ∧
      ∑ k ∈ Finset.range (m / c + 1), Ring.choose (y + a' * k) (m - c * k) * coeff k f =
        coeff m (PowerSeries.binomialSeries ℂ y *
          f.subst (X ^ c * PowerSeries.binomialSeries ℂ (a' : ℂ)))

/-- **Theorem 6.** `binom(n, k)_2 = [t^{2n}] α(t) β(t)^k`, where
`β = t (t + √(4 - 3t^2)) / (2 (1 - t^2))` and
`α = -2 (2√(2 - t^2 - t√(4-3t^2)) + t^2 √(8-6t^2) - t√2) /
(√(2 - t^2 - t√(4-3t^2)) (3t^4 + 2t√(4-3t^2) - t^2 - 4))`.
The square roots are the power series `S` with `S^2 = 4 - 3t^2`, `S(0) = 2`, and `√2 · Q`
with `2 Q^2 = 2 - t^2 - t S`, `Q(0) = 1`; using `√(8 - 6t^2) = √2 · S`, the factors `√2`
cancel and `α = -2 (2Q + t^2 S - t) / (Q (3t^4 + 2tS - t^2 - 4))` has rational coefficients.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 6 (`jis-2025-25.3.5-thm-6`). -/
public theorem_wanted trinomialCoefficient_eq_coeff_alpha_mul_beta_pow (S Q : PowerSeries ℚ)
    (hS : S ^ 2 = 4 - 3 * X ^ 2) (hS0 : constantCoeff S = 2)
    (hQ : 2 * Q ^ 2 = 2 - X ^ 2 - X * S) (hQ0 : constantCoeff Q = 1) (n k : ℕ) :
    let α := -2 * (2 * Q + X ^ 2 * S - X) * (Q * (3 * X ^ 4 + 2 * X * S - X ^ 2 - 4))⁻¹
    let β := X * (X + S) * (2 * (1 - X ^ 2))⁻¹
    (trinomialCoefficient n k : ℚ) = coeff (2 * n) (α * β ^ k)

/-- **Theorem 7.** For `2a < b`,
`∑_k binom(n+ak, x+bk)_2 z^{2n-x+(2a-b)k} f_k =
[t^{2n}] (1-zt+(zt)^2)^n t^x (1-zt)^{-(x+1)} f(t^{b-2a} (1-zt+(zt)^2)^a (1-zt)^{-b})`;
and for `b = -c < 0`, complex `y` and integer `a'`,
`∑_k binom(y+a'k, m-ck)_2 z^{m-ck} f_k = [t^m] (1+zt+(zt)^2)^y f(t^c (1+zt+(zt)^2)^{a'})`.
Here `binom(u, j)_2 = [t^j](1+t+t^2)^u` (Comtet's extension, the paper's Eq. (8)) and
`(1+zt+(zt)^2)^u` is the binomial series of `u` evaluated at `zt + (zt)^2`. The first identity
is stated for natural `x`, `a` (the record allows integers), with `k ≤ 2n`; the exponent
`2n - x + (2a-b)k` is written `2(n+ak) - (x+bk)` in `ℕ`, exact on every nonzero term.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 7 (`jis-2025-25.3.5-thm-7`). -/
public theorem_wanted sum_trinomialCoefficient_mul_coeff_eq_coeff_subst (n x a b m c : ℕ)
    (hab : 2 * a < b) (hc : 0 < c) (y z : ℂ) (a' : ℤ) (f : PowerSeries ℂ) :
    let E : ℂ → ℕ → ℂ := fun u j =>
      coeff j ((PowerSeries.binomialSeries ℂ u).subst (X + X ^ 2 : PowerSeries ℂ))
    let P : ℂ → PowerSeries ℂ := fun u =>
      (PowerSeries.binomialSeries ℂ u).subst (C z * X + C z ^ 2 * X ^ 2)
    ∑ k ∈ Finset.range (2 * n + 1), (trinomialCoefficient (n + a * k) (x + b * k) : ℂ) *
          z ^ (2 * (n + a * k) - (x + b * k)) * coeff k f =
        coeff (2 * n) ((1 - C z * X + C z ^ 2 * X ^ 2) ^ n * X ^ x *
          ((1 - C z * X) ^ (x + 1))⁻¹ * f.subst (X ^ (b - 2 * a) *
            (1 - C z * X + C z ^ 2 * X ^ 2) ^ a * ((1 - C z * X) ^ b)⁻¹)) ∧
      ∑ k ∈ Finset.range (m / c + 1), E (y + a' * k) (m - c * k) * z ^ (m - c * k) * coeff k f =
        coeff m (P y * f.subst (X ^ c * P a'))

/-- **Theorem 21**, the true parts. For complex `x`, `y`:
`∑_{k ≤ n/3} binom(x, k) binom(y-3x, n-3k) = ∑_{k=0}^{n} binom(x, k) binom(y-2k, n-k) (-3)^k`
and `∑_{k ≤ n/3} binom(-x, n-3k)_2 binom(x, k) (-1)^k = (-1)^n binom(x, n)`, with
`binom(u, j)_2 = [t^j](1+t+t^2)^u` (Comtet's extension, Eq. (8)). The first expression of
Eq. (25), `∑_k binom(2x, n-k)_2 binom(y-2x, k) (-1)^{n-k}`, is omitted: it is false as
printed (`x = 2`, `y = 1/3`, `n = 1`: it is `-23/3`, the other two are `-17/3`).

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 21 (`jis-2025-25.3.5-thm-21`). -/
public theorem_wanted sum_choose_gould_and_extended_trinomial (x y : ℂ) (n : ℕ) :
    let E : ℂ → ℕ → ℂ := fun u j =>
      coeff j ((PowerSeries.binomialSeries ℂ u).subst (X + X ^ 2 : PowerSeries ℂ))
    ∑ k ∈ Finset.range (n / 3 + 1), Ring.choose x k * Ring.choose (y - 3 * x) (n - 3 * k) =
        ∑ k ∈ Finset.range (n + 1),
          Ring.choose x k * Ring.choose (y - 2 * k) (n - k) * (-3) ^ k ∧
      ∑ k ∈ Finset.range (n / 3 + 1), E (-x) (n - 3 * k) * Ring.choose x k * (-1) ^ k =
        (-1) ^ n * Ring.choose x n

/-- **Theorem 23.** For complex `x`,
`∑_{k=0}^{n} binom(2n-x, n-k)_2 binom(x, k)_2 (-1)^k = ∑_{k ≤ n/2} binom(2n-2x, n-2k)_2 binom(x, k)_2`,
with `binom(u, j)_2 = [t^j](1+t+t^2)^u` (Comtet's extension, Eq. (8)).

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 23 (`jis-2025-25.3.5-thm-23`). -/
public theorem_wanted sum_extended_trinomial_alternating_eq (x : ℂ) (n : ℕ) :
    let E : ℂ → ℕ → ℂ := fun u j =>
      coeff j ((PowerSeries.binomialSeries ℂ u).subst (X + X ^ 2 : PowerSeries ℂ))
    ∑ k ∈ Finset.range (n + 1), E (2 * n - x) (n - k) * E x k * (-1) ^ k =
      ∑ k ∈ Finset.range (n / 2 + 1), E (2 * n - 2 * x) (n - 2 * k) * E x k

/-- **Theorem 27.** `T_{n+2} = y_{3(n+1)} / 2^{n+1}`, with `T` the Tribonacci numbers
(`T_0 = T_1 = 0`, `T_2 = 1`) and `y` the sequence A077943,
`y_n = 2y_{n-1} - 2y_{n-2} + 2y_{n-3}`, `y_0 = y_1 = 0`, `y_2 = 1` (given by its recurrence).

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 27 (`jis-2025-25.3.5-thm-27`). -/
public theorem_wanted two_pow_mul_tribonacci_eq (y : ℕ → ℤ) (hy0 : y 0 = 0) (hy1 : y 1 = 0)
    (hy2 : y 2 = 1) (hy : ∀ n, y (n + 3) = 2 * y (n + 2) - 2 * y (n + 1) + 2 * y n) (n : ℕ) :
    2 ^ (n + 1) * (tribonacci (n + 2) : ℤ) = y (3 * (n + 1))

/-- **Theorem 28.** Let `r₁, r₂, r₃` be the zeros of `t^3 - 2wt^2 + 2w^2 t - (z + w^3)`,
assumed distinct. Then
`∑_{k ≤ 2n/3} binom(n-k, k)_2 w^{2n-3k} z^k = ∑_i (w^2 - w r_i + r_i^2)^{n+1} / ∏_{j ≠ i} (r_i - r_j)`.
The paper names the zeros `α_{z,w}, β_{z,w}, β̄_{z,w}` by Cardano's formulas; the right side is
symmetric, so they are given here by Vieta's relations.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 28 (`jis-2025-25.3.5-thm-28`). -/
public theorem_wanted sum_trinomialCoefficient_diagonal_binet (z w r₁ r₂ r₃ : ℂ)
    (h₁ : r₁ + r₂ + r₃ = 2 * w) (h₂ : r₁ * r₂ + r₁ * r₃ + r₂ * r₃ = 2 * w ^ 2)
    (h₃ : r₁ * r₂ * r₃ = z + w ^ 3) (h₁₂ : r₁ ≠ r₂) (h₁₃ : r₁ ≠ r₃) (h₂₃ : r₂ ≠ r₃) (n : ℕ) :
    ∑ k ∈ Finset.range (2 * n / 3 + 1),
        (trinomialCoefficient (n - k) k : ℂ) * w ^ (2 * n - 3 * k) * z ^ k =
      (w ^ 2 - w * r₁ + r₁ ^ 2) ^ (n + 1) / ((r₁ - r₂) * (r₁ - r₃)) +
        (w ^ 2 - w * r₂ + r₂ ^ 2) ^ (n + 1) / ((r₂ - r₁) * (r₂ - r₃)) +
        (w ^ 2 - w * r₃ + r₃ ^ 2) ^ (n + 1) / ((r₃ - r₁) * (r₃ - r₂))

/-- **Corollary 33.** For `n > 0`,
`K_n = ∑_{k ≤ 2n/3} binom(n-k, k)_2 n/(n-k) = λ_{3n} / 2^n`, with `λ` the sequence A075115,
`λ_n = 2λ_{n-1} - 2λ_{n-2} + 2λ_{n-3}`, `λ_0 = 3`, `λ_1 = 2`, `λ_2 = 0` (given by its
recurrence).

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Corollary 33 (`jis-2025-25.3.5-cor-33`). -/
public theorem_wanted two_pow_mul_sum_trinomialCoefficient_diagonal_weighted (l : ℕ → ℤ)
    (hl0 : l 0 = 3) (hl1 : l 1 = 2) (hl2 : l 2 = 0)
    (hl : ∀ n, l (n + 3) = 2 * l (n + 2) - 2 * l (n + 1) + 2 * l n) (n : ℕ) (hn : 0 < n) :
    2 ^ n * ∑ k ∈ Finset.range (2 * n / 3 + 1),
        (trinomialCoefficient (n - k) k : ℚ) * n / (n - k : ℕ) = l (3 * n)

/-- **Corollary 36.** Let `r₁, r₂, r₃` be the zeros of `t^3 - 2wt^2 + 2w^2 t - (z + w^3)`.
For `n > 0`,
`∑_{k ≤ 2n/3} binom(n-k, k)_2 (n/(n-k)) w^{2n-3k} z^k = ∑_i (w^2 - w r_i + r_i^2)^n`.
The zeros (Cardano's `α_{z,w}, β_{z,w}, β̄_{z,w}` in the paper) are given by Vieta's relations.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Corollary 36 (`jis-2025-25.3.5-cor-36`). -/
public theorem_wanted sum_trinomialCoefficient_diagonal_weighted_power_sum (z w r₁ r₂ r₃ : ℂ)
    (h₁ : r₁ + r₂ + r₃ = 2 * w) (h₂ : r₁ * r₂ + r₁ * r₃ + r₂ * r₃ = 2 * w ^ 2)
    (h₃ : r₁ * r₂ * r₃ = z + w ^ 3) (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ Finset.range (2 * n / 3 + 1),
        (trinomialCoefficient (n - k) k : ℂ) * n / (n - k : ℕ) * w ^ (2 * n - 3 * k) * z ^ k =
      (w ^ 2 - w * r₁ + r₁ ^ 2) ^ n + (w ^ 2 - w * r₂ + r₂ ^ 2) ^ n +
        (w ^ 2 - w * r₃ + r₃ ^ 2) ^ n

/-- **Corollary 42.** `∑_k binom(n+k, n-k)_2 = T_{2(n+1)}/2 + binom(n, n)_2/2 +
(1/2) ∑_{k=0}^{n-1} binom(k, k)_2 (T_{2(n-k)} + T_{2(n-1-k)})`, with `T` the Tribonacci
numbers (`T_0 = T_1 = 0`, `T_2 = 1`), so `T_{2n}` is the bisection A099463.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Corollary 42 (`jis-2025-25.3.5-cor-42`). -/
public theorem_wanted sum_trinomialCoefficient_add_sub_eq_tribonacci (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (trinomialCoefficient (n + k) (n - k) : ℚ) =
      (tribonacci (2 * (n + 1)) : ℚ) / 2 + (trinomialCoefficient n n : ℚ) / 2 +
        (∑ k ∈ Finset.range n, (trinomialCoefficient k k : ℚ) *
          ((tribonacci (2 * (n - k)) : ℚ) + tribonacci (2 * (n - 1 - k)))) / 2

/-- **Corollary 49.** With `α`, `β` as in Theorem 6 and `g(t) = α(t) f(β(t))`,
`f_{2n} = [t^{2n}] (2-t)(1-t)^{2n} / (2(1-t+t^2)) · g(t / √(1-t+t^2))`. The square roots are
the power series `S`, `Q` of Theorem 6 and `R` with `R^2 = 1 - t + t^2`, `R(0) = 1`.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Corollary 49 (`jis-2025-25.3.5-cor-49`). -/
public theorem_wanted coeff_two_mul_eq_inverse_trinomial_transform (S Q R : PowerSeries ℚ)
    (hS : S ^ 2 = 4 - 3 * X ^ 2) (hS0 : constantCoeff S = 2)
    (hQ : 2 * Q ^ 2 = 2 - X ^ 2 - X * S) (hQ0 : constantCoeff Q = 1)
    (hR : R ^ 2 = 1 - X + X ^ 2) (hR0 : constantCoeff R = 1) (f : PowerSeries ℚ) (n : ℕ) :
    let α := -2 * (2 * Q + X ^ 2 * S - X) * (Q * (3 * X ^ 4 + 2 * X * S - X ^ 2 - 4))⁻¹
    let β := X * (X + S) * (2 * (1 - X ^ 2))⁻¹
    let g := α * f.subst β
    coeff (2 * n) f = coeff (2 * n) ((2 - X) * (1 - X) ^ (2 * n) * (2 * (1 - X + X ^ 2))⁻¹ *
      g.subst (X * R⁻¹))

end

end MetaMathlibExt
