/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.PolygonalNumber
public import MathlibExt.NumberTheory.PracticalNumber
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Data.Nat.ModEq

/-!
# Sums of practical numbers and polygonal numbers

Statements from Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and
Polygonal Numbers*, Journal of Integer Sequences 27 (2024), Article 24.5.1
(arXiv:2403.13533). In the paper "natural number" means positive integer; practical numbers
are `MetaMathlibExt.IsPracticalNumber`. The paper's `s`-gonal number `P_s(n)` is the canonical
`Nat.polygonalNumber s n`; triangular numbers are `Nat.polygonalNumber 3 k = k (k + 1) / 2`
with `k ≥ 0` (the paper's Lemma 5, arXiv Lemma 3.3, counts `0`).
-/

namespace MetaMathlibExt

@[expose] public section

open ArithmeticFunction
open scoped Nat

/-- Every positive integer is a practical number plus a triangular number.

Source: Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and Polygonal
Numbers*, Journal of Integer Sequences 27 (2024), Article 24.5.1, Theorem 1
(`jis-2024-24.5.1-thm-1`). -/
public theorem_wanted exists_practical_add_triangular (n : ℕ) (hn : 0 < n) :
    ∃ q k : ℕ, IsPracticalNumber q ∧ n = q + Nat.polygonalNumber 3 k

/-- For `s > 3`, every sufficiently large positive integer is a practical number plus two
`s`-gonal numbers.

Source: Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and Polygonal
Numbers*, Journal of Integer Sequences 27 (2024), Article 24.5.1, Theorem 2
(`jis-2024-24.5.1-thm-2`). -/
public theorem_wanted eventually_practical_add_two_polygonal (s : ℕ) (hs : 3 < s) :
    ∃ N : ℕ, ∀ n > N, ∃ q x y : ℕ,
      IsPracticalNumber q ∧ n = q + Nat.polygonalNumber s x + Nat.polygonalNumber s y

/-- For positive `m, n` there is `1 ≤ x ≤ 2^m - 1` with `x² ≡ 8n + 1 (mod 2^(m+2))`.

Source: Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and Polygonal
Numbers*, Journal of Integer Sequences 27 (2024), Article 24.5.1, Lemma 3
(arXiv Lemma 3.1; `jis-2024-24.5.1-lem-3`). -/
public theorem_wanted exists_sq_modEq_eight_mul_add_one (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    ∃ x : ℕ, 1 ≤ x ∧ x ≤ 2 ^ m - 1 ∧ x ^ 2 ≡ 8 * n + 1 [MOD 2 ^ (m + 2)]

/-- If `m` is practical and `1 ≤ n ≤ σ(m) + 1`, then `m n` is practical.

Source: Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and Polygonal
Numbers*, Journal of Integer Sequences 27 (2024), Article 24.5.1, Lemma 4
(arXiv Lemma 3.2; `jis-2024-24.5.1-lem-4`), quoting Margenstern. -/
public theorem_wanted isPracticalNumber_mul_of_le_sigma_add_one (m n : ℕ)
    (hm : IsPracticalNumber m) (hn : 0 < n) (hnm : n ≤ sigma 1 m + 1) :
    IsPracticalNumber (m * n)

/-- For odd `x`, `(x² - 1) / 8` is a triangular number.

Source: Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and Polygonal
Numbers*, Journal of Integer Sequences 27 (2024), Article 24.5.1, Lemma 5
(arXiv Lemma 3.3; `jis-2024-24.5.1-lem-5`). -/
public theorem_wanted sq_sub_one_div_eight_eq_triangular (x : ℕ) (hx : Odd x) :
    ∃ k : ℕ, (x ^ 2 - 1) / 8 = Nat.polygonalNumber 3 k

/-- For an odd prime `p`, positive `n` and `s > 3`, some positive `x, y` have
`P_s(x) + P_s(y) ≡ n (mod p)`.

Source: Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and Polygonal
Numbers*, Journal of Integer Sequences 27 (2024), Article 24.5.1, Lemma 6
(arXiv Lemma 4.1; `jis-2024-24.5.1-lem-6`). -/
public theorem_wanted exists_polygonal_add_polygonal_modEq_prime (p n s : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (hn : 0 < n) (hs : 3 < s) :
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ Nat.polygonalNumber s x + Nat.polygonalNumber s y ≡ n [MOD p]

/-- For positive `n` and `s > 3` there are positive `x, y` such that
`P_s(x₁) + P_s(y₁) ≡ n (mod 2)` for all positive `x₁ ≡ x`, `y₁ ≡ y (mod 4)`.

Source: Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and Polygonal
Numbers*, Journal of Integer Sequences 27 (2024), Article 24.5.1, Lemma 7
(arXiv Lemma 4.2; `jis-2024-24.5.1-lem-7`). -/
public theorem_wanted exists_polygonal_add_polygonal_modEq_two (n s : ℕ) (hn : 0 < n)
    (hs : 3 < s) :
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ ∀ x₁ y₁ : ℕ, 0 < x₁ → 0 < y₁ → x₁ ≡ x [MOD 4] → y₁ ≡ y [MOD 4] →
      Nat.polygonalNumber s x₁ + Nat.polygonalNumber s y₁ ≡ n [MOD 2]

/-- For a prime `p ≡ 1 (mod 4)` and positive `n, k` there are positive `x, y` with
`x² + y² ≡ n (mod p^k)` and `p ∤ y`.

Source: Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and Polygonal
Numbers*, Journal of Integer Sequences 27 (2024), Article 24.5.1, Lemma 8
(arXiv Lemma 4.3; `jis-2024-24.5.1-lem-8`). -/
public theorem_wanted exists_sq_add_sq_modEq_prime_pow (p n k : ℕ) (hp : p.Prime)
    (hp4 : p % 4 = 1) (hn : 0 < n) (hk : 0 < k) :
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x ^ 2 + y ^ 2 ≡ n [MOD p ^ k] ∧ ¬ p ∣ y

/-- For `s > 3` there is an odd prime `p ∤ s - 2` such that for all positive `k, n` some
positive `x, y` have `P_s(x) + P_s(y) ≡ n (mod p^k)`. The witness is required to satisfy
`p ≡ 1 (mod 4)` (hence odd), as chosen in the paper's proof via Lemma 8 (arXiv Lemma 4.3);
the printed statement asks only for an odd prime.

Source: Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and Polygonal
Numbers*, Journal of Integer Sequences 27 (2024), Article 24.5.1, Lemma 9
(arXiv Lemma 4.4; `jis-2024-24.5.1-lem-9`). -/
public theorem_wanted exists_prime_polygonal_add_polygonal_modEq_prime_pow (s : ℕ)
    (hs : 3 < s) :
    ∃ p : ℕ, p.Prime ∧ p % 4 = 1 ∧ ¬ p ∣ s - 2 ∧ ∀ k n : ℕ, 0 < k → 0 < n →
      ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ Nat.polygonalNumber s x + Nat.polygonalNumber s y ≡ n [MOD p ^ k]

/-- For `s > 3` and every natural `c` there is a constant `A` with
`2 P_s(2 c x) ≤ A x²` for all `x ≥ 1`. The paper states this for the specific prime
`c = p_{i(s)}` of Lemma 9 (arXiv Lemma 4.4), with `x` real; here `c` is arbitrary and `x` natural.

Source: Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and Polygonal
Numbers*, Journal of Integer Sequences 27 (2024), Article 24.5.1, Lemma 10
(arXiv Lemma 4.5; `jis-2024-24.5.1-lem-10`). -/
public theorem_wanted exists_two_polygonal_two_mul_le_mul_sq (s c : ℕ) (hs : 3 < s) :
    ∃ A : ℕ, ∀ x : ℕ, 1 ≤ x → 2 * Nat.polygonalNumber s (2 * c * x) ≤ A * x ^ 2

/-- A practical number divisible by neither `3` nor `4` is `1` or `2`.

Source: Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and Polygonal
Numbers*, Journal of Integer Sequences 27 (2024), Article 24.5.1, Lemma 11
(arXiv Lemma 4.6; `jis-2024-24.5.1-lem-11`). -/
public theorem_wanted isPracticalNumber_eq_one_or_two (q : ℕ) (hq : IsPracticalNumber q)
    (h3 : ¬ 3 ∣ q) (h4 : ¬ 4 ∣ q) :
    q = 1 ∨ q = 2

/-- (a) If `s ≥ 3` and `s ≡ 0` or `4 (mod 12)`, infinitely many positive integers are not a
practical number plus an `s`-gonal number. (b) The number `E(s)` of positive integers that
are not a practical number plus two `s`-gonal numbers tends to infinity: for every `M`, all
large `s` have at least `M` such integers.

Source: Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and Polygonal
Numbers*, Journal of Integer Sequences 27 (2024), Article 24.5.1, Proposition 12
(arXiv Proposition 4.7; `jis-2024-24.5.1-prop-12`). -/
public theorem_wanted practical_add_polygonal_exceptions (s : ℕ) :
    ((3 ≤ s ∧ (s % 12 = 0 ∨ s % 12 = 4)) →
      {n : ℕ | 0 < n ∧
        ¬ ∃ q m : ℕ, IsPracticalNumber q ∧ n = q + Nat.polygonalNumber s m}.Infinite) ∧
    ∀ M : ℕ, ∃ S : ℕ, ∀ t ≥ S, ∃ F : Finset ℕ, M ≤ F.card ∧ ∀ n ∈ F, 0 < n ∧
      ¬ ∃ q x y : ℕ, IsPracticalNumber q ∧ n = q + Nat.polygonalNumber t x + Nat.polygonalNumber t y

end

end MetaMathlibExt
