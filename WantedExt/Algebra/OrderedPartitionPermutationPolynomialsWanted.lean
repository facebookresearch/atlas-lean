/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Basic.Complex.Basic
public import MathlibExt.FieldTheory.Finite.PermutationPolynomial

/-!
# Permutation polynomials of the form `∑ n^t X^(n+a)` and related lemmas

Statements from Chandan Kumar Vishwakarma and Rajesh P. Singh, *A Congruence Identity on
Ordered Partitions Using Permutation Polynomials*, INTEGERS 24 (2024), Article A12: the
monomial and power-sum criteria the paper quotes, its binomial-sum identity, and its two
new classes of permutation polynomials over `𝔽_p`. Permutation polynomials use MathlibExt's
`Polynomial.IsPermutationPolynomial` (bijective evaluation map).
-/

namespace MetaMathlibExt

@[expose] public section

open Polynomial

/-- `X ^ d` (with `d ≥ 1`) is a permutation polynomial of the finite field `K` with `q`
elements if and only if `gcd(d, q - 1) = 1`. The hypothesis `d ≥ 1` is added: at `d = 0`,
`q = 2` the right side holds but `X ^ 0 = 1` is constant.

Source: Chandan Kumar Vishwakarma and Rajesh P. Singh, *A Congruence Identity on Ordered
Partitions Using Permutation Polynomials*, INTEGERS 24 (2024), Article A12, Lemma 2
(`integers-2024-A12-lem-2`). -/
public theorem_wanted isPermutationPolynomial_X_pow_iff_coprime {K : Type*} [Field K]
    [Fintype K] {d : ℕ} (hd : 0 < d) :
    (X ^ d : K[X]).IsPermutationPolynomial ↔ d.Coprime (Fintype.card K - 1)

/-- Elements `a₁, …, a_q` of the finite field `K` with `q` elements are distinct if and only
if `∑ aᵢ^t = 0` for `t = 0, 1, …, q - 2` and `∑ aᵢ^(q-1) = -1` (with `0 ^ 0 = 1`).

Source: Chandan Kumar Vishwakarma and Rajesh P. Singh, *A Congruence Identity on Ordered
Partitions Using Permutation Polynomials*, INTEGERS 24 (2024), Article A12, Lemma 3
(`integers-2024-A12-lem-3`). -/
public theorem_wanted injective_iff_sum_pow_eq {K : Type*} [Field K] [Fintype K]
    (a : Fin (Fintype.card K) → K) :
    Function.Injective a ↔
      (∀ t : ℕ, t < Fintype.card K - 1 → ∑ i, a i ^ t = 0) ∧
        ∑ i, a i ^ (Fintype.card K - 1) = -1

/-- For complex `x, y, k` and positive integers `n, m`,
`∑_{i=0}^{n} (-1)^i C(n, i) (kx + iy)^m` equals `(-1)^n y^n n!` when `n = m` and `0` when
`n > m`.

Source: Chandan Kumar Vishwakarma and Rajesh P. Singh, *A Congruence Identity on Ordered
Partitions Using Permutation Polynomials*, INTEGERS 24 (2024), Article A12, Theorem 3
(`integers-2024-A12-thm-3`). -/
public theorem_wanted sum_neg_one_pow_choose_mul_pow (x y k : ℂ) {n m : ℕ} (hn : 0 < n)
    (hm : 0 < m) :
    (n = m → ∑ i ∈ Finset.range (n + 1),
        (-1 : ℂ) ^ i * (n.choose i : ℂ) * (k * x + i * y) ^ m =
          (-1) ^ n * y ^ n * (n.factorial : ℂ)) ∧
      (m < n → ∑ i ∈ Finset.range (n + 1),
        (-1 : ℂ) ^ i * (n.choose i : ℂ) * (k * x + i * y) ^ m = 0)

/-- For an odd prime `p`, positive integers `k, t, a` with `gcd(a + 1, p - 1) = 1` and
`k ≡ 1 (mod p(p - 1))`, the polynomial `∑_{n=1}^{k} n^t X^(n+a)` permutes `𝔽_p` provided
`p - 1 ∤ t`, or `p² ∣ k - 1`.

Source: Chandan Kumar Vishwakarma and Rajesh P. Singh, *A Congruence Identity on Ordered
Partitions Using Permutation Polynomials*, INTEGERS 24 (2024), Article A12, Corollary 1
(`integers-2024-A12-cor-1`). -/
public theorem_wanted isPermutationPolynomial_sum_pow_mul_X_pow_add {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) {k t a : ℕ} (hk : 0 < k) (ht : 0 < t) (ha : 0 < a)
    (hka : (a + 1).Coprime (p - 1)) (hkcong : k ≡ 1 [MOD p * (p - 1)])
    (hcases : ¬(p - 1) ∣ t ∨ p ^ 2 ∣ k - 1) :
    (∑ n ∈ Finset.Icc 1 k, C ((n : ZMod p) ^ t) * X ^ (n + a)).IsPermutationPolynomial

/-- For an odd prime `p`, positive integers `k, t, a` with `p ∤ a`, `gcd(a, p - 1) = 1` and
`k ≡ 1 (mod p(p - 1))`, the polynomial `∑_{n=1}^{k} (an)^t X^(an)` permutes `𝔽_p` provided
`p - 1 ∤ t`, or `p² ∣ k - 1`.

Source: Chandan Kumar Vishwakarma and Rajesh P. Singh, *A Congruence Identity on Ordered
Partitions Using Permutation Polynomials*, INTEGERS 24 (2024), Article A12, Corollary 3
(`integers-2024-A12-cor-3`). -/
public theorem_wanted isPermutationPolynomial_sum_mul_pow_mul_X_pow_mul {p : ℕ}
    [Fact p.Prime] (hp : p ≠ 2) {k t a : ℕ} (hk : 0 < k) (ht : 0 < t) (ha : 0 < a)
    (hpa : ¬p ∣ a) (hap : a.Coprime (p - 1)) (hkcong : k ≡ 1 [MOD p * (p - 1)])
    (hcases : ¬(p - 1) ∣ t ∨ p ^ 2 ∣ k - 1) :
    (∑ n ∈ Finset.Icc 1 k,
      C (((a * n : ℕ) : ZMod p) ^ t) * X ^ (a * n)).IsPermutationPolynomial

/-- For positive integers `t, k`, `(1 - X)^(t+1) ∑_{n=1}^{k} n^t X^n` equals
`∑_{n=1}^{t} (∑_{i=0}^{n-1} (-1)^i C(t+1, i) (n - i)^t) X^n
+ ∑_{m=1}^{t+1} (∑_{i=m}^{t+1} (-1)^i C(t+1, i) (k + m - i)^t) X^(k+m)`, i.e. for `x ≠ 1` the
polynomial `h_t^k(x) = ∑ n^t x^n` is this numerator divided by `(1 - x)^(t+1)`. Stated as an
identity in `ℤ[X]` (equivalent to the paper's quotient form at every `x ≠ 1`).

Source: Chandan Kumar Vishwakarma and Rajesh P. Singh, *A Congruence Identity on Ordered
Partitions Using Permutation Polynomials*, INTEGERS 24 (2024), Article A12, Lemma 4
(`integers-2024-A12-lem-4`). -/
public theorem_wanted one_sub_X_pow_mul_sum_pow_mul_X_pow (t k : ℕ) (ht : 0 < t) (hk : 0 < k) :
    (1 - X : ℤ[X]) ^ (t + 1) * ∑ n ∈ Finset.Icc 1 k, C ((n : ℤ) ^ t) * X ^ n =
      ∑ n ∈ Finset.Icc 1 t, C (∑ i ∈ Finset.range n,
          (-1) ^ i * ((t + 1).choose i : ℤ) * ((n : ℤ) - i) ^ t) * X ^ n +
        ∑ m ∈ Finset.Icc 1 (t + 1), C (∑ i ∈ Finset.Icc m (t + 1),
          (-1) ^ i * ((t + 1).choose i : ℤ) * ((k : ℤ) + m - i) ^ t) * X ^ (k + m)

/-- For an odd prime `p` and positive integers `k, s, t` with `s ≤ p - 2`,
`k ≡ 1 (mod p(p - 1))` and `p² ∣ k - 1` whenever `p - 1 ∣ t`, with `μ = ⌊ks/(p - 1)⌋`:
`∑_{j=1}^{μ} ∑ (ω_1 ⋯ ω_s)^t ≡ 0 (mod p)`, the inner sum over `s`-tuples `ω` with entries in
`{1, …, k}` and `ω_1 + ⋯ + ω_s = j(p - 1)`. The printed hypothesis `s ≢ 0 (mod p)` is replaced
by `s ≤ p - 2`, the range of Hermite's criterion (the paper's Theorem 2) used in the proof; as
printed the claim fails, e.g. `p = 3`, `k = 1`, `s = 2`, `t = 1` gives the sum `1`.

Source: Chandan Kumar Vishwakarma and Rajesh P. Singh, *A Congruence Identity on Ordered
Partitions Using Permutation Polynomials*, INTEGERS 24 (2024), Article A12, Theorem 1
(`integers-2024-A12-thm-1`). -/
public theorem_wanted prime_dvd_sum_compositions_prod_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {k s t : ℕ} (hk : 0 < k) (hs : 0 < s) (hsp : s ≤ p - 2) (ht : 0 < t)
    (hkcong : k ≡ 1 [MOD p * (p - 1)]) (hcases : (p - 1) ∣ t → p ^ 2 ∣ k - 1) :
    p ∣ ∑ j ∈ Finset.Icc 1 (k * s / (p - 1)),
      ∑ ω ∈ (Fintype.piFinset fun _ : Fin s => Finset.Icc 1 k).filter
          (fun ω => ∑ i, ω i = j * (p - 1)),
        (∏ i, ω i) ^ t

/-- The case `t = 1` of Theorem 1: for an odd prime `p` and positive integers `k, s` with
`s ≤ p - 2` and `k ≡ 1 (mod p(p - 1))`, with `μ = ⌊ks/(p - 1)⌋`,
`∑_{j=1}^{μ} ∑ ω_1 ⋯ ω_s ≡ 0 (mod p)` over `s`-tuples with entries in `{1, …, k}` summing to
`j(p - 1)`. The printed hypothesis `s ≢ 0 (mod p)` is replaced by `s ≤ p - 2` (as in
Theorem 1); as printed the claim fails, e.g. `p = 3`, `k = 7`, `s = 2` gives `400 ≡ 1 (mod 3)`.

Source: Chandan Kumar Vishwakarma and Rajesh P. Singh, *A Congruence Identity on Ordered
Partitions Using Permutation Polynomials*, INTEGERS 24 (2024), Article A12, Corollary 2
(`integers-2024-A12-cor-2`). -/
public theorem_wanted prime_dvd_sum_compositions_prod {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {k s : ℕ} (hk : 0 < k) (hs : 0 < s) (hsp : s ≤ p - 2) (hkcong : k ≡ 1 [MOD p * (p - 1)]) :
    p ∣ ∑ j ∈ Finset.Icc 1 (k * s / (p - 1)),
      ∑ ω ∈ (Fintype.piFinset fun _ : Fin s => Finset.Icc 1 k).filter
          (fun ω => ∑ i, ω i = j * (p - 1)),
        ∏ i, ω i

/-- For an odd prime `p`, positive integers `a, k, s, t` with `gcd(a, p - 1) = 1`, `s ≤ p - 2`,
`k ≡ 1 (mod p(p - 1))` and `p² ∣ k - 1` whenever `p - 1 ∣ t`, with `μ = ⌊aks/(p - 1)⌋`:
`∑_{j=1}^{μ} ∑ (ω_1 ⋯ ω_s)^t ≡ 0 (mod p)` over `s`-tuples with entries in `{an : 1 ≤ n ≤ k}`
summing to `j(p - 1)`. Two corrections. The printed hypothesis `s ≢ 0 (mod p)` is replaced by
`s ≤ p - 2` (as in Theorem 1); as printed the claim fails, e.g. `a = 1`, `p = 3`, `k = 7`,
`s = 2`, `t = 1`. The printed bound `μ = ⌊ks/(p - 1)⌋` is extended to `⌊aks/(p - 1)⌋`, the
largest `j` with `j(p - 1)` an exponent of `h_{k,a}(x)^s` (the paper's proof applies Hermite's
criterion to that power); with the printed bound the claim fails for `a > 1`, e.g. `p = 5`,
`a = 3`, `k = 21`, `s = t = 1` gives the sum `12`.

Source: Chandan Kumar Vishwakarma and Rajesh P. Singh, *A Congruence Identity on Ordered
Partitions Using Permutation Polynomials*, INTEGERS 24 (2024), Article A12, Corollary 4
(`integers-2024-A12-cor-4`). -/
public theorem_wanted prime_dvd_sum_compositions_mul_prod_pow {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {a k s t : ℕ} (ha : 0 < a) (hap : a.Coprime (p - 1)) (hk : 0 < k) (hs : 0 < s)
    (hsp : s ≤ p - 2) (ht : 0 < t) (hkcong : k ≡ 1 [MOD p * (p - 1)])
    (hcases : (p - 1) ∣ t → p ^ 2 ∣ k - 1) :
    p ∣ ∑ j ∈ Finset.Icc 1 (a * k * s / (p - 1)),
      ∑ ω ∈ (Fintype.piFinset fun _ : Fin s => (Finset.Icc 1 k).image (a * ·)).filter
          (fun ω => ∑ i, ω i = j * (p - 1)),
        (∏ i, ω i) ^ t

end

end MetaMathlibExt
