/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Nth
public import Mathlib.Data.Nat.Totient
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

namespace MetaMathlibExt

@[expose] public section

open Polynomial

/-- **A common prime divisor of $x - 1$ and $\Phi_p(x)$ is $p$.** Let $\rho$ and $p$ be primes,
let $x$ be a positive integer, and let $\Phi_p$ be the $p$-th cyclotomic polynomial with integer
coefficients. If $\rho \mid x - 1$ and $\rho \mid \Phi_p(x)$, then $\rho = p$.

Source: Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026),
Article A95, Lemma 1 (`integers-2026-A95-lem-1`). -/
public theorem_wanted prime_eq_of_dvd_sub_one_of_dvd_cyclotomic_eval {ρ p : ℕ}
    (hρ : ρ.Prime) (hp : p.Prime) {x : ℤ} (hx : 0 < x) (h₁ : (ρ : ℤ) ∣ x - 1)
    (h₂ : (ρ : ℤ) ∣ (cyclotomic p ℤ).eval x) : ρ = p

/-- **Divisibility of $x^p - 1$ by $p$.** Let $p$ be a prime, let $x$ be a positive integer, and
let $\Phi_p$ be the $p$-th cyclotomic polynomial with integer coefficients. Then
$p \mid x^p - 1$ if and only if $p \mid x - 1$ and $p \mid \Phi_p(x)$.

Source: Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026),
Article A95, Lemma 2 (`integers-2026-A95-lem-2`). -/
public theorem_wanted prime_dvd_pow_self_sub_one_iff {p : ℕ} (hp : p.Prime) {x : ℤ}
    (hx : 0 < x) :
    (p : ℤ) ∣ x ^ p - 1 ↔ (p : ℤ) ∣ x - 1 ∧ (p : ℤ) ∣ (cyclotomic p ℤ).eval x

/-- **A common prime divisor of $y - 1$ and $\Phi_p(y^{p^{a-1}})$ is $p$.** Let $\rho$ and $p$ be
primes, let $a \ge 1$ be a natural number, let $y$ be a positive integer, and let $\Phi_p$ be the
$p$-th cyclotomic polynomial with integer coefficients. If $\rho \mid y - 1$ and
$\rho \mid \Phi_p(y^{p^{a-1}})$, then $\rho = p$.

Source: Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026),
Article A95, Lemma 3 (`integers-2026-A95-lem-3`). -/
public theorem_wanted prime_eq_of_dvd_sub_one_of_dvd_cyclotomic_eval_pow {ρ p a : ℕ}
    (hρ : ρ.Prime) (hp : p.Prime) (ha : 0 < a) {y : ℤ} (hy : 0 < y) (h₁ : (ρ : ℤ) ∣ y - 1)
    (h₂ : (ρ : ℤ) ∣ (cyclotomic p ℤ).eval (y ^ p ^ (a - 1))) : ρ = p

/-- **Divisibility of $x^{rp^a} - 1$ by $p$.** Let $p$ be a prime, let $r$ and $a$ be natural
numbers with $r$ coprime to $p$, let $x$ be a positive integer, and let $\Phi_p$ be the $p$-th
cyclotomic polynomial with integer coefficients. Then $p \mid x^{rp^a} - 1$ if and only if
$p \mid x^r - 1$ and $p \mid \Phi_p(x^{rp^{i-1}})$ for every $i \in \{1, \dots, a\}$.

Source: Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026),
Article A95, Lemma 4 (`integers-2026-A95-lem-4`). -/
public theorem_wanted prime_dvd_pow_sub_one_iff_cyclotomic {p r a : ℕ} (hp : p.Prime)
    (hr : r.Coprime p) {x : ℤ} (hx : 0 < x) :
    (p : ℤ) ∣ x ^ (r * p ^ a) - 1 ↔
      (p : ℤ) ∣ x ^ r - 1 ∧
        ∀ i ∈ Finset.Icc 1 a, (p : ℤ) ∣ (cyclotomic p ℤ).eval (x ^ (r * p ^ (i - 1)))

/-- **Prime divisors of $\Phi_p(x)$ other than $p$ are $1$ modulo $p$.** Let $\rho$ and $p$ be
distinct primes, let $x$ be a positive integer, and let $\Phi_p$ be the $p$-th cyclotomic
polynomial with integer coefficients. If $\rho \mid \Phi_p(x)$, then $\rho \equiv 1 \pmod p$.

Source: Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026),
Article A95, Proposition 1 (`integers-2026-A95-prop-1`). -/
public theorem_wanted prime_modEq_one_of_dvd_cyclotomic_eval {ρ p : ℕ} (hρ : ρ.Prime)
    (hp : p.Prime) (hne : ρ ≠ p) {x : ℤ} (hx : 0 < x)
    (h : (ρ : ℤ) ∣ (cyclotomic p ℤ).eval x) : Nat.ModEq p ρ 1

/-- The hybrid bound. Let `n = ∏_{i=1}^m p_i^{a_i}` with distinct primes `p_i` (in any order),
`x > 1`, and `ω_n = ω(x^n - 1)`. With `p_0 := 1`, let
`Π^j = {ρ prime : ρ ≡ 1 (mod p_j), ρ ≢ 1 (mod p_s) for j < s ≤ m}` and `r_{i,j}` its `i`-th
element (`Nat.nth`, `0`-indexed here). The source's
`x ≥ min_{k_0 + ⋯ + k_m = ω_n} max_{0 ≤ t ≤ m} (1 + ∏_{j ≤ t} ∏_{i ≤ k_j} r_{i,j})^{T(t)}` with
`T(t) = ∏_{s=1}^t p_s^{-a_s}` is stated equivalently, after raising to the power
`∏_{s ≤ t} p_s^{a_s}`, as the existence of a composition `k` meeting every bound. The parts `k_j`
range over `ℕ` (the source writes `k_i ∈ ℤ⁺`; with positive parts the claim fails for
`n = 3`, `x = 2`, where `x^3 - 1 = 7` and `ω_n = 1` admits no positive composition into two
parts).

Source: Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026),
Article A95, Theorem 1 (`integers-2026-A95-thm-1`). -/
public theorem_wanted hybrid_bound_prime_divisors (m : ℕ) (p a : ℕ → ℕ)
    (hp : ∀ i ∈ Finset.Icc 1 m, (p i).Prime) (hinj : Set.InjOn p (Finset.Icc 1 m))
    (ha : ∀ i ∈ Finset.Icc 1 m, 0 < a i) {x : ℕ} (hx : 1 < x) :
    ∃ k : ℕ → ℕ,
      ∑ j ∈ Finset.range (m + 1), k j =
          (x ^ (∏ i ∈ Finset.Icc 1 m, p i ^ a i) - 1).primeFactors.card ∧
        ∀ t ≤ m,
          1 + ∏ j ∈ Finset.range (t + 1), ∏ i ∈ Finset.range (k j),
              Nat.nth (fun ρ => ρ.Prime ∧ (j = 0 ∨ Nat.ModEq (p j) ρ 1) ∧
                ∀ s ∈ Finset.Ioc j m, ¬ Nat.ModEq (p s) ρ 1) i ≤
            x ^ ∏ s ∈ Finset.Icc 1 t, p s ^ a s

/-- The `p`-hybrid bound (Theorem 1 for prime `n = p`). For a prime `p`, `x > 1` and
`ω_p = ω(x^p - 1)`, let `r_{i,0}` and `r_{j,1}` enumerate the primes `≢ 1` and `≡ 1 (mod p)`
(`Nat.nth`, `0`-indexed here). The source's
`x ≥ min_{0 ≤ k < ω_p} max(1 + ∏_{i ≤ k} r_{i,0}, (1 + ∏_{i ≤ k} r_{i,0} ∏_{j ≤ ω_p - k} r_{j,1})^{1/p})`
is stated equivalently as the existence of `k < ω_p` meeting both bounds, the second after
raising to the `p`-th power.

Source: Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026),
Article A95, Proposition 2 (`integers-2026-A95-prop-2`). -/
public theorem_wanted prime_hybrid_bound {p : ℕ} (hp : p.Prime) {x : ℕ} (hx : 1 < x) :
    ∃ k < (x ^ p - 1).primeFactors.card,
      1 + ∏ i ∈ Finset.range k, Nat.nth (fun ρ => ρ.Prime ∧ ¬ Nat.ModEq p ρ 1) i ≤ x ∧
        1 + (∏ i ∈ Finset.range k, Nat.nth (fun ρ => ρ.Prime ∧ ¬ Nat.ModEq p ρ 1) i) *
            ∏ j ∈ Finset.range ((x ^ p - 1).primeFactors.card - k),
              Nat.nth (fun ρ => ρ.Prime ∧ Nat.ModEq p ρ 1) j ≤ x ^ p

/-- **The ramified bound for $n = 2^a$.** Let $a \ge 1$, let $n = 2^a$, let $x > 1$ be a natural
number, let $\omega_n$ be the number of distinct prime factors of $x^n - 1$, and let
$s_1 = 2 < s_2 = 3 < s_3 = 5 < \cdots$ be the primes in increasing order. Then
$$\min\Bigl(1 + 2n \prod_{i=1}^{\omega_n} s_i,\ 1 + \prod_{i=2}^{\omega_n + 1} s_i\Bigr) \le x^n.$$

Equivalently, $x$ is at least the smaller of the $n$-th roots of these two numbers, which is the
form of the source. The source admits every positive integer $x$; at $x = 1$ the number
$x^n - 1 = 0$ has an empty prime factorization, so $\omega_n = 0$ and the bound would read
$2 \le 1$.

Source: Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026),
Article A95, Theorem 3 (`integers-2026-A95-thm-3`). -/
public theorem_wanted two_pow_ramified_bound {a x : ℕ} (ha : 0 < a) (hx : 1 < x) :
    min (1 + 2 * 2 ^ a * ∏ i ∈ Finset.range (x ^ 2 ^ a - 1).primeFactors.card, Nat.nth Nat.Prime i)
        (1 + ∏ i ∈ Finset.range (x ^ 2 ^ a - 1).primeFactors.card, Nat.nth Nat.Prime (i + 1)) ≤
      x ^ 2 ^ a

/-- **A weaker ramified bound for $n = 2^a$.** Let $a \ge 1$, let $n = 2^a$, let $x > 1$ be a
natural number, let $\omega_n$ be the number of distinct prime factors of $x^n - 1$, and let
$s_1 = 2 < s_2 = 3 < s_3 = 5 < \cdots$ be the primes in increasing order. Then
$$\min\Bigl(1 + n \prod_{i=1}^{\omega_n} s_i,\ 1 + \prod_{i=2}^{\omega_n + 1} s_i\Bigr) \le x^n.$$

This weakens the ramified bound for $n = 2^a$, which has the factor $2n$ in place of $n$. The
extracted text of the source reads $n = 2a$; its own discussion ($n = 4$, "extends to $n = 2^a$")
shows that $n = 2^a$ is meant. As in the stronger bound, $x > 1$ replaces the source's positive
integer $x$.

Source: Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026),
Article A95, Corollary 1 (`integers-2026-A95-cor-1`). -/
public theorem_wanted two_pow_trivial_ramified_bound {a x : ℕ} (ha : 0 < a) (hx : 1 < x) :
    min (1 + 2 ^ a * ∏ i ∈ Finset.range (x ^ 2 ^ a - 1).primeFactors.card, Nat.nth Nat.Prime i)
        (1 + ∏ i ∈ Finset.range (x ^ 2 ^ a - 1).primeFactors.card, Nat.nth Nat.Prime (i + 1)) ≤
      x ^ 2 ^ a

/-- **Primorials below powers of sixteen.** For every positive integer $w$, we have $w < 16$ if and
only if the product $p_1 p_2 \cdots p_w$ of the first $w$ primes is less than $16^w$.

Source: Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026),
Article A95, Proposition 10 (`integers-2026-A95-prop-10`). -/
public theorem_wanted lt_sixteen_iff_prod_first_primes_lt {w : ℕ} (hw : 0 < w) :
    w < 16 ↔ ∏ i ∈ Finset.range w, Nat.nth Nat.Prime i < 16 ^ w

/-- The ramified bound. Let `n = ∏_{i=1}^m p_i^{a_i}` with primes `p_1 < ⋯ < p_m` (the ordering
the source fixes at the start of its Section 5), `x > 1`, `ω_n = ω(x^n - 1)`, and, with
`p_0 := 1`, let `r_{i,j}` be the `i`-th element (`Nat.nth`, `0`-indexed here) of
`Π^j = {ρ prime : ρ ≡ 1 (mod p_j), ρ ≢ 1 (mod p_s) for j < s ≤ m}`. Fix a prime factor `p_α` of
`n` and write `p_α = r_{b,τ}` with `τ ≤ m`. As in `hybrid_bound_prime_divisors`, the source's
`x ≥ min_{k_0 + ⋯ + k_m = ω_n} max_t (1 + ∏_{j ≤ t} δ_α(j) ∏_{i ≤ k_j} r_{i,j})^{T(t)}` is stated
as the existence of a composition `k` (parts in `ℕ`, not `ℤ⁺`) meeting every bound after raising
to the power `∏_{s ≤ t} p_s^{a_s}`. The factors `δ_α(j)` are applied to the block products: if
`p_α ∣ x^n - 1`, block `τ` with `k_τ < b` (`1`-indexed in the source, `k_τ ≤ b` here) has its
largest factor `r_{k_τ,τ}` replaced by `p_α`, and block `α` gains the factor `p_α^{a_α}`; if
`p_α ∤ x^n - 1`, block `τ` with `k_τ ≥ b` drops `p_α` and takes the next element instead. In
the divisible case the composition also has `k_τ > 0` (the source's `δ_α(τ)` is undefined at
`k_τ = 0`). The source's worked example (`n = 3`, `ω_3 = 10`: `x ≥ 4387` if `3 ∣ x^3 - 1`,
`x ≥ 5423` otherwise) is reproduced exactly by this reading. Definitions follow the arXiv version
(arXiv:2412.00010), whose statement matches the journal record.

Source: Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026),
Article A95, Theorem 2 (`integers-2026-A95-thm-2`). -/
public theorem_wanted ramified_bound_prime_divisors (m : ℕ) (p a : ℕ → ℕ)
    (hp : ∀ i ∈ Finset.Icc 1 m, (p i).Prime) (hmono : StrictMonoOn p (Finset.Icc 1 m))
    (ha : ∀ i ∈ Finset.Icc 1 m, 0 < a i) {x : ℕ} (hx : 1 < x) {α : ℕ}
    (hα : α ∈ Finset.Icc 1 m) :
    let n := ∏ i ∈ Finset.Icc 1 m, p i ^ a i
    let r : ℕ → ℕ → ℕ := fun j i => Nat.nth (fun ρ => ρ.Prime ∧
      (j = 0 ∨ Nat.ModEq (p j) ρ 1) ∧ ∀ s ∈ Finset.Ioc j m, ¬ Nat.ModEq (p s) ρ 1) i
    let R : ℕ → ℕ → ℕ := fun j k => ∏ i ∈ Finset.range k, r j i
    ∀ τ ≤ m, ∀ b, r τ b = p α →
      ∃ k : ℕ → ℕ, ∑ j ∈ Finset.range (m + 1), k j = (x ^ n - 1).primeFactors.card ∧
        if p α ∣ x ^ n - 1 then
          0 < k τ ∧ ∀ t ≤ m,
            1 + ∏ j ∈ Finset.range (t + 1),
                (if j = τ then (if k τ ≤ b then p α * R τ (k τ - 1) else R τ (k τ))
                  else if j = α then p α ^ a α * R α (k α) else R j (k j)) ≤
              x ^ ∏ s ∈ Finset.Icc 1 t, p s ^ a s
        else
          ∀ t ≤ m,
            1 + ∏ j ∈ Finset.range (t + 1),
                (if j = τ ∧ b < k τ then ∏ i ∈ (Finset.range (k τ + 1)).erase b, r τ i
                  else R j (k j)) ≤
              x ^ ∏ s ∈ Finset.Icc 1 t, p s ^ a s

/-- The `p`-ramified bound (Theorem 2 for prime `n = p`). For a prime `p`, `x > 1` and
`ω_p = ω(x^p - 1)`, let `r_{i,0}` and `r_{j,1}` enumerate the primes `≢ 1` and `≡ 1 (mod p)`
(`Nat.nth`, `0`-indexed here), `p = r_{b,0}`, `R^0_k = ∏_{i < k} r_{i,0}` and
`R^1_k = ∏_{j < ω_p - k} r_{j,1}`. The source's minima over `k ∈ [0, k') ∪ [k', ω_p)` (with
`k' = b + 1`) are stated as the existence of `k < ω_p` meeting both bounds, the second after
raising to the `p`-th power; `p^{-1} R^0_{k+1}` is written as the product over
`{0, …, k} \ {b}`. If `p ∤ x^p - 1`: `k ≤ b` gives `1 + R^0_k ≤ x`, `1 + R^0_k R^1_k ≤ x^p`, and
`k > b` gives `1 + p^{-1} R^0_{k+1} ≤ x`, `1 + p^{-1} R^0_{k+1} R^1_k ≤ x^p`. If `p ∣ x^p - 1`:
`k ≤ b` gives `1 + p R^0_{k-1} ≤ x`, `1 + p^2 R^0_{k-1} R^1_k ≤ x^p`, and `k > b` gives
`1 + R^0_k ≤ x`, `1 + p R^0_k R^1_k ≤ x^p`. The divisible case requires `p ≠ 2` and has `k > 0`:
`R^0_{-1}` is undefined at `k = 0`, and for `p = 2`, `x = 3` (`x^2 - 1 = 8`, `ω_2 = 1`) the only
admitted `k = 0` fails under any reading (with `R^0_{-1} := 1` the second bound reads
`1 + 4 · 3 = 13 ≤ 9`).

Source: Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026),
Article A95, Proposition 3 (`integers-2026-A95-prop-3`). -/
public theorem_wanted prime_ramified_bound {p : ℕ} (hp : p.Prime) {x : ℕ} (hx : 1 < x) {b : ℕ}
    (hb : Nat.nth (fun ρ => ρ.Prime ∧ ¬ Nat.ModEq p ρ 1) b = p) :
    let ω := (x ^ p - 1).primeFactors.card
    let r₀ : ℕ → ℕ := Nat.nth (fun ρ => ρ.Prime ∧ ¬ Nat.ModEq p ρ 1)
    let R₀ : ℕ → ℕ := fun k => ∏ i ∈ Finset.range k, r₀ i
    let S₀ : ℕ → ℕ := fun k => ∏ i ∈ (Finset.range (k + 1)).erase b, r₀ i
    let R₁ : ℕ → ℕ := fun k =>
      ∏ j ∈ Finset.range (ω - k), Nat.nth (fun ρ => ρ.Prime ∧ Nat.ModEq p ρ 1) j
    (¬ p ∣ x ^ p - 1 → ∃ k < ω,
      if k ≤ b then 1 + R₀ k ≤ x ∧ 1 + R₀ k * R₁ k ≤ x ^ p
      else 1 + S₀ k ≤ x ∧ 1 + S₀ k * R₁ k ≤ x ^ p) ∧
    (p ≠ 2 → p ∣ x ^ p - 1 → ∃ k, 0 < k ∧ k < ω ∧
      if k ≤ b then 1 + p * R₀ (k - 1) ≤ x ∧ 1 + p ^ 2 * R₀ (k - 1) * R₁ k ≤ x ^ p
      else 1 + R₀ k ≤ x ∧ 1 + p * R₀ k * R₁ k ≤ x ^ p)

/-- **Factorization into composed cyclotomic polynomials.** Let $x$ be the indeterminate of the
polynomial ring $\mathbb{Z}[x]$. Let $m$ be a natural number, let $p_1, \dots, p_m$ be primes,
not necessarily distinct, let $a_1, \dots, a_m$ be natural numbers, and put
$n = \prod_{i=1}^m p_i^{a_i}$. For $1 \le i \le m$ let $x_i = x^{N_i}$ with
$N_i = \prod_{1 \le r < i} p_r^{a_r}$. Then
$$x^n - 1 = (x - 1) \prod_{i=1}^m \prod_{j=1}^{a_i} \Phi_{p_i}(x_i^{p_i^{j-1}}),$$
where $\Phi_p$ is the $p$-th cyclotomic polynomial over $\mathbb{Z}$ and $\Phi_{p_i}(\cdot)$
denotes composition of polynomials.

The source takes the prime factorization of $n$; the identity needs only that each $p_i$ is
prime. The definition of $x_i$ follows the arXiv version of the source (arXiv:2412.00010),
which the journal statement refers to as "$x_k$ as above".

Source: Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026),
Article A95, Proposition 4 (`integers-2026-A95-prop-4`). -/
public theorem_wanted X_pow_sub_one_eq_mul_prod_cyclotomic_comp (m : ℕ) (p a : ℕ → ℕ)
    (hp : ∀ i ∈ Finset.Icc 1 m, (p i).Prime) :
    (X ^ (∏ i ∈ Finset.Icc 1 m, p i ^ a i) - 1 : ℤ[X]) =
      (X - 1) * ∏ i ∈ Finset.Icc 1 m, ∏ j ∈ Finset.Icc 1 (a i),
        (cyclotomic (p i) ℤ).comp (X ^ ((∏ r ∈ Finset.Ico 1 i, p r ^ a r) * p i ^ (j - 1)))

/-- **Cohen's prime sieve for the line problem.** Let $q$ and $n$ be natural numbers, let $\omega$
be the number of distinct prime factors of $q^n - 1$, and let $S$ be a set of $s$ prime factors of
$q^n - 1$ with $\delta = 1 - \sum_{\rho \in S} 1/\rho > 0$. Suppose that
$q > (n - 1)^2 \, 2^{2(\omega - s)} \left(\frac{s - 1}{\delta} + 2\right)^2$. Then for all finite
fields $K$ and $L$ with $L$ an extension of $K$, $|K| = q$ and $[L : K] = n$, and all nonzero
$\gamma_1, \gamma_2 \in L$ with $K(\gamma_1/\gamma_2) = L$, there is $a \in K$ such that
$a\gamma_2 + \gamma_1$ generates the multiplicative group $L^\times$.

Source: Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026),
Article A95, Proposition 5 (`integers-2026-A95-prop-5`), quoting S. D. Cohen,
Proposition 4.3. -/
public theorem_wanted mem_lineProblem_of_prime_sieve {q n : ℕ} (S : Finset ℕ)
    (hS : S ⊆ (q ^ n - 1).primeFactors)
    (hδ : 0 < 1 - ∑ ρ ∈ S, (1 : ℚ) / ρ)
    (hbound : ((n : ℚ) - 1) ^ 2 * 2 ^ (2 * ((q ^ n - 1).primeFactors.card - S.card)) *
        (((S.card : ℚ) - 1) / (1 - ∑ ρ ∈ S, (1 : ℚ) / ρ) + 2) ^ 2 < q)
    (K L : Type) [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
    (hK : Fintype.card K = q) (hL : Module.finrank K L = n) (γ₁ γ₂ : L) (h₁ : γ₁ ≠ 0)
    (h₂ : γ₂ ≠ 0) (hgen : IntermediateField.adjoin K {γ₁ / γ₂} = ⊤) :
    ∃ a : K, IsPrimitiveRoot (algebraMap K L a * γ₂ + γ₁) (Fintype.card L - 1)

/-- **Cohen's modified prime sieve for the line problem.** Let $q$ and $n$ be natural numbers such
that $q^n - 1$ has $\omega \ge 2$ distinct prime factors. Let $S$ be a set of $s$ prime factors of
$q^n - 1$, let $l$ be a prime factor of $q^n - 1$ not in $S$, let $k$ be the product of the prime
factors of $q^n - 1$ that are neither $l$ nor in $S$, and put
$\delta = 1 - \sum_{\rho \in S} 1/\rho$. Suppose that $\delta > 1/(l\varphi(k))$, where $\varphi$ is
Euler's totient function, and
$$
q > (n - 1)^2 \left(\frac{2^{\omega - s - 1} \varphi(k) (s - 1 + 2\delta) + 1 - 1/l}
{\varphi(k)\delta - 1/l} - 1\right)^2.
$$
Then for all finite fields $K$ and $L$ with $L$ an extension of $K$, $|K| = q$ and $[L : K] = n$,
and all nonzero $\gamma_1, \gamma_2 \in L$ with $K(\gamma_1/\gamma_2) = L$, there is $a \in K$
such that $a\gamma_2 + \gamma_1$ generates the multiplicative group $L^\times$.

Source: Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026),
Article A95, Proposition 6 (`integers-2026-A95-prop-6`), quoting S. D. Cohen,
Proposition 6.3. -/
public theorem_wanted mem_lineProblem_of_modified_prime_sieve {q n : ℕ}
    (hω : 2 ≤ (q ^ n - 1).primeFactors.card) (S : Finset ℕ) (hS : S ⊆ (q ^ n - 1).primeFactors)
    {l : ℕ} (hl : l ∈ (q ^ n - 1).primeFactors) (hlS : l ∉ S)
    (hδ : (1 : ℚ) / (l * ((∏ ρ ∈ (q ^ n - 1).primeFactors \ insert l S, ρ).totient : ℚ)) <
      1 - ∑ ρ ∈ S, (1 : ℚ) / ρ)
    (hbound : ((n : ℚ) - 1) ^ 2 *
        ((2 ^ ((q ^ n - 1).primeFactors.card - S.card - 1) *
              ((∏ ρ ∈ (q ^ n - 1).primeFactors \ insert l S, ρ).totient : ℚ) *
              ((S.card : ℚ) - 1 + 2 * (1 - ∑ ρ ∈ S, (1 : ℚ) / ρ)) + 1 - 1 / (l : ℚ)) /
            (((∏ ρ ∈ (q ^ n - 1).primeFactors \ insert l S, ρ).totient : ℚ) *
              (1 - ∑ ρ ∈ S, (1 : ℚ) / ρ) - 1 / (l : ℚ)) - 1) ^ 2 < q)
    (K L : Type) [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
    (hK : Fintype.card K = q) (hL : Module.finrank K L = n) (γ₁ γ₂ : L) (h₁ : γ₁ ≠ 0)
    (h₂ : γ₂ ≠ 0) (hgen : IntermediateField.adjoin K {γ₁ / γ₂} = ⊤) :
    ∃ a : K, IsPrimitiveRoot (algebraMap K L a * γ₂ + γ₁) (Fintype.card L - 1)

/-- **General prime sieve for the line problem.** Let $q$ and $n$ be natural numbers, let $\omega$
be the number of distinct prime factors of $q^n - 1$, and let $S$ and $T$ be disjoint sets of prime
factors of $q^n - 1$, with $s = |S|$ and $r = |T|$. Let $k$ be the product of the prime factors of
$q^n - 1$ that lie in neither $S$ nor $T$, and put $\delta = 1 - \sum_{\rho \in S} 1/\rho$,
$\varepsilon = \sum_{l \in T} 1/l$ and $\mu = \varphi(k)/k$, where $\varphi$ is Euler's totient
function. Suppose that $\delta\mu > \varepsilon$ and
$$
q > (n - 1)^2 \left(\frac{2^{\omega - s - r} \mu (s - 1 + 2\delta) - \delta\mu + r -
\varepsilon}{\delta\mu - \varepsilon}\right)^2.
$$
Then for all finite fields $K$ and $L$ with $L$ an extension of $K$, $|K| = q$ and $[L : K] = n$,
and all nonzero $\gamma_1, \gamma_2 \in L$ with $K(\gamma_1/\gamma_2) = L$, there is $a \in K$
such that $a\gamma_2 + \gamma_1$ generates the multiplicative group $L^\times$.

Source: Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026),
Article A95, Proposition 7 (`integers-2026-A95-prop-7`), quoting Bailey, Cohen, Sutherland and
Trudgian, Lemma 1. -/
public theorem_wanted mem_lineProblem_of_general_prime_sieve {q n : ℕ}
    (S T : Finset ℕ) (hS : S ⊆ (q ^ n - 1).primeFactors) (hT : T ⊆ (q ^ n - 1).primeFactors)
    (hST : Disjoint S T)
    (hδε : ∑ l ∈ T, (1 : ℚ) / l < (1 - ∑ ρ ∈ S, (1 : ℚ) / ρ) *
      (((∏ ρ ∈ (q ^ n - 1).primeFactors \ (S ∪ T), ρ).totient : ℚ) /
        (∏ ρ ∈ (q ^ n - 1).primeFactors \ (S ∪ T), ρ : ℕ)))
    (hbound : ((n : ℚ) - 1) ^ 2 *
        ((2 ^ ((q ^ n - 1).primeFactors.card - S.card - T.card) *
              (((∏ ρ ∈ (q ^ n - 1).primeFactors \ (S ∪ T), ρ).totient : ℚ) /
                (∏ ρ ∈ (q ^ n - 1).primeFactors \ (S ∪ T), ρ : ℕ)) *
              ((S.card : ℚ) - 1 + 2 * (1 - ∑ ρ ∈ S, (1 : ℚ) / ρ)) -
            (1 - ∑ ρ ∈ S, (1 : ℚ) / ρ) *
              (((∏ ρ ∈ (q ^ n - 1).primeFactors \ (S ∪ T), ρ).totient : ℚ) /
                (∏ ρ ∈ (q ^ n - 1).primeFactors \ (S ∪ T), ρ : ℕ)) +
            T.card - ∑ l ∈ T, (1 : ℚ) / l) /
          ((1 - ∑ ρ ∈ S, (1 : ℚ) / ρ) *
              (((∏ ρ ∈ (q ^ n - 1).primeFactors \ (S ∪ T), ρ).totient : ℚ) /
                (∏ ρ ∈ (q ^ n - 1).primeFactors \ (S ∪ T), ρ : ℕ)) -
            ∑ l ∈ T, (1 : ℚ) / l)) ^ 2 < q)
    (K L : Type) [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
    (hK : Fintype.card K = q) (hL : Module.finrank K L = n) (γ₁ γ₂ : L) (h₁ : γ₁ ≠ 0)
    (h₂ : γ₂ ≠ 0) (hgen : IntermediateField.adjoin K {γ₁ / γ₂} = ⊤) :
    ∃ a : K, IsPrimitiveRoot (algebraMap K L a * γ₂ + γ₁) (Fintype.card L - 1)

/-- **The line problem for quintic extensions.** Let $E_5$ be the set of $647$ prime powers listed
in the appendix of arXiv:2412.00010, the smallest being $2$ and the largest $62791$. Let $q$ be a
natural number not in $E_5$. Then for all finite fields $K$ and $L$ with $L$ an extension of $K$,
$|K| = q$ and $[L : K] = 5$, and all nonzero $\gamma_1, \gamma_2 \in L$ with
$K(\gamma_1/\gamma_2) = L$, there is $a \in K$ such that $a\gamma_2 + \gamma_1$ generates the
multiplicative group $L^\times$.

Source: Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026),
Article A95, Proposition 8 (`integers-2026-A95-prop-8`). -/
public theorem_wanted mem_lineProblem_five {q : ℕ}
    (hE : q ∉ ([
      2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 29, 31, 32, 37, 41, 43, 47, 49, 53, 59,
      61, 64, 67, 71, 73, 79, 81, 83, 89, 97, 101, 103, 107, 109, 113, 121, 125, 127, 128, 131,
      137, 139, 149, 151, 157, 163, 167, 169, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227,
      229, 233, 239, 241, 243, 251, 256, 257, 269, 271, 277, 281, 283, 289, 293, 307, 311, 313,
      317, 331, 337, 343, 347, 349, 353, 361, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421,
      431, 433, 439, 443, 449, 457, 461, 463, 467, 487, 491, 499, 509, 512, 521, 523, 529, 541,
      547, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 625, 631, 641, 643, 647, 653,
      659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 729, 733, 739, 743, 751, 757, 761, 769,
      773, 787, 797, 811, 821, 823, 827, 829, 839, 841, 853, 857, 859, 863, 877, 881, 883, 887,
      907, 911, 919, 929, 937, 941, 947, 953, 961, 967, 971, 977, 991, 997, 1009, 1013, 1019,
      1021, 1024, 1031, 1033, 1039, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109,
      1117, 1123, 1151, 1153, 1163, 1171, 1181, 1193, 1213, 1217, 1223, 1229, 1231, 1237, 1259,
      1277, 1279, 1283, 1289, 1291, 1301, 1303, 1307, 1321, 1327, 1331, 1361, 1367, 1369, 1373,
      1381, 1399, 1409, 1423, 1429, 1433, 1439, 1447, 1451, 1453, 1471, 1483, 1489, 1499, 1511,
      1531, 1543, 1549, 1567, 1571, 1583, 1597, 1607, 1609, 1621, 1627, 1637, 1667, 1669, 1681,
      1693, 1697, 1699, 1709, 1721, 1723, 1741, 1747, 1753, 1759, 1777, 1783, 1789, 1801, 1831,
      1849, 1861, 1867, 1871, 1873, 1879, 1901, 1907, 1933, 1949, 1951, 1993, 1999, 2003, 2011,
      2017, 2027, 2029, 2053, 2081, 2083, 2087, 2089, 2113, 2131, 2137, 2141, 2143, 2161, 2179,
      2197, 2203, 2209, 2221, 2237, 2251, 2267, 2269, 2281, 2293, 2297, 2311, 2333, 2341, 2347,
      2357, 2371, 2377, 2381, 2389, 2393, 2401, 2411, 2437, 2467, 2473, 2503, 2521, 2531, 2539,
      2551, 2557, 2593, 2621, 2633, 2647, 2659, 2671, 2683, 2689, 2707, 2713, 2731, 2749, 2767,
      2791, 2797, 2803, 2809, 2833, 2851, 2857, 2861, 2887, 2927, 2953, 2963, 2971, 3001, 3011,
      3019, 3023, 3037, 3041, 3061, 3067, 3109, 3121, 3125, 3181, 3187, 3191, 3217, 3221, 3253,
      3259, 3271, 3301, 3319, 3331, 3361, 3391, 3433, 3457, 3463, 3481, 3511, 3529, 3541, 3547,
      3571, 3583, 3607, 3613, 3631, 3643, 3691, 3697, 3721, 3727, 3733, 3739, 3767, 3821, 3823,
      3851, 3853, 3877, 3907, 3911, 3919, 3931, 3943, 4003, 4019, 4021, 4051, 4057, 4096, 4111,
      4129, 4159, 4201, 4219, 4229, 4231, 4243, 4261, 4271, 4273, 4327, 4441, 4447, 4489, 4513,
      4519, 4523, 4561, 4567, 4591, 4603, 4621, 4651, 4657, 4663, 4691, 4733, 4759, 4783, 4789,
      4813, 4831, 4909, 4931, 4933, 4951, 4957, 4999, 5011, 5041, 5101, 5119, 5167, 5179, 5329,
      5437, 5449, 5503, 5521, 5531, 5581, 5591, 5641, 5659, 5701, 5743, 5779, 5791, 5839, 5851,
      5857, 5881, 5923, 6007, 6037, 6043, 6073, 6091, 6121, 6133, 6163, 6217, 6241, 6247, 6271,
      6301, 6361, 6373, 6421, 6427, 6451, 6571, 6581, 6619, 6637, 6679, 6691, 6733, 6763, 6781,
      6791, 6841, 6859, 6889, 6991, 7039, 7177, 7243, 7351, 7411, 7417, 7549, 7561, 7573, 7591,
      7603, 7687, 7723, 7753, 7921, 7951, 8011, 8089, 8161, 8191, 8317, 8353, 8419, 8431, 8647,
      8737, 8779, 8821, 8893, 8941, 8971, 9001, 9091, 9109, 9199, 9241, 9283, 9409, 9421, 9521,
      9631, 9661, 9769, 9781, 9871, 10141, 10201, 10321, 10531, 10609, 10651, 10711, 10831, 10861,
      10891, 11047, 11071, 11131, 11257, 11311, 11317, 11449, 11551, 11701, 11719, 11731, 11881,
      11971, 12391, 12433, 12541, 12769, 13171, 13399, 13567, 13831, 13921, 14281, 14479, 14551,
      14821, 15331, 15511, 15541, 15601, 15625, 15877, 15991, 16339, 16927, 17161, 17491, 17791,
      17851, 18181, 18481, 18769, 19321, 19501, 19891, 20011, 20431, 20749, 21211, 21751, 22201,
      22621, 23011, 23311, 24781, 25117, 26041, 27691, 28561, 28771, 29671, 30661, 32761, 41611,
      42331, 46411, 51871, 60901, 62791
    ] : List ℕ))
    (K L : Type) [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
    (hK : Fintype.card K = q) (hL : Module.finrank K L = 5) (γ₁ γ₂ : L) (h₁ : γ₁ ≠ 0)
    (h₂ : γ₂ ≠ 0) (hgen : IntermediateField.adjoin K {γ₁ / γ₂} = ⊤) :
    ∃ a : K, IsPrimitiveRoot (algebraMap K L a * γ₂ + γ₁) (Fintype.card L - 1)

/-- **Liao–Li–Pu criterion for primitive element sums.** Let $q$ and $n$ be coprime natural numbers
with $q^n > 2$, and let $\omega$ be the number of distinct prime factors of $q^n - 1$. If
$16^\omega < q^n$, that is $q^{n/2} > 2^{2\omega}$, then every finite field $L$ with $q^n$ elements
contains an element $\alpha$ such that both $\alpha$ and $\alpha + \alpha^{-1}$ generate the
multiplicative group $L^\times$.

The hypothesis $q^n > 2$ is added to the source's statement: for $q = 2$ and $n = 1$ the inequality
$16^0 < 2$ holds, but the only generator of $\mathbb{F}_2^\times$ is $1$, and $1 + 1^{-1} = 0$.

Source: Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026),
Article A95, Proposition 9 (`integers-2026-A95-prop-9`), quoting Liao, Li and Pu,
Theorem 1.3. -/
public theorem_wanted mem_primitiveSum_of_sixteen_pow_lt {q n : ℕ} (hcop : q.Coprime n)
    (h2 : 2 < q ^ n) (h : 16 ^ (q ^ n - 1).primeFactors.card < q ^ n)
    (L : Type) [Field L] [Fintype L] (hL : Fintype.card L = q ^ n) :
    ∃ α : L, IsPrimitiveRoot α (Fintype.card L - 1) ∧
      IsPrimitiveRoot (α + α⁻¹) (Fintype.card L - 1)

/-- **Finite fields with a primitive element sum.** For every natural number $q$, we have
$q \notin \{2, 3, 4, 5, 7, 9, 13, 25, 121\}$ if and only if every finite field $L$ with $q$
elements contains an element $\alpha$ such that both $\alpha$ and $\alpha + \alpha^{-1}$ generate
the multiplicative group $L^\times$.

Source: Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026),
Article A95, Proposition 11 (`integers-2026-A95-prop-11`), quoting Cohen, Oliveira e Silva,
Sutherland and Trudgian, Corollary 2. -/
public theorem_wanted mem_primitiveSum_one_iff {q : ℕ} :
    q ∉ ({2, 3, 4, 5, 7, 9, 13, 25, 121} : Finset ℕ) ↔
      ∀ (L : Type) [Field L] [Fintype L], Fintype.card L = q →
        ∃ α : L, IsPrimitiveRoot α (Fintype.card L - 1) ∧
          IsPrimitiveRoot (α + α⁻¹) (Fintype.card L - 1)

/-- **Primitive element sums away from exceptional pairs.** Let $q$ and $n > 1$ be coprime natural
numbers, and let $\omega$ be the number of distinct prime factors of $q^n - 1$. Suppose that the
pair $(n, \omega)$ is none of the following $33$ pairs: $(2, w)$ for $1 \le w \le 11$; $(3, w)$ for
$2 \le w \le 7$; $(4, w)$ for $w \in \{2, 3, 4, 5, 6, 7, 9\}$; $(5, 3)$ and $(5, 5)$; $(6, w)$ for
$3 \le w \le 6$; $(8, 4)$ and $(8, 6)$; and $(12, 6)$. Then every finite field $L$ with $q^n$
elements contains an element $\alpha$ such that both $\alpha$ and $\alpha + \alpha^{-1}$ generate
the multiplicative group $L^\times$.

The hypotheses $n > 1$ and $\gcd(q, n) = 1$ are added. For $n = 1$ and $q = 2$ the pair $(1, 0)$
is not exceptional, yet $\mathbb{F}_2$ has no such $\alpha$; and the source derives the result from
the Liao–Li–Pu criterion, which assumes coprimality.

Source: Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026),
Article A95, Proposition 12 (`integers-2026-A95-prop-12`). -/
public theorem_wanted mem_primitiveSum_of_not_mem_exceptional {q n : ℕ} (hn : 1 < n)
    (hcop : q.Coprime n)
    (hE : (n, (q ^ n - 1).primeFactors.card) ∉ ({(2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6),
      (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7),
      (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 9), (5, 3), (5, 5), (6, 3), (6, 4),
      (6, 5), (6, 6), (8, 4), (8, 6), (12, 6)} : Finset (ℕ × ℕ)))
    (L : Type) [Field L] [Fintype L] (hL : Fintype.card L = q ^ n) :
    ∃ α : L, IsPrimitiveRoot α (Fintype.card L - 1) ∧
      IsPrimitiveRoot (α + α⁻¹) (Fintype.card L - 1)

/-- **Fields without primitive element sums have few prime factors.** Let $q$ and $n$ be natural
numbers with $\gcd(q, n) = 1$. If it is not the case that every finite field $L$ with $q^n$
elements contains an element $\alpha$ such that both $\alpha$ and $\alpha + \alpha^{-1}$ generate
the multiplicative group $L^\times$, then $q^n - 1$ has at most $15$ distinct prime factors.

The hypothesis $\gcd(q, n) = 1$ is added: the source derives the bound from the Liao–Li–Pu
criterion, which assumes it.

Source: Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026),
Article A95, Corollary 2 (`integers-2026-A95-cor-2`). -/
public theorem_wanted card_primeFactors_le_fifteen_of_not_mem_primitiveSum {q n : ℕ}
    (hcop : q.Coprime n)
    (h : ¬ ∀ (L : Type) [Field L] [Fintype L], Fintype.card L = q ^ n →
      ∃ α : L, IsPrimitiveRoot α (Fintype.card L - 1) ∧
        IsPrimitiveRoot (α + α⁻¹) (Fintype.card L - 1)) :
    (q ^ n - 1).primeFactors.card ≤ 15

end

end MetaMathlibExt
