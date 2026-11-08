/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.ArithmeticFunction.CompletelyMultiplicative
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace MetaMathlibExt

open ArithmeticFunction Filter Asymptotics
open scoped ArithmeticFunction.Moebius

@[expose] public section

open scoped Classical in
/-- The characteristic function `q_{B_κ}` of `B_κ`-free integers, where `B_κ` is the set of
prime powers `p ^ κ(p)`: `q_{B_κ}(n) = 1` if `n ≥ 1` is divisible by no `p ^ κ(p)` (`p` prime) and
`0` otherwise. The paper indexes the exponents by the position of the prime
(`b_i = p_i ^ κ_i`); here `κ` is indexed by the prime itself. For constant `κ = k` this is the
characteristic function `q_k` of `k`-free integers.

Source: André Pierro de Camargo, *Weighted Summation of Dirichlet Convolutions and Applications
to Some Divisor Problems over k-Free and B-Free Integers*, INTEGERS 24 (2024), Article A75,
Equations (2), (11), (12). -/
public noncomputable def bFreeIndicator (κ : ℕ → ℕ) : ArithmeticFunction ℤ :=
  ⟨fun n => if n ≠ 0 ∧ ∀ p : ℕ, p.Prime → ¬ p ^ κ p ∣ n then 1 else 0, by simp⟩

open scoped Classical in
/-- Unfolding lemma for `bFreeIndicator`.

Source: André Pierro de Camargo, *Weighted Summation of Dirichlet Convolutions and Applications
to Some Divisor Problems over k-Free and B-Free Integers*, INTEGERS 24 (2024), Article A75,
Equations (11), (12). -/
public theorem bFreeIndicator_apply (κ : ℕ → ℕ) (n : ℕ) :
    bFreeIndicator κ n = if n ≠ 0 ∧ ∀ p : ℕ, p.Prime → ¬ p ^ κ p ∣ n then 1 else 0 :=
  rfl

open scoped Classical in
/-- `1` is `B_κ`-free when every exponent `κ(p)` is positive.

Source: André Pierro de Camargo, *Weighted Summation of Dirichlet Convolutions and Applications
to Some Divisor Problems over k-Free and B-Free Integers*, INTEGERS 24 (2024), Article A75,
Equation (12). -/
public theorem bFreeIndicator_one {κ : ℕ → ℕ} (hκ : ∀ p : ℕ, p.Prime → 1 ≤ κ p) :
    bFreeIndicator κ 1 = 1 := by
  have h : ∀ p : ℕ, p.Prime → ¬ p ^ κ p ∣ 1 := by
    intro p hp hdvd
    have h1 : p ^ κ p = 1 := Nat.dvd_one.mp hdvd
    have h2 : p ^ 1 ≤ p ^ κ p := Nat.pow_le_pow_right hp.pos (hκ p hp)
    rw [pow_one] at h2
    have h3 := hp.two_le
    omega
  rw [bFreeIndicator_apply, ite_eq_left_iff]
  intro hc
  exact absurd ⟨one_ne_zero, h⟩ hc

open scoped Classical in
/-- A prime power `p ^ κ(p)` is not `B_κ`-free.

Source: André Pierro de Camargo, *Weighted Summation of Dirichlet Convolutions and Applications
to Some Divisor Problems over k-Free and B-Free Integers*, INTEGERS 24 (2024), Article A75,
Equation (12). -/
public theorem bFreeIndicator_prime_pow {κ : ℕ → ℕ} {p : ℕ} (hp : p.Prime) :
    bFreeIndicator κ (p ^ κ p) = 0 := by
  have : ¬ (p ^ κ p ≠ 0 ∧ ∀ q : ℕ, q.Prime → ¬ q ^ κ q ∣ p ^ κ p) := by
    rintro ⟨-, h⟩
    exact h p hp dvd_rfl
  rw [bFreeIndicator_apply, ite_eq_right_iff]
  intro hc
  exact absurd hc this

/-- Lemma 1: for `a, b` in a commutative ring (the values `u(n), v(n)`) and `τ, ξ ≥ 0`,
`∑_{j=0}^{τ+ξ} a^j b^{τ+ξ-j} = (∑_{j=0}^{τ} a^j b^{τ-j}) (∑_{i=0}^{ξ} a^i b^{ξ-i})
  - a b (∑_{j=0}^{τ-1} a^j b^{τ-1-j}) (∑_{i=0}^{ξ-1} a^i b^{ξ-1-i})`, void sums being zero.

Stated for arbitrary values in a commutative ring instead of `u(n), v(n) ∈ ℂ`.

Source: André Pierro de Camargo, *Weighted Summation of Dirichlet Convolutions and Applications
to Some Divisor Problems over k-Free and B-Free Integers*, INTEGERS 24 (2024), Article A75,
Lemma 1, Equation (16) (`integers-2024-A75-lem-1`). -/
public theorem_wanted sum_pow_mul_pow_add_eq {R : Type*} [CommRing R] (a b : R) (τ ξ : ℕ) :
    ∑ j ∈ Finset.range (τ + ξ + 1), a ^ j * b ^ (τ + ξ - j) =
      (∑ j ∈ Finset.range (τ + 1), a ^ j * b ^ (τ - j)) *
          (∑ i ∈ Finset.range (ξ + 1), a ^ i * b ^ (ξ - i)) -
        a * b * (∑ j ∈ Finset.range τ, a ^ j * b ^ (τ - 1 - j)) *
          (∑ i ∈ Finset.range ξ, a ^ i * b ^ (ξ - 1 - i))

/-- Lemma 2: for completely multiplicative `u, v`,
`(u * v)(rs) = ∑_{m ∣ gcd(r, s)} μ(m) u(m) v(m) (u * v)(r/m) (u * v)(s/m)`.

The paper takes `r, s` positive; the identity also holds (both sides vanish) when `r` or `s`
is `0`, so no positivity hypothesis is imposed.

Source: André Pierro de Camargo, *Weighted Summation of Dirichlet Convolutions and Applications
to Some Divisor Problems over k-Free and B-Free Integers*, INTEGERS 24 (2024), Article A75,
Lemma 2, Equation (17) (`integers-2024-A75-lem-2`). -/
public theorem_wanted dirichletConvolution_mul_eq_sum_gcd {u v : ArithmeticFunction ℂ}
    (hu : u.IsCompletelyMultiplicative) (hv : v.IsCompletelyMultiplicative) (r s : ℕ) :
    (u * v) (r * s) = ∑ m ∈ (Nat.gcd r s).divisors,
      (μ m : ℂ) * u m * v m * (u * v) (r / m) * (u * v) (s / m)

/-- Lemma 3: for completely multiplicative `u, v`, `r ∈ ℕ` and real `x`,
`S_r[u, v](x) = ∑_{j ≤ x/r} (u * v)(rj)` equals
`∑_{d ∣ r} u(d) v(r/d) ∑_{m ∣ d} μ(m) v(m) D[u, v](x/(mr))`, where
`D[u, v](y) = ∑_{1 ≤ j ≤ y} (u * v)(j)` (Equations (7), (19)).

The paper takes `r ≥ 1` and `x ≥ 1`; both sides vanish otherwise, so these hypotheses are dropped.

Source: André Pierro de Camargo, *Weighted Summation of Dirichlet Convolutions and Applications
to Some Divisor Problems over k-Free and B-Free Integers*, INTEGERS 24 (2024), Article A75,
Lemma 3, Equation (20) (`integers-2024-A75-lem-3`). -/
public theorem_wanted sum_dirichletConvolution_mul_eq {u v : ArithmeticFunction ℂ}
    (hu : u.IsCompletelyMultiplicative) (hv : v.IsCompletelyMultiplicative) (r : ℕ) (x : ℝ) :
    ∑ j ∈ Finset.Icc 1 ⌊x / r⌋₊, (u * v) (r * j) =
      ∑ d ∈ r.divisors, u d * v (r / d) * ∑ m ∈ d.divisors, (μ m : ℂ) * v m *
        ∑ j ∈ Finset.Icc 1 ⌊x / (m * r)⌋₊, (u * v) j

/-- Lemma 4: for arbitrary arithmetic functions `w, u, v` and real `x`,
`D[w, u, v](x) = ∑_{j ≤ x} w(j) (u * v)(j) = ∑_{r ≤ x} g(r) S_r[u, v](x)` with `g = w * μ` and
`S_r[u, v](x) = ∑_{j ≤ x/r} (u * v)(rj)`.

The paper's `x ≥ 1` is dropped (both sides vanish for `x < 1`).

Source: André Pierro de Camargo, *Weighted Summation of Dirichlet Convolutions and Applications
to Some Divisor Problems over k-Free and B-Free Integers*, INTEGERS 24 (2024), Article A75,
Lemma 4 (`integers-2024-A75-lem-4`). -/
public theorem_wanted sum_mul_dirichletConvolution_eq_sum_moebius (w u v : ArithmeticFunction ℂ)
    (x : ℝ) :
    ∑ j ∈ Finset.Icc 1 ⌊x⌋₊, w j * (u * v) j =
      ∑ r ∈ Finset.Icc 1 ⌊x⌋₊, (w * (μ : ArithmeticFunction ℂ)) r *
        ∑ j ∈ Finset.Icc 1 ⌊x / r⌋₊, (u * v) (r * j)

/-- Theorem 1: for completely multiplicative `u, v`, any arithmetic function `w` and real `x`,
`D[w, u, v](x) = ∑_{r ≤ x} g(r) ∑_{d ∣ r} u(d) v(r/d) ∑_{m ∣ d} μ(m) v(m) D[u, v](x/(mr))`
with `g = w * μ`, `D[w, u, v](x) = ∑_{j ≤ x} w(j) (u * v)(j)` and
`D[u, v](y) = ∑_{1 ≤ j ≤ y} (u * v)(j)`.

The paper's `x ≥ 1` is dropped (both sides vanish for `x < 1`); the trailing text about the
Dirichlet divisor problem is omitted.

Source: André Pierro de Camargo, *Weighted Summation of Dirichlet Convolutions and Applications
to Some Divisor Problems over k-Free and B-Free Integers*, INTEGERS 24 (2024), Article A75,
Theorem 1, Equation (8) (`integers-2024-A75-thm-1`). -/
public theorem_wanted weighted_sum_dirichletConvolution_eq {u v : ArithmeticFunction ℂ}
    (hu : u.IsCompletelyMultiplicative) (hv : v.IsCompletelyMultiplicative)
    (w : ArithmeticFunction ℂ) (x : ℝ) :
    ∑ j ∈ Finset.Icc 1 ⌊x⌋₊, w j * (u * v) j =
      ∑ r ∈ Finset.Icc 1 ⌊x⌋₊, (w * (μ : ArithmeticFunction ℂ)) r *
        ∑ d ∈ r.divisors, u d * v (r / d) * ∑ m ∈ d.divisors, (μ m : ℂ) * v m *
          ∑ j ∈ Finset.Icc 1 ⌊x / (m * r)⌋₊, (u * v) j

open scoped Classical in
/-- Lemma 5: for `n ≥ 1`, `(q_{B_κ} * μ)(n) = μ(n^{1/κ})` if `n^{1/κ}` is an integer and `0`
otherwise, where for `n = ∏ p^{e_p}` one sets `n^{1/κ} = ∏ p^{e_p/κ(p)}`; it is an integer
exactly when `κ(p) ∣ e_p` for every prime `p`.

`κ` is indexed by primes (paper: `κ_i` for the `i`-th prime) and every `κ(p) ≥ 1` (the paper
requires `b_i = p_i^{κ_i} > 1`).

Source: André Pierro de Camargo, *Weighted Summation of Dirichlet Convolutions and Applications
to Some Divisor Problems over k-Free and B-Free Integers*, INTEGERS 24 (2024), Article A75,
Lemma 5, Equation (22) (`integers-2024-A75-lem-5`). -/
public theorem_wanted bFreeIndicator_mul_moebius_apply {κ : ℕ → ℕ}
    (hκ : ∀ p : ℕ, p.Prime → 1 ≤ κ p) {n : ℕ} (hn : 1 ≤ n) :
    (bFreeIndicator κ * μ) n =
      if ∀ p : ℕ, κ p ∣ n.factorization p then
        μ (n.factorization.prod fun p e => p ^ (e / κ p))
      else 0

/-- Lemma 6: let `w(n) = q_{B_κ}(n) χ_ξ(n)` with `χ_ξ` the principal Dirichlet character modulo
`ξ` (`χ_ξ(n) = 1` if `gcd(n, ξ) = 1`, else `0`). Then `(w * μ)(n) ≠ 0` only if `n = ℓ r^κ` with
`ℓ ∣ ξ` and `gcd(r, ξ) = 1`, and in that case `(w * μ)(n) = μ(ℓ) μ(r)`. Here
`r^κ = ∏ p^{κ(p) e_p}` for `r = ∏ p^{e_p}`, and the convolution is written out as a divisor sum.

`κ` is indexed by primes with every `κ(p) ≥ 1`; `r ≥ 1` is required in the evaluation (for
`r = 0` the formula is false); the paper's positivity of `ξ` is not needed.

Source: André Pierro de Camargo, *Weighted Summation of Dirichlet Convolutions and Applications
to Some Divisor Problems over k-Free and B-Free Integers*, INTEGERS 24 (2024), Article A75,
Lemma 6, Equation (23) (`integers-2024-A75-lem-6`). -/
public theorem_wanted bFreeCoprimeIndicator_mul_moebius {κ : ℕ → ℕ}
    (hκ : ∀ p : ℕ, p.Prime → 1 ≤ κ p) (ξ : ℕ) :
    (∀ n : ℕ, ∑ d ∈ n.divisors, (if d.Coprime ξ then bFreeIndicator κ d else 0) * μ (n / d) ≠ 0 →
        ∃ ℓ r : ℕ, ℓ ∣ ξ ∧ r.Coprime ξ ∧ n = ℓ * r.factorization.prod fun p e => p ^ (κ p * e)) ∧
      ∀ ℓ r : ℕ, ℓ ∣ ξ → r.Coprime ξ → 0 < r →
        ∑ d ∈ (ℓ * r.factorization.prod fun p e => p ^ (κ p * e)).divisors,
            (if d.Coprime ξ then bFreeIndicator κ d else 0) *
              μ ((ℓ * r.factorization.prod fun p e => p ^ (κ p * e)) / d) = μ ℓ * μ r

/-- Corollary 1: for `k ≥ 2` there is a constant `β_k` such that
`D̃_k(x) = ∑_{n ≤ x, n k-free} τ(n) = c_k x log x + β_k x + O(x^{η_k + ε})` for every `ε > 0`,
with `c_k = ∏_p (1 - (k + 1)/p^k + k/p^{k+1})`, `η_k = 1/k` for `k = 2, 3`, and for `k ≥ 4`
`η_k` any `η ≥ 1/4` with `Δ(x) = O(x^η)`, where
`Δ(x) = ∑_{n ≤ x} τ(n) - x log x - (2γ - 1) x` is the Dirichlet divisor error term (10).

The infinite product is a `tprod` over primes; the `O` is as `x → ∞`.

Source: André Pierro de Camargo, *Weighted Summation of Dirichlet Convolutions and Applications
to Some Divisor Problems over k-Free and B-Free Integers*, INTEGERS 24 (2024), Article A75,
Corollary 1 (`integers-2024-A75-cor-1`). -/
public theorem_wanted kFree_divisor_sum_asymptotic {k : ℕ} (hk : 2 ≤ k) :
    ∃ β : ℝ,
      let err : ℝ → ℝ := fun x =>
        (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (bFreeIndicator (fun _ => k) n : ℝ) * n.divisors.card) -
          (∏' p : Nat.Primes, (1 - (k + 1) / (p : ℝ) ^ k + k / (p : ℝ) ^ (k + 1))) *
            x * Real.log x - β * x
      (k ≤ 3 → ∀ ε : ℝ, 0 < ε → err =O[atTop] fun x => x ^ ((1 : ℝ) / k + ε)) ∧
        (4 ≤ k → ∀ η : ℝ, 1 / 4 ≤ η →
          ((fun x : ℝ => (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n.divisors.card : ℝ)) - x * Real.log x -
              (2 * Real.eulerMascheroniConstant - 1) * x) =O[atTop] fun x => x ^ η) →
            ∀ ε : ℝ, 0 < ε → err =O[atTop] fun x => x ^ (η + ε))

/-- Corollary 2: let `κ` assign to each prime `p` an exponent `κ(p)` with minimum
`κ_min ≥ 2`. There is a constant `β_κ` such that
`D̃_{B_κ}(x) = ∑_{n ≤ x, n B_κ-free} τ(n)
  = (∏_p (1 - (κ(p) + 1)/p^{κ(p)} + κ(p)/p^{κ(p)+1})) x log x + β_κ x + O(x^{η_κ + ε})`
for every `ε > 0`, with `η_κ = 1/κ_min` for `κ_min = 2, 3` and, for `κ_min ≥ 4`, `η_κ` any
`η ≥ 1/4` with `Δ(x) = O(x^η)` (`Δ` the Dirichlet divisor error term (10)).

`κ` is indexed by primes (paper: `κ_i` for the `i`-th prime); `κ_min` is the parameter `K`,
attained at some prime.

Source: André Pierro de Camargo, *Weighted Summation of Dirichlet Convolutions and Applications
to Some Divisor Problems over k-Free and B-Free Integers*, INTEGERS 24 (2024), Article A75,
Corollary 2 (`integers-2024-A75-cor-2`). -/
public theorem_wanted bFree_divisor_sum_asymptotic {κ : ℕ → ℕ} {K : ℕ} (hK : 2 ≤ K)
    (hmin : ∀ p : ℕ, p.Prime → K ≤ κ p) (hatt : ∃ p : ℕ, p.Prime ∧ κ p = K) :
    ∃ β : ℝ,
      let err : ℝ → ℝ := fun x =>
        (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (bFreeIndicator κ n : ℝ) * n.divisors.card) -
          (∏' p : Nat.Primes, (1 - (κ p + 1) / (p : ℝ) ^ κ p + κ p / (p : ℝ) ^ (κ p + 1))) *
            x * Real.log x - β * x
      (K ≤ 3 → ∀ ε : ℝ, 0 < ε → err =O[atTop] fun x => x ^ ((1 : ℝ) / K + ε)) ∧
        (4 ≤ K → ∀ η : ℝ, 1 / 4 ≤ η →
          ((fun x : ℝ => (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n.divisors.card : ℝ)) - x * Real.log x -
              (2 * Real.eulerMascheroniConstant - 1) * x) =O[atTop] fun x => x ^ η) →
            ∀ ε : ℝ, 0 < ε → err =O[atTop] fun x => x ^ (η + ε))

/-- Corollary 3: let `κ_min = K ≥ 2` and let `0 ≤ a < ξ` with `gcd(a, ξ) = 1`. There is a
constant `c̃` such that, for every `ε > 0`,
`D̃_{B_κ}(x, a, ξ) = ∑_{n ≤ x, n ≡ a (mod ξ), n B_κ-free} τ(n)
  = (φ(ξ)/ξ²) (∏_{p ∤ ξ} (1 - (κ(p) + 1)/p^{κ(p)} + κ(p)/p^{κ(p)+1})) x log x + c̃ x
    + O(x^{η_κ + ε})`,
with `η_κ = 1/2` for `κ_min = 2` and `η_κ = 1/3` for `κ_min ≥ 4`. The printed statement does not
cover `κ_min = 3`, so neither does this declaration.

The product over `χ_ξ(p) = 1` is written as a `tprod` over primes with factor `1` at primes
dividing `ξ`; `κ` is indexed by primes.

Source: André Pierro de Camargo, *Weighted Summation of Dirichlet Convolutions and Applications
to Some Divisor Problems over k-Free and B-Free Integers*, INTEGERS 24 (2024), Article A75,
Corollary 3, Equation (15) (`integers-2024-A75-cor-3`). -/
public theorem_wanted bFree_divisor_sum_progression_asymptotic {κ : ℕ → ℕ} {K : ℕ} (hK : 2 ≤ K)
    (hK3 : K ≠ 3) (hmin : ∀ p : ℕ, p.Prime → K ≤ κ p) (hatt : ∃ p : ℕ, p.Prime ∧ κ p = K)
    {a ξ : ℕ} (haξ : a < ξ) (hcop : a.Coprime ξ) :
    ∃ c : ℝ, ∀ ε : ℝ, 0 < ε →
      (fun x : ℝ =>
        (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n % ξ = a),
            (bFreeIndicator κ n : ℝ) * n.divisors.card) -
          (Nat.totient ξ : ℝ) / (ξ : ℝ) ^ 2 *
            (∏' p : Nat.Primes, if (p : ℕ).Coprime ξ then
              (1 - (κ p + 1) / (p : ℝ) ^ κ p + κ p / (p : ℝ) ^ (κ p + 1)) else 1) *
            x * Real.log x - c * x) =O[atTop]
        fun x => x ^ ((if K = 2 then (1 : ℝ) / 2 else 1 / 3) + ε)

end

end MetaMathlibExt
