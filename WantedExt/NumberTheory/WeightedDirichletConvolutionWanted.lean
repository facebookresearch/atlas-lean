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
/-- **Indicator of $B_\kappa$-free integers.** Let $\kappa$ be a function from the natural numbers
to the natural numbers (only its values $\kappa(p)$ at primes $p$ matter) and let $B_\kappa$ be
the set of prime powers $p^{\kappa(p)}$. A natural number $n$ is $B_\kappa$-free if $n \ge 1$ and
no $p^{\kappa(p)}$ with $p$ prime divides $n$. The indicator $q_{B_\kappa}$ is the integer-valued
arithmetic function with $q_{B_\kappa}(n) = 1$ if $n$ is $B_\kappa$-free and
$q_{B_\kappa}(n) = 0$ otherwise.

The paper indexes the exponents by the position of the prime ($b_i = p_i^{\kappa_i}$); here
$\kappa$ is indexed by the prime itself. For constant $\kappa = k$ this is the indicator $q_k$ of
$k$-free integers.

Source: André Pierro de Camargo, *Weighted Summation of Dirichlet Convolutions and Applications
to Some Divisor Problems over k-Free and B-Free Integers*, INTEGERS 24 (2024), Article A75,
Equations (2), (11), (12). -/
public noncomputable def bFreeIndicator (κ : ℕ → ℕ) : ArithmeticFunction ℤ :=
  ⟨fun n => if n ≠ 0 ∧ ∀ p : ℕ, p.Prime → ¬ p ^ κ p ∣ n then 1 else 0, by simp⟩

open scoped Classical in
/-- **Values of the $B_\kappa$-free indicator.** Let $\kappa$ be a function from the natural
numbers to the natural numbers. For every natural number $n$, the indicator $q_{B_\kappa}$ of
$B_\kappa$-free integers satisfies $q_{B_\kappa}(n) = 1$ if $n \ne 0$ and no $p^{\kappa(p)}$ with
$p$ prime divides $n$, and $q_{B_\kappa}(n) = 0$ otherwise.

Source: André Pierro de Camargo, *Weighted Summation of Dirichlet Convolutions and Applications
to Some Divisor Problems over k-Free and B-Free Integers*, INTEGERS 24 (2024), Article A75,
Equations (11), (12). -/
public theorem bFreeIndicator_apply (κ : ℕ → ℕ) (n : ℕ) :
    bFreeIndicator κ n = if n ≠ 0 ∧ ∀ p : ℕ, p.Prime → ¬ p ^ κ p ∣ n then 1 else 0 :=
  rfl

open scoped Classical in
/-- **The integer $1$ is $B_\kappa$-free.** Let $\kappa$ be a function from the natural numbers
to the natural numbers with $\kappa(p) \ge 1$ for every prime $p$. Then the indicator
$q_{B_\kappa}$ of $B_\kappa$-free integers satisfies $q_{B_\kappa}(1) = 1$.

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
/-- **The prime power $p^{\kappa(p)}$ is not $B_\kappa$-free.** Let $\kappa$ be a function from
the natural numbers to the natural numbers and let $p$ be a prime. Then the indicator
$q_{B_\kappa}$ of $B_\kappa$-free integers satisfies $q_{B_\kappa}(p^{\kappa(p)}) = 0$.

No positivity of $\kappa(p)$ is assumed; for $\kappa(p) = 0$ the statement is
$q_{B_\kappa}(1) = 0$.

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

/-- **Product formula for homogeneous sums of powers.** Let $R$ be a commutative ring, let
$a, b \in R$ and let $\tau, \xi$ be natural numbers. Then
$$
\sum_{j=0}^{\tau+\xi} a^j b^{\tau+\xi-j} =
\left(\sum_{j=0}^{\tau} a^j b^{\tau-j}\right) \left(\sum_{i=0}^{\xi} a^i b^{\xi-i}\right) -
ab \left(\sum_{j=0}^{\tau-1} a^j b^{\tau-1-j}\right)
\left(\sum_{i=0}^{\xi-1} a^i b^{\xi-1-i}\right),
$$
where a sum with upper limit $-1$ is zero.

In the source, $a$ and $b$ are the values $u(n)$ and $v(n)$ of complex arithmetic functions.

Source: André Pierro de Camargo, *Weighted Summation of Dirichlet Convolutions and Applications
to Some Divisor Problems over k-Free and B-Free Integers*, INTEGERS 24 (2024), Article A75,
Lemma 1, Equation (16) (`integers-2024-A75-lem-1`). -/
public theorem_wanted sum_pow_mul_pow_add_eq {R : Type*} [CommRing R] (a b : R) (τ ξ : ℕ) :
    ∑ j ∈ Finset.range (τ + ξ + 1), a ^ j * b ^ (τ + ξ - j) =
      (∑ j ∈ Finset.range (τ + 1), a ^ j * b ^ (τ - j)) *
          (∑ i ∈ Finset.range (ξ + 1), a ^ i * b ^ (ξ - i)) -
        a * b * (∑ j ∈ Finset.range τ, a ^ j * b ^ (τ - 1 - j)) *
          (∑ i ∈ Finset.range ξ, a ^ i * b ^ (ξ - 1 - i))

/-- **Gcd expansion of a convolution of completely multiplicative functions at a product.** Let
$u$ and $v$ be complex-valued completely multiplicative arithmetic functions, meaning
$u(mn) = u(m) u(n)$ and $v(mn) = v(m) v(n)$ for all natural numbers $m$ and $n$. Let $u * v$ be
their Dirichlet convolution and $\mu$ the Möbius function. Then for all natural numbers $r$ and
$s$,

$$(u * v)(rs) = \sum_{m \mid \gcd(r, s)} \mu(m) u(m) v(m) (u * v)(r/m) (u * v)(s/m),$$

the sum running over the positive divisors $m$ of $\gcd(r, s)$ (it is empty when $r = s = 0$).

The paper takes $r, s$ positive; the identity also holds (both sides vanish) when $r$ or $s$
is $0$, so no positivity hypothesis is imposed.

Source: André Pierro de Camargo, *Weighted Summation of Dirichlet Convolutions and Applications
to Some Divisor Problems over k-Free and B-Free Integers*, INTEGERS 24 (2024), Article A75,
Lemma 2, Equation (17) (`integers-2024-A75-lem-2`). -/
public theorem_wanted dirichletConvolution_mul_eq_sum_gcd {u v : ArithmeticFunction ℂ}
    (hu : u.IsCompletelyMultiplicative) (hv : v.IsCompletelyMultiplicative) (r s : ℕ) :
    (u * v) (r * s) = ∑ m ∈ (Nat.gcd r s).divisors,
      (μ m : ℂ) * u m * v m * (u * v) (r / m) * (u * v) (s / m)

/-- **Sums of a Dirichlet convolution over multiples of $r$.** Let $u$ and $v$ be completely
multiplicative arithmetic functions with complex values, let $u * v$ be their Dirichlet
convolution, let $\mu$ be the Möbius function, and for real $y$ put
$D(y) = \sum_{1 \le j \le y} (u * v)(j)$. Then for every natural number $r$ and every real $x$,
$$
\sum_{1 \le j \le x/r} (u * v)(rj) =
\sum_{d \mid r} u(d)\, v(r/d) \sum_{m \mid d} \mu(m)\, v(m)\, D\left(\frac{x}{mr}\right),
$$
where $d$ and $m$ run over positive divisors and $x/0 = 0$, so both sides vanish for $r = 0$.

Both sides also vanish for $x < 1$; the source assumes $r \ge 1$ and $x \ge 1$.

Source: André Pierro de Camargo, *Weighted Summation of Dirichlet Convolutions and Applications
to Some Divisor Problems over k-Free and B-Free Integers*, INTEGERS 24 (2024), Article A75,
Lemma 3, Equation (20) (`integers-2024-A75-lem-3`). -/
public theorem_wanted sum_dirichletConvolution_mul_eq {u v : ArithmeticFunction ℂ}
    (hu : u.IsCompletelyMultiplicative) (hv : v.IsCompletelyMultiplicative) (r : ℕ) (x : ℝ) :
    ∑ j ∈ Finset.Icc 1 ⌊x / r⌋₊, (u * v) (r * j) =
      ∑ d ∈ r.divisors, u d * v (r / d) * ∑ m ∈ d.divisors, (μ m : ℂ) * v m *
        ∑ j ∈ Finset.Icc 1 ⌊x / (m * r)⌋₊, (u * v) j

/-- **Möbius expansion of weighted sums of a Dirichlet convolution.** Let $w$, $u$ and $v$ be
arithmetic functions with complex values, let $*$ denote Dirichlet convolution, let $\mu$ be the
Möbius function and put $g = w * \mu$. Then for every real $x$,
$$
\sum_{1 \le j \le x} w(j)\, (u * v)(j) =
\sum_{1 \le r \le x} g(r) \sum_{1 \le j \le x/r} (u * v)(rj),
$$
where $j$ and $r$ run over positive integers.

Both sides vanish for $x < 1$; the source assumes $x \ge 1$.

Source: André Pierro de Camargo, *Weighted Summation of Dirichlet Convolutions and Applications
to Some Divisor Problems over k-Free and B-Free Integers*, INTEGERS 24 (2024), Article A75,
Lemma 4 (`integers-2024-A75-lem-4`). -/
public theorem_wanted sum_mul_dirichletConvolution_eq_sum_moebius (w u v : ArithmeticFunction ℂ)
    (x : ℝ) :
    ∑ j ∈ Finset.Icc 1 ⌊x⌋₊, w j * (u * v) j =
      ∑ r ∈ Finset.Icc 1 ⌊x⌋₊, (w * (μ : ArithmeticFunction ℂ)) r *
        ∑ j ∈ Finset.Icc 1 ⌊x / r⌋₊, (u * v) (r * j)

/-- **Weighted summation of Dirichlet convolutions.** Let $u$ and $v$ be completely
multiplicative arithmetic functions with complex values, let $w$ be any arithmetic function with
complex values, let $*$ denote Dirichlet convolution, let $\mu$ be the Möbius function, put
$g = w * \mu$, and for real $y$ put $D(y) = \sum_{1 \le j \le y} (u * v)(j)$. Then for every
real $x$,
$$
\sum_{1 \le j \le x} w(j)\, (u * v)(j) =
\sum_{1 \le r \le x} g(r) \sum_{d \mid r} u(d)\, v(r/d) \sum_{m \mid d} \mu(m)\, v(m)\,
D\left(\frac{x}{mr}\right),
$$
where $r$, $d$ and $m$ run over positive integers.

Both sides vanish for $x < 1$; the source assumes $x \ge 1$.

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
/-- **The $B_\kappa$-free indicator convolved with the Möbius function.** Let $\kappa$ be a
function from the natural numbers to the natural numbers with $\kappa(p) \ge 1$ for every prime
$p$, let $q_{B_\kappa}$ be the indicator of $B_\kappa$-free integers, let $\mu$ be the Möbius
function and let $*$ denote Dirichlet convolution. Let $n \ge 1$ be a natural number with prime
factorization $n = \prod_p p^{e_p}$. If $\kappa(p)$ divides $e_p$ for every prime $p$, then
$(q_{B_\kappa} * \mu)(n) = \mu(n^{1/\kappa})$, where $n^{1/\kappa} = \prod_p p^{e_p/\kappa(p)}$;
otherwise $(q_{B_\kappa} * \mu)(n) = 0$.

The source indexes the exponents by the position of the prime ($\kappa_i$ for the $i$-th prime
$p_i$) and requires $b_i = p_i^{\kappa_i} > 1$, which is the hypothesis $\kappa(p) \ge 1$.

Source: André Pierro de Camargo, *Weighted Summation of Dirichlet Convolutions and Applications
to Some Divisor Problems over k-Free and B-Free Integers*, INTEGERS 24 (2024), Article A75,
Lemma 5, Equation (22) (`integers-2024-A75-lem-5`). -/
public theorem_wanted bFreeIndicator_mul_moebius_apply {κ : ℕ → ℕ}
    (hκ : ∀ p : ℕ, p.Prime → 1 ≤ κ p) {n : ℕ} (hn : 1 ≤ n) :
    (bFreeIndicator κ * μ) n =
      if ∀ p : ℕ, κ p ∣ n.factorization p then
        μ (n.factorization.prod fun p e => p ^ (e / κ p))
      else 0

/-- **The $B_\kappa$-free indicator twisted by the principal character, convolved with $\mu$.**
Let $\kappa$ be a function from the natural numbers to the natural numbers with $\kappa(p) \ge 1$
for every prime $p$, let $\xi$ be a natural number, let $q_{B_\kappa}$ be the indicator of
$B_\kappa$-free integers and let $\mu$ be the Möbius function. Put $w(d) = q_{B_\kappa}(d)$ if
$\gcd(d, \xi) = 1$ and $w(d) = 0$ otherwise, so that $w = q_{B_\kappa} \chi_\xi$ with $\chi_\xi$
the principal character modulo $\xi$, and let $(w * \mu)(n) = \sum_{d \mid n} w(d) \mu(n/d)$, the
sum running over the positive divisors $d$ of $n$ (it is empty for $n = 0$). For $r \ge 1$ with
prime factorization $r = \prod_p p^{e_p}$ write $r^\kappa = \prod_p p^{\kappa(p) e_p}$, and set
$0^\kappa = 1$. Then for every natural number $n$ with $(w * \mu)(n) \ne 0$ there are natural
numbers $\ell$ and $r$ with $\ell \mid \xi$, $\gcd(r, \xi) = 1$ and $n = \ell r^\kappa$. Moreover,
for all natural numbers $\ell$ and $r$ with $\ell \mid \xi$, $\gcd(r, \xi) = 1$ and $r \ge 1$,
$(w * \mu)(\ell r^\kappa) = \mu(\ell) \mu(r)$.

The hypothesis $r \ge 1$ in the evaluation is needed: for $r = 0$ the formula is false. No
positivity of $\xi$ is assumed.

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

/-- **Asymptotic for the divisor function summed over $k$-free integers.** Let $k \ge 2$ be a
natural number, let $q_k$ be the indicator of $k$-free integers (the indicator of
$B_\kappa$-free integers for the constant function $\kappa = k$), let $\tau(n)$ be the number of
positive divisors of $n$, let $\gamma$ be the Euler–Mascheroni constant, let
$\Delta(x) = \sum_{1 \le n \le x} \tau(n) - x \log x - (2\gamma - 1) x$ be the Dirichlet divisor
error term, and put

$$c_k = \prod_p \Bigl(1 - \frac{k + 1}{p^k} + \frac{k}{p^{k+1}}\Bigr),$$

the product running over all primes $p$. Then there is a real constant $\beta_k$ such that
$E(x) = \sum_{1 \le n \le x} q_k(n) \tau(n) - c_k x \log x - \beta_k x$ satisfies the following
as $x \to \infty$. If $k \le 3$, then $E(x) = O(x^{1/k + \varepsilon})$ for every
$\varepsilon > 0$. If $k \ge 4$, then for every real $\eta \ge 1/4$ with $\Delta(x) = O(x^\eta)$,
$E(x) = O(x^{\eta + \varepsilon})$ for every $\varepsilon > 0$.

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

/-- **Asymptotic for the divisor function summed over $B_\kappa$-free integers.** Let $\kappa$ be
a function from the natural numbers to the natural numbers and let $K \ge 2$ be the minimum of
$\kappa(p)$ over the primes $p$: $\kappa(p) \ge K$ for every prime $p$, with equality for some
prime. Let $q_{B_\kappa}$ be the indicator of $B_\kappa$-free integers, $\tau(n)$ the number of
positive divisors of $n$, $\gamma$ the Euler–Mascheroni constant and
$\Delta(x) = \sum_{1 \le n \le x} \tau(n) - x \log x - (2\gamma - 1) x$ the Dirichlet divisor
error term, and put

$$C_\kappa = \prod_p \Bigl(1 - \frac{\kappa(p) + 1}{p^{\kappa(p)}} +
\frac{\kappa(p)}{p^{\kappa(p)+1}}\Bigr),$$

the product running over all primes $p$. Then there is a real constant $\beta_\kappa$ such that
$E(x) = \sum_{1 \le n \le x} q_{B_\kappa}(n) \tau(n) - C_\kappa x \log x - \beta_\kappa x$
satisfies the following as $x \to \infty$. If $K \le 3$, then $E(x) = O(x^{1/K + \varepsilon})$
for every $\varepsilon > 0$. If $K \ge 4$, then for every real $\eta \ge 1/4$ with
$\Delta(x) = O(x^\eta)$, $E(x) = O(x^{\eta + \varepsilon})$ for every $\varepsilon > 0$.

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

/-- **Asymptotic for the divisor function summed over $B_\kappa$-free integers in a progression.**
Let $\kappa$ be a function from the natural numbers to the natural numbers and let $K$ be the
minimum of $\kappa(p)$ over the primes $p$: $\kappa(p) \ge K$ for every prime $p$, with equality
for some prime. Assume $K \ge 2$ and $K \ne 3$. Let $a$ and $\xi$ be natural numbers with
$a < \xi$ and $\gcd(a, \xi) = 1$. Let $q_{B_\kappa}$ be the indicator of $B_\kappa$-free
integers, $\tau(n)$ the number of positive divisors of $n$ and $\varphi$ Euler's totient
function, and put

$$C_{\kappa,\xi} = \prod_{p \nmid \xi} \Bigl(1 - \frac{\kappa(p) + 1}{p^{\kappa(p)}} +
\frac{\kappa(p)}{p^{\kappa(p)+1}}\Bigr),$$

the product running over the primes $p$ that do not divide $\xi$. Let $\eta = 1/2$ if $K = 2$
and $\eta = 1/3$ if $K \ge 4$. Then there is a real constant $\tilde c$ such that for every
$\varepsilon > 0$, as $x \to \infty$,

$$\sum_{\substack{1 \le n \le x \\ n \equiv a \pmod{\xi}}} q_{B_\kappa}(n) \tau(n) =
\frac{\varphi(\xi)}{\xi^2} C_{\kappa,\xi} \, x \log x + \tilde c x + O(x^{\eta + \varepsilon}).$$

The case $K = 3$ is not covered by the paper's statement and is excluded.

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
