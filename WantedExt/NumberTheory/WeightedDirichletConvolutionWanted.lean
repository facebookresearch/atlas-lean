/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Algebra.BigOperators.HomogeneousGeomSum
public import MathlibExt.NumberTheory.ArithmeticFunction.CompletelyMultiplicative
public import MathlibExt.NumberTheory.ArithmeticFunction.WeightedDirichletConvolution
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import MathlibExt.NumberTheory.WeightedDirichletConvolution
public import MathlibExt.NumberTheory.WeightedDirichletConvolutionBFreeCoprimeIndicatorMulMoebius

namespace MetaMathlibExt

open ArithmeticFunction Filter Asymptotics
open scoped ArithmeticFunction.Moebius

@[expose] public section

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
