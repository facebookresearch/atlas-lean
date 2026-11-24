/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Calzado, a Bombieri–Vinogradov result and the parity problem — wishlist

Statement-only records for the sieve lemmas of Calzado's INTEGERS 26 (2026)
paper that are stated over explicit objects: the Mertens-type sums over primes
in `x^{1/5} < p ≤ x^{1/2}` (Lemma 1), the size of the Euler product `V(z)` of a
sieve of dimension `k` (Lemma 3), and the sifting bounds for the shifted primes
`{p + a : p ≤ x}` with `a` even and nonzero (Lemmas 4 and 6).

For the shifted primes, `S(A, P, z)` is the number of primes `n ≤ x` such that
`n + a` has no prime factor `q < z` (divisibility in `ℤ`), and `S(A_ℓ, P, z)`
adds the condition `ℓ ∣ n + a`. Here `P` is the set of all primes, as in the
paper's Theorem 2.
-/

open Filter Topology

namespace MetaMathlibExt

@[expose] public section

/-- **Reciprocal totients of the primes between $x^{1/5}$ and $x^{1/2}$.** As the real number $x$
tends to infinity, the sum of $1/\varphi(p)$ over the primes $p$ with $x^{1/5} < p \le x^{1/2}$
tends to $\log(5/2)$, where $\varphi$ is Euler's totient function.

The paper prints the limit as $0.916\ldots$; the exact value $\log(5/2) = 0.91629\ldots$ is
forced by Mertens' theorem.

Source: Angel Calzado, *A Bombieri-Vinogradov Result to Address the Parity
Problem*, INTEGERS 26 (2026), Article A117, Lemma 1
(`integers-2026-A117-lem-1`). -/
public theorem_wanted calzado_sum_inv_totient_fifth_to_half_tendsto :
    Tendsto (fun x : ℝ =>
      ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧
          x ^ ((1 : ℝ) / 5) < (p : ℝ) ∧ (p : ℝ) ≤ x ^ ((1 : ℝ) / 2)),
        1 / (Nat.totient p : ℝ))
      atTop (𝓝 (Real.log (5 / 2)))

/-- **Reciprocal totients of the primes just below $x^{1/2}$.** For every real $B > 0$ there is a
constant $C$ such that for all sufficiently large real $x$, the sum of $1/\varphi(p)$ over the
primes $p$ with $x^{1/2} (\log x)^{-B} < p \le x^{1/2}$ is at most $C \log\log x / \log x$, where
$\varphi$ is Euler's totient function.

Source: Angel Calzado, *A Bombieri-Vinogradov Result to Address the Parity
Problem*, INTEGERS 26 (2026), Article A117, Lemma 1
(`integers-2026-A117-lem-1`). -/
public theorem_wanted calzado_sum_inv_totient_near_sqrt_isBigO (B : ℝ) (hB : 0 < B) :
    ∃ C : ℝ, ∀ᶠ x : ℝ in atTop,
      ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧
          x ^ ((1 : ℝ) / 2) * Real.log x ^ (-B) < (p : ℝ) ∧
            (p : ℝ) ≤ x ^ ((1 : ℝ) / 2)),
        1 / (Nat.totient p : ℝ)
        ≤ C * Real.log (Real.log x) / Real.log x

/-- **Size of the Euler product of a sieve of dimension $k$.** Let $P$ be a set of primes, $k > 0$
a real number, and $\omega$ a real-valued function on the natural numbers with
$0 \le \omega(p) < p$ for $p \in P$. Suppose there is a constant $C_0$ with
$|\sum_{p \in P,\ t \le p < z} \omega(p) \log p / p - k \log(z/t)| \le C_0$ for all real $t$ and
$z$ with $2 \le t \le z$. Then there are constants $c > 0$ and $C > 0$ such that for every real
$z \ge 2$, $c / (\log z)^k \le \prod_{p \in P,\ p < z} (1 - \omega(p)/p) \le C / (\log z)^k$.

The constants depend on $\omega$ and $P$, not only on $k$.

Source: Angel Calzado, *A Bombieri-Vinogradov Result to Address the Parity
Problem*, INTEGERS 26 (2026), Article A117, Lemma 3
(`integers-2026-A117-lem-3`). -/
public theorem_wanted calzado_sieve_euler_product_asymp (P : Set ℕ)
    [DecidablePred (· ∈ P)] (ω : ℕ → ℝ) (k : ℝ) (hk : 0 < k)
    (hP : ∀ p ∈ P, p.Prime ∧ 0 ≤ ω p ∧ ω p < p)
    (hdim : ∃ C₀ : ℝ, ∀ t z : ℝ, 2 ≤ t → t ≤ z →
      |∑ p ∈ (Finset.range (⌈z⌉₊)).filter (fun p : ℕ => p ∈ P ∧ t ≤ (p : ℝ) ∧ (p : ℝ) < z),
          ω p * Real.log p / p - k * Real.log (z / t)| ≤ C₀) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z : ℝ, 2 ≤ z →
      c / Real.log z ^ k ≤
          ∏ p ∈ (Finset.range (⌈z⌉₊)).filter (fun p : ℕ => p ∈ P ∧ (p : ℝ) < z),
            (1 - ω p / p) ∧
        ∏ p ∈ (Finset.range (⌈z⌉₊)).filter (fun p : ℕ => p ∈ P ∧ (p : ℝ) < z),
            (1 - ω p / p) ≤ C / Real.log z ^ k

open Classical in
/-- **Upper bound for sifted shifted primes divisible by a large prime.** Let $a$ be a nonzero
even integer. For real $x$ and a prime $\ell$ let $S_\ell(x)$ be the number of primes $n \le x$
such that $\ell$ divides $n + a$ and no prime $q < x^{1/5}$ divides $n + a$. There is a constant
$C$ such that for all sufficiently large $x$ and every prime $\ell$ with
$x^{1/5} < \ell \le x^{1/2}$, $S_\ell(x) \le C x / (\varphi(\ell) (\log x)^2)$, where $\varphi$ is
Euler's totient function.

Source: Angel Calzado, *A Bombieri-Vinogradov Result to Address the Parity
Problem*, INTEGERS 26 (2026), Article A117, Lemma 4
(`integers-2026-A117-lem-4`). -/
public theorem_wanted calzado_shifted_primes_sifted_multiple_le (a : ℤ) (ha : Even a)
    (ha0 : a ≠ 0) :
    ∃ C : ℝ, ∀ᶠ x : ℝ in atTop, ∀ ℓ : ℕ, ℓ.Prime →
      x ^ ((1 : ℝ) / 5) < (ℓ : ℝ) → (ℓ : ℝ) ≤ x ^ ((1 : ℝ) / 2) →
      (((Finset.range (⌊x⌋₊ + 1)).filter (fun n : ℕ => n.Prime ∧ (ℓ : ℤ) ∣ (n : ℤ) + a ∧
          ∀ q : ℕ, q.Prime → (q : ℝ) < x ^ ((1 : ℝ) / 5) → ¬ (q : ℤ) ∣ (n : ℤ) + a)).card : ℝ)
        ≤ C * x / ((Nat.totient ℓ : ℝ) * Real.log x ^ 2)

open Classical in
/-- **Order of magnitude of the sifted shifted primes.** Let $a$ be a nonzero even integer, and
for real $x$ let $S(x)$ be the number of primes $n \le x$ such that no prime $q < x^{1/5}$ divides
$n + a$. There are constants $0 < C_1 < C_2$ such that
$C_1 x / (\log x)^2 < S(x) < C_2 x / (\log x)^2$ for all sufficiently large $x$.

Source: Angel Calzado, *A Bombieri-Vinogradov Result to Address the Parity
Problem*, INTEGERS 26 (2026), Article A117, Lemma 6
(`integers-2026-A117-lem-6`). -/
public theorem_wanted calzado_shifted_primes_sifted_asymp (a : ℤ) (ha : Even a)
    (ha0 : a ≠ 0) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ C₁ < C₂ ∧ ∀ᶠ x : ℝ in atTop,
      C₁ * x / Real.log x ^ 2 <
          (((Finset.range (⌊x⌋₊ + 1)).filter (fun n : ℕ => n.Prime ∧
            ∀ q : ℕ, q.Prime → (q : ℝ) < x ^ ((1 : ℝ) / 5) →
              ¬ (q : ℤ) ∣ (n : ℤ) + a)).card : ℝ) ∧
        (((Finset.range (⌊x⌋₊ + 1)).filter (fun n : ℕ => n.Prime ∧
            ∀ q : ℕ, q.Prime → (q : ℝ) < x ^ ((1 : ℝ) / 5) →
              ¬ (q : ℤ) ∣ (n : ℤ) + a)).card : ℝ) < C₂ * x / Real.log x ^ 2

open Classical in
/-- **Relative bound for sifted shifted primes divisible by a large prime.** Let $a$ be a nonzero
even integer. For real $x$ let $S(x)$ be the number of primes $n \le x$ such that no prime
$q < x^{1/5}$ divides $n + a$, and for a prime $\ell$ let $S_\ell(x)$ be the number of those $n$
for which moreover $\ell$ divides $n + a$. There is a constant $C$ such that for all sufficiently
large $x$ and every prime $\ell$ with $x^{1/5} < \ell \le x^{1/2}$,
$S_\ell(x) \le C S(x) / \varphi(\ell)$, where $\varphi$ is Euler's totient function.

Source: Angel Calzado, *A Bombieri-Vinogradov Result to Address the Parity
Problem*, INTEGERS 26 (2026), Article A117, Lemma 6
(`integers-2026-A117-lem-6`). -/
public theorem_wanted calzado_shifted_primes_sifted_multiple_le_sifted (a : ℤ)
    (ha : Even a) (ha0 : a ≠ 0) :
    ∃ C : ℝ, ∀ᶠ x : ℝ in atTop, ∀ ℓ : ℕ, ℓ.Prime →
      x ^ ((1 : ℝ) / 5) < (ℓ : ℝ) → (ℓ : ℝ) ≤ x ^ ((1 : ℝ) / 2) →
      (((Finset.range (⌊x⌋₊ + 1)).filter (fun n : ℕ => n.Prime ∧ (ℓ : ℤ) ∣ (n : ℤ) + a ∧
          ∀ q : ℕ, q.Prime → (q : ℝ) < x ^ ((1 : ℝ) / 5) → ¬ (q : ℤ) ∣ (n : ℤ) + a)).card : ℝ)
        ≤ C * (((Finset.range (⌊x⌋₊ + 1)).filter (fun n : ℕ => n.Prime ∧
            ∀ q : ℕ, q.Prime → (q : ℝ) < x ^ ((1 : ℝ) / 5) →
              ¬ (q : ℤ) ∣ (n : ℤ) + a)).card : ℝ) / (Nat.totient ℓ : ℝ)

open Classical in
/-- **Selberg's upper bound sieve.** For all real numbers $\kappa > 0$ and $C_0$ there is a
constant $C$ with the following property. Let $P$ be a set of primes, $\omega$ a non-negative
multiplicative arithmetic function with $\omega(p) < p$ for $p \in P$, $A$ a finite multiset of
positive integers, and $X > 0$ and $z \ge 2$ real numbers such that
$|\sum_{p \in P,\ t \le p < z} \omega(p) \log p / p - \kappa \log(z/t)| \le C_0$ for every real
$t$ with $2 \le t \le z$. Write $P(z) = \prod_{p \in P,\ p < z} p$, let $S$ be the number of
elements of $A$ coprime to $P(z)$ and $\#A_d$ the number of elements of $A$ divisible by $d$, both
counted with multiplicity, and let $\nu(d)$ be the number of distinct prime factors of $d$. Then
$S \le X e^{\gamma\kappa} \Gamma(\kappa + 1) \prod_{p \in P,\ p < z} (1 - \omega(p)/p)
(1 + C / \log z) + \sum_{d \mid P(z),\ d < z^2} 3^{\nu(d)} |\#A_d - \omega(d) X / d|$,
where $\gamma$ is the Euler–Mascheroni constant.

Source: Angel Calzado, *A Bombieri-Vinogradov Result to Address the Parity
Problem*, INTEGERS 26 (2026), Article A117, Lemma 2 (`integers-2026-A117-lem-2`). -/
public theorem_wanted calzado_selberg_upper_bound_sieve (κ C₀ : ℝ) (hκ : 0 < κ) :
    ∃ C : ℝ, ∀ (P : Set ℕ) (ω : ArithmeticFunction ℝ) (A : Multiset ℕ) (X z : ℝ),
      (∀ p ∈ P, p.Prime ∧ ω p < p) → ω.IsMultiplicative → (∀ n, 0 ≤ ω n) →
      (∀ n ∈ A, 0 < n) → 0 < X → 2 ≤ z →
      (∀ t : ℝ, 2 ≤ t → t ≤ z →
        |∑ p ∈ (Finset.range ⌈z⌉₊).filter (fun p : ℕ => p ∈ P ∧ t ≤ (p : ℝ) ∧ (p : ℝ) < z),
            ω p * Real.log p / p - κ * Real.log (z / t)| ≤ C₀) →
      ((A.filter fun n => n.Coprime
          (∏ p ∈ (Finset.range ⌈z⌉₊).filter (fun p : ℕ => p ∈ P ∧ (p : ℝ) < z), p)).card : ℝ) ≤
        X * Real.exp (Real.eulerMascheroniConstant * κ) * Real.Gamma (κ + 1) *
            (∏ p ∈ (Finset.range ⌈z⌉₊).filter (fun p : ℕ => p ∈ P ∧ (p : ℝ) < z),
              (1 - ω p / p)) * (1 + C / Real.log z) +
          ∑ d ∈ (∏ p ∈ (Finset.range ⌈z⌉₊).filter (fun p : ℕ => p ∈ P ∧ (p : ℝ) < z),
              p).divisors.filter (fun d : ℕ => (d : ℝ) < z ^ 2),
            (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors d) *
              |((A.filter (fun n => d ∣ n)).card : ℝ) - ω d / d * X|

open Classical in
/-- **Rosser–Iwaniec linear sieve.** Let $\gamma$ be the Euler–Mascheroni constant, $C_0$ a real
number, and $F, f \colon \mathbb{R} \to \mathbb{R}$ functions continuous on $(0, \infty)$ with
$F(s) = 2e^{\gamma}/s$ for $0 < s \le 3$ and $f(s) = 0$ for $0 < s \le 2$, such that
$u \mapsto uF(u)$ has derivative $f(s - 1)$ at every $s > 3$ and $u \mapsto uf(u)$ has derivative
$F(s - 1)$ at every $s > 2$. Then $f(s) = 2e^{\gamma}\log(s - 1)/s$ for $2 \le s \le 4$, and there
is a constant $C > 0$ with the following property. Let $P$ be a set of primes, $\omega$ a
non-negative multiplicative arithmetic function with $\omega(p) < p$ for $p \in P$, $A$ a finite
multiset of positive integers, and $X > 0$ and $2 \le z \le y$ real numbers such that
$\sum_{p \in P,\ t \le p < z} \omega(p) \log p / p \le \log(z/t) + C_0$ for every real $t$ with
$2 \le t \le z$. Write $P(z) = \prod_{p \in P,\ p < z} p$,
$V(z) = \prod_{p \in P,\ p < z} (1 - \omega(p)/p)$ and $s = \log y / \log z$; let $S$ be the number
of elements of $A$ coprime to $P(z)$ and $\#A_d$ the number of elements of $A$ divisible by $d$,
both counted with multiplicity; and let
$R = \sum_{d \mid P(z),\ d < y} |\#A_d - \omega(d) X / d|$. Then
$S \le X V(z) (F(s) + C e^{-s} (\log y)^{-1/3}) + R$ and
$X V(z) (f(s) - C e^{-s} (\log y)^{-1/3}) - R \le S$.

Source: Angel Calzado, *A Bombieri-Vinogradov Result to Address the Parity
Problem*, INTEGERS 26 (2026), Article A117, Lemma 5 (`integers-2026-A117-lem-5`). -/
public theorem_wanted calzado_linear_sieve (F f : ℝ → ℝ)
    (hFc : ContinuousOn F (Set.Ioi 0)) (hfc : ContinuousOn f (Set.Ioi 0))
    (hF : ∀ s, 0 < s → s ≤ 3 → F s = 2 * Real.exp Real.eulerMascheroniConstant / s)
    (hf : ∀ s, 0 < s → s ≤ 2 → f s = 0)
    (hF' : ∀ s, 3 < s → HasDerivAt (fun u => u * F u) (f (s - 1)) s)
    (hf' : ∀ s, 2 < s → HasDerivAt (fun u => u * f u) (F (s - 1)) s) (C₀ : ℝ) :
    (∀ s, 2 ≤ s → s ≤ 4 → f s = 2 * Real.exp Real.eulerMascheroniConstant * Real.log (s - 1) / s) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Set ℕ) (ω : ArithmeticFunction ℝ) (A : Multiset ℕ) (X z y : ℝ),
      (∀ p ∈ P, p.Prime ∧ ω p < p) → ω.IsMultiplicative → (∀ n, 0 ≤ ω n) →
      (∀ n ∈ A, 0 < n) → 0 < X → 2 ≤ z → z ≤ y →
      (∀ t : ℝ, 2 ≤ t → t ≤ z →
        ∑ p ∈ (Finset.range ⌈z⌉₊).filter (fun p : ℕ => p ∈ P ∧ t ≤ (p : ℝ) ∧ (p : ℝ) < z),
            ω p * Real.log p / p ≤ Real.log (z / t) + C₀) →
      let Pz := ∏ p ∈ (Finset.range ⌈z⌉₊).filter (fun p : ℕ => p ∈ P ∧ (p : ℝ) < z), p
      let V := ∏ p ∈ (Finset.range ⌈z⌉₊).filter (fun p : ℕ => p ∈ P ∧ (p : ℝ) < z), (1 - ω p / p)
      let s := Real.log y / Real.log z
      let R := ∑ d ∈ Pz.divisors.filter (fun d : ℕ => (d : ℝ) < y),
        |((A.filter (fun n => d ∣ n)).card : ℝ) - ω d / d * X|
      let S := ((A.filter fun n => n.Coprime Pz).card : ℝ)
      S ≤ X * V * (F s + C * Real.exp (-s) * Real.log y ^ (-(1 : ℝ) / 3)) + R ∧
        X * V * (f s - C * Real.exp (-s) * Real.log y ^ (-(1 : ℝ) / 3)) - R ≤ S

open Classical in
/-- **Lower bound for primes $n$ with $n + a$ prime, up to a sieve error.** Let $a$ be a nonzero
even integer, and call a prime $n$ admissible at level $x$ if no prime $q < x^{1/5}$ divides
$n + a$. For a prime $p$ and real $x$ let
$\bar\Delta_p(x) = \#\{n \le x \text{ admissible} : n \equiv -a \pmod p\} -
\#\{n \le x \text{ admissible} : \gcd(n, p) = 1\} / \varphi(p)$, where $\varphi$ is Euler's
totient function. There is $C > 0$ such that for every real $B > 0$ and all sufficiently large
real $x$, the number of primes $n \le x$ with $n + a > 0$ and $n + a$ prime is at least
$C x / (\log x)^2 - \sum_p \bar\Delta_p(x)$, the sum running over the primes $p$ with
$x^{1/5} < p \le x^{1/2} (\log x)^{-B}$.

Source: Angel Calzado, *A Bombieri-Vinogradov Result to Address the Parity
Problem*, INTEGERS 26 (2026), Article A117, Theorem 2 (`integers-2026-A117-thm-2`). -/
public theorem_wanted calzado_shifted_primes_prime_count_lower (a : ℤ) (ha : Even a)
    (ha0 : a ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℝ, 0 < B → ∀ᶠ x : ℝ in atTop,
      C * x / Real.log x ^ 2 -
          ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧
              x ^ ((1 : ℝ) / 5) < (p : ℝ) ∧ (p : ℝ) ≤ x ^ ((1 : ℝ) / 2) * Real.log x ^ (-B)),
            ((((Finset.range (⌊x⌋₊ + 1)).filter (fun n : ℕ => n.Prime ∧
                (n : ℤ) ≡ -a [ZMOD p] ∧ ∀ q : ℕ, q.Prime → (q : ℝ) < x ^ ((1 : ℝ) / 5) →
                  ¬ (q : ℤ) ∣ (n : ℤ) + a)).card : ℝ) -
              (((Finset.range (⌊x⌋₊ + 1)).filter (fun n : ℕ => n.Prime ∧ n.Coprime p ∧
                ∀ q : ℕ, q.Prime → (q : ℝ) < x ^ ((1 : ℝ) / 5) →
                  ¬ (q : ℤ) ∣ (n : ℤ) + a)).card : ℝ) / (Nat.totient p : ℝ)) ≤
        (((Finset.range (⌊x⌋₊ + 1)).filter (fun n : ℕ => n.Prime ∧
          0 < (n : ℤ) + a ∧ Prime ((n : ℤ) + a))).card : ℝ)

end

end MetaMathlibExt
