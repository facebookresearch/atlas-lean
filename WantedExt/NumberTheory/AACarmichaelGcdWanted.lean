/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Data.Set.Card
public import Mathlib.NumberTheory.ArithmeticFunction.Carmichael

namespace MetaMathlibExt

@[expose] public section

/-- **$(a, a)$-Carmichael numbers.** Let $a$ be an integer. A natural number $n$ is an
$(a, a)$-Carmichael number if $n$ is squarefree and $p - a$ divides $n - a$ in $\mathbb{Z}$ for
every prime $p$ dividing $n$.

Source: Thomas Wright, *(a,a)-Carmichael Numbers and Greatest Common Divisors of p-a*,
INTEGERS 26 (2026), Article A123, abstract and Section 1 (definition read from the arXiv version,
arXiv:2607.02738; the journal display could not be checked). -/
def IsAACarmichael (a : ℤ) (n : ℕ) : Prop :=
  Squarefree n ∧ ∀ p ∈ n.primeFactors, ((p : ℤ) - a) ∣ ((n : ℤ) - a)

/-- **Primes are $(a, a)$-Carmichael numbers.** For every integer $a$, every prime $p$ is an
$(a, a)$-Carmichael number.

Source: Thomas Wright, *(a,a)-Carmichael Numbers and Greatest Common Divisors of p-a*,
INTEGERS 26 (2026), Article A123, characteristic lemma of the definition in Section 1. -/
theorem isAACarmichael_of_prime (a : ℤ) {p : ℕ} (hp : p.Prime) : IsAACarmichael a p := by
  refine ⟨hp.prime.squarefree, fun q hq => ?_⟩
  rw [hp.primeFactors, Finset.mem_singleton] at hq
  subst hq
  exact dvd_rfl

/-- **Conditional lower bound for $(a, a)$-Carmichael numbers with prescribed gcd.** Assume
Conjecture 2: there are a real number $A \ge 2$ and a natural number $l_0$ such that for every
natural number $l \ge l_0$ and every integer $b$ with $\gcd(b, l) = 1$ there is a prime $p$ with
$p \equiv b \pmod{l}$ and $p < l (\log l)^A$. Let $a$ be an integer and $\nu$ a positive integer
with $\gcd(a, \nu) = 1$ and $a + \nu$ odd. For real $X$ let $C_\nu(X, a)$ be the number of
$(a, a)$-Carmichael numbers $n \le X$ for which the nonnegative greatest common divisor of the
integers $p - a$, over the primes $p$ dividing $n$, equals $\nu$. Then for every $\varepsilon > 0$
and all sufficiently large real $X$,
$$C_\nu(X, a) \ge X^{1 - (2 + \varepsilon) \log\log\log\log X / \log\log\log X}.$$

This is the paper's bound $C_\nu(X, a) \ge X^{1 - (2 + o(1)) \log\log\log\log X / \log\log\log X}$,
with $2 + \varepsilon$ in place of $2 + o(1)$.

Source: definitions of $C_\nu(X, a)$ and Conjecture 2 read from the arXiv version
(arXiv:2607.02738); the theorem's journal wording matches it.

Source: Thomas Wright, *(a,a)-Carmichael Numbers and Greatest Common Divisors of p-a*,
INTEGERS 26 (2026), Article A123, Theorem 1 (`integers-2026-A123-thm-1`). -/
public theorem_wanted aaCarmichael_count_ge_of_least_prime_in_progression_bound
    (hconj : ∃ A : ℝ, 2 ≤ A ∧ ∃ l₀ : ℕ, ∀ l : ℕ, l₀ ≤ l → ∀ b : ℤ, Int.gcd b l = 1 →
      ∃ p : ℕ, p.Prime ∧ (p : ℤ) ≡ b [ZMOD l] ∧ (p : ℝ) < l * Real.log l ^ A)
    (a : ℤ) (ν : ℕ) (hν : 0 < ν) (hcop : Int.gcd a ν = 1) (hpar : Odd (a + ν))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in Filter.atTop,
      X ^ (1 - (2 + ε) * Real.log (Real.log (Real.log (Real.log X))) /
          Real.log (Real.log (Real.log X))) ≤
        ({n : ℕ | (n : ℝ) ≤ X ∧ IsAACarmichael a n ∧
            n.primeFactors.gcd (fun p => (p : ℤ) - a) = ν}.ncard : ℝ)


/-- **Size of the auxiliary primes in the construction.** For a natural number $z$, let $J$ be the
product of the primes $r$ with $z/2 \le r \le z$, and write $\omega(g)$ for the number of distinct
prime factors of $g$. For every real $A$ and all sufficiently large natural numbers $z$ the
following holds: if $j$, $g$ and $q$ are natural numbers with $1 \le j \le (\log z)^{2A}$,
$g \mid J$, $\omega(g) = \lfloor \log z \rfloor$, $q$ prime and $q = gj + 1$, then
$$(z/6)^{\log z} \le q \le 2 z^{\log z} (\log z)^{2A}.$$

In the paper the bound is stated for the primes $q$ of a chosen set $\mathcal{Q}_i$ of such primes
with a fixed $j = j_0$, and $A \ge 2$ is the constant of Conjecture 2; the statement here covers
every such $j$ and $q$, and every real $A$.

Source: Thomas Wright, *(a,a)-Carmichael Numbers and Greatest Common Divisors of p-a*,
INTEGERS 26 (2026), Article A123, Section 3 (definitions of `J`, `𝓡_j`, `𝒬ᵢ`) and Lemma 1
(`integers-2026-A123-lem-1`). -/
public theorem_wanted rpow_log_le_prime_of_eq_mul_add_one_of_dvd_prod_primes
    (A : ℝ) :
    ∀ᶠ z : ℕ in Filter.atTop, ∀ j g q : ℕ, 1 ≤ j → (j : ℝ) ≤ Real.log z ^ (2 * A) →
      g ∣ ∏ r ∈ (Finset.Iic z).filter (fun r : ℕ => r.Prime ∧ (z : ℝ) / 2 ≤ r), r →
      g.primeFactors.card = ⌊Real.log z⌋₊ → q.Prime → q = g * j + 1 →
        ((z : ℝ) / 6) ^ Real.log z ≤ q ∧
          (q : ℝ) ≤ 2 * (z : ℝ) ^ Real.log z * Real.log z ^ (2 * A)

/-- **The Carmichael function of a product of auxiliary primes is small.** For a natural number
$z$, let $J$ be the product of the primes $r$ with $z/2 \le r \le z$, and write $\omega(g)$ for the
number of distinct prime factors of $g$. For every real $A$ and all sufficiently large natural
numbers $z$ the following holds: for every natural number $j$ with $1 \le j \le (\log z)^{2A}$
and every finite set $S$ of primes such that each $q \in S$ equals $gj + 1$ for some natural
number $g$ with $g \mid J$ and $\omega(g) = \lfloor \log z \rfloor$, the Carmichael function
$\lambda$ satisfies $\lambda\bigl(\prod_{q \in S} q\bigr) \le e^{4z/5}$.

In the paper this is stated for $L_1 L_2$, the product of the primes in two disjoint chosen sets
of such primes for a fixed $j = j_0$; the statement here covers every finite set of such primes,
for every such $j$ and every real $A$.

Source: Thomas Wright, *(a,a)-Carmichael Numbers and Greatest Common Divisors of p-a*,
INTEGERS 26 (2026), Article A123, Section 3 and Lemma 3 (`integers-2026-A123-lem-3`). -/
public theorem_wanted carmichael_prod_primes_eq_mul_add_one_le_exp
    (A : ℝ) :
    ∀ᶠ z : ℕ in Filter.atTop, ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ Real.log z ^ (2 * A) →
      ∀ S : Finset ℕ, (∀ q ∈ S, q.Prime ∧ ∃ g : ℕ,
          g ∣ ∏ r ∈ (Finset.Iic z).filter (fun r : ℕ => r.Prime ∧ (z : ℝ) / 2 ≤ r), r ∧
          g.primeFactors.card = ⌊Real.log z⌋₊ ∧ q = g * j + 1) →
        (ArithmeticFunction.carmichael (∏ q ∈ S, q) : ℝ) ≤ Real.exp (4 * z / 5)

/-- **Exact gcd of two shifted values in the construction.** Let $a$ be an integer and let $\nu$,
$L_1$, $L_2$, $k_1$, $k_2$, $d_1$, $d_2$ be natural numbers with $\gcd(L_1, L_2) = 1$,
$\gcd(k_1, \nu L_1 L_2) = \gcd(k_2, \nu L_1 L_2) = 1$, $\gcd(k_1, k_2) = 1$, $d_1 \mid L_1$ and
$d_2 \mid L_2$. If $p_1 = d_1 k_1 \nu + a$ and $p_2 = d_2 k_2 \nu + a$, then
$\gcd(p_1 - a, p_2 - a) = \nu$.

In the paper $p_1, p_2$ are primes, $d_1, d_2$ have a prescribed number of prime factors,
$L_1, L_2$ are the products of two disjoint sets of primes, and $k_1, k_2$ come from Lemmas 4 and
5; the statement keeps only the hypotheses the conclusion uses.

Source: Thomas Wright, *(a,a)-Carmichael Numbers and Greatest Common Divisors of p-a*,
INTEGERS 26 (2026), Article A123, Section 5 (definition of `𝒫^i_k`) and Lemma 6
(`integers-2026-A123-lem-6`). -/
public theorem_wanted int_gcd_sub_eq_of_eq_mul_mul_add
    (a : ℤ) (ν L₁ L₂ k₁ k₂ d₁ d₂ : ℕ) (hL : Nat.Coprime L₁ L₂)
    (hk₁ : Nat.Coprime k₁ (ν * L₁ * L₂)) (hk₂ : Nat.Coprime k₂ (ν * L₁ * L₂))
    (hk : Nat.Coprime k₁ k₂) (hd₁ : d₁ ∣ L₁) (hd₂ : d₂ ∣ L₂) (p₁ p₂ : ℤ)
    (hp₁ : p₁ = d₁ * k₁ * ν + a) (hp₂ : p₂ = d₂ * k₂ * ν + a) :
    Int.gcd (p₁ - a) (p₂ - a) = ν

end

end MetaMathlibExt
