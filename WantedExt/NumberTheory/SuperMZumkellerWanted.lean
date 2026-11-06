/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Super m-Zumkeller numbers

Statements from Harish Patodia, "Super m-Zumkeller Numbers",
*INTEGERS* 26 (2026), Article A79
(<https://math.colgate.edu/~integers/aa79/aa79.pdf>),
DOI `10.5281/zenodo.20931172`.

For a positive integer `n`, `T(n)` is the product of all positive
divisors of `n` and `τ(n)` is their number.  The integer `n` is
*super-m-Zumkeller* if the divisors of `T(n)` can be partitioned
into two disjoint subsets with equal products (encoded by one
subset `A` whose product equals the product of its complement),
and *`k`-m-perfect* if `T(n) = n^k`.  Only the seven records of
this paper that are correct as printed are formalized here.

**The paper's Theorems 4, 5, and 7 are false as printed** and
are deliberately not stated: Theorem 4 fails at `60 = 12·5`
(`12` is super-m-Zumkeller, its exponents `2, 1` are not
`0 (mod 8)`, but `T(T(60))` has odd `3`-adic exponent `1911`,
so no equal-product partition of the divisors of `T(60)`
exists); Theorem 5 fails at `108 = 4·3^3`; Theorem 7 fails at
`n = 12`, which is `3`-m-perfect and super-m-Zumkeller although
its exponent of `2` is not `1 (mod 4)`.  Corollary 2 is stated
with the odd-prime reading its proof uses (`τ(n) = (k+1)2^r`
forces `2 ∉ {p_1, …, p_r}`); with `2` allowed among the `p_i` it
already fails at `60 = 2·(2·3·5)`.  Theorems 1 and 2 are
quantified over `n ≥ 2`, the paper's prime-factorization
context (under the subset encoding, `1` would vacuously be
super-m-Zumkeller with `τ(1) = 1`).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Factors
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.NumberTheory.Divisors

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.SuperMZumkellerWanted

/-- **Product of the divisors.** For a natural number $n$, $T(n)$ is the product of all positive
divisors of $n$. For $n = 0$ the set of divisors is taken to be empty, so $T(0) = 1$. -/
def divisorProd (n : ℕ) : ℕ := ∏ d ∈ n.divisors, d

/-- **Super-m-Zumkeller numbers.** For a natural number $n$, let $T(n)$ be the product of the
positive divisors of $n$ (for $n = 0$ the divisor set is taken to be empty, so $T(0) = 1$).
Then $n$ is *super-m-Zumkeller* if there is a set $A$ of positive divisors of $T(n)$ such that
the product of the elements of $A$ equals the product of the positive divisors of $T(n)$ that
are not in $A$; that is, the divisors of $T(n)$ split into two complementary sets, one of which
may be empty, with equal products. -/
def IsSuperMZumkeller (n : ℕ) : Prop :=
  ∃ A : Finset ℕ, A ⊆ (divisorProd n).divisors ∧
    (∏ d ∈ A, d) = ∏ d ∈ (divisorProd n).divisors \ A, d

/-- **$k$-m-perfect numbers.** For natural numbers $k$ and $n$, $n$ is $k$-m-perfect if
$T(n) = n^k$, where $T(n)$ is the product of the divisors of $n$. -/
def IsKMPerfect (k n : ℕ) : Prop := divisorProd n = n ^ k

/-- **Square of the product of the divisors.** For every positive integer $n$, let $T(n)$ be the
product of the positive divisors of $n$ and $\tau(n)$ their number. Then $T(n)^2 = n^{\tau(n)}$.

The paper writes this as $T(n) = n^{\tau(n)/2}$.

Source: Harish Patodia, "Super m-Zumkeller Numbers", Lemma 1. -/
theorem_wanted divisorProd_sq (n : ℕ) (hn : 0 < n) :
    (divisorProd n) ^ 2 = n ^ (n.divisors.card)

/-- **Super-m-Zumkeller numbers $n \ge 2$ have at least three divisors.** If a natural number
$n \ge 2$ is super-m-Zumkeller, then the number $\tau(n)$ of positive divisors of $n$ satisfies
$\tau(n) \ge 3$.

Source: Harish Patodia, "Super m-Zumkeller Numbers", Theorem 1. -/
theorem_wanted three_le_card_divisors_of_isSuperMZumkeller (n : ℕ)
    (hn : 2 ≤ n) (h : IsSuperMZumkeller n) :
    3 ≤ n.divisors.card

/-- **Criterion for super-m-Zumkeller numbers.** Let $n \ge 2$ be an integer, let $\tau(n)$ be the
number of positive divisors of $n$ and $T(n)$ their product. Then $n$ is super-m-Zumkeller if and
only if $8$ divides $\alpha \cdot \tau(n) \cdot \tau(T(n))$ for every prime $p$ dividing $n$,
where $\alpha$ is the exponent of $p$ in $n$.

Source: Harish Patodia, "Super m-Zumkeller Numbers", Theorem 2. -/
theorem_wanted isSuperMZumkeller_iff (n : ℕ) (hn : 2 ≤ n) :
    IsSuperMZumkeller n ↔
      ∀ p ∈ n.primeFactors,
        8 ∣ (n.factorization p) * n.divisors.card *
          (divisorProd n).divisors.card

/-- **Super-m-Zumkeller prime powers.** Let $p$ be a prime and $\alpha \ge 1$ an integer. Then
$p^\alpha$ is super-m-Zumkeller if and only if
$\alpha \equiv 0, 2, 5, 7, 8, 10, 13$ or $15 \pmod{16}$.

Source: Harish Patodia, "Super m-Zumkeller Numbers", Theorem 3. -/
theorem_wanted isSuperMZumkeller_prime_pow_iff (p : ℕ)
    (hp : p.Prime) (a : ℕ) (ha : 1 ≤ a) :
    IsSuperMZumkeller (p ^ a) ↔
      a % 16 ∈ ({0, 2, 5, 7, 8, 10, 13, 15} : Finset ℕ)

/-- **Products of at least three distinct primes are super-m-Zumkeller.** For every finite set
$S$ of at least three primes, the product $\prod_{p \in S} p$ is super-m-Zumkeller.

Source: Harish Patodia, "Super m-Zumkeller Numbers",
Corollary 1. -/
theorem_wanted isSuperMZumkeller_prod_primes (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) (hcard : 3 ≤ s.card) :
    IsSuperMZumkeller (∏ p ∈ s, p)

/-- **Odd powers of $2$ times two distinct odd primes are super-m-Zumkeller.** Let $k$ be an odd
natural number and let $p$ and $q$ be distinct odd primes. Then $2^k p q$ is super-m-Zumkeller.

The primes are required to be odd because the paper's proof uses that this number has
$(k+1) \cdot 2^2$ divisors.

Source: Harish Patodia, "Super m-Zumkeller Numbers",
Corollary 2. -/
theorem_wanted isSuperMZumkeller_two_pow_mul_two_primes (k : ℕ)
    (hk : Odd k) (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : p ≠ q) :
    IsSuperMZumkeller ((2 : ℕ) ^ k * (p * q))

/-- **Powers of $2$ times at least three distinct odd primes are super-m-Zumkeller.** Let $k$ be
a natural number and $S$ a finite set of at least three odd primes. Then $2^k \prod_{p \in S} p$
is super-m-Zumkeller.

The primes are required to be odd because the paper's proof uses that this number has
$(k+1)2^r$ divisors, where $r$ is the number of primes in $S$.

Source: Harish Patodia, "Super m-Zumkeller Numbers",
Corollary 2. -/
theorem_wanted isSuperMZumkeller_two_pow_mul_prod_primes (k : ℕ)
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (hs2 : 2 ∉ s)
    (hcard : 3 ≤ s.card) :
    IsSuperMZumkeller ((2 : ℕ) ^ k * ∏ p ∈ s, p)

/-- **$k$-m-perfect numbers with $k$ a positive multiple of $4$ are super-m-Zumkeller.** Let
$k \ge 2$ be a natural number with $k \equiv 0 \pmod 4$. Then every natural number that is
$k$-m-perfect is super-m-Zumkeller.

Source: Harish Patodia, "Super m-Zumkeller Numbers", Theorem 6. -/
theorem_wanted isSuperMZumkeller_of_isKMPerfect (k n : ℕ)
    (hk : 2 ≤ k) (hk4 : k % 4 = 0) (h : IsKMPerfect k n) :
    IsSuperMZumkeller n

/-- **$4$ is super-m-Zumkeller but not $k$-m-perfect for $k \ge 2$.** The number $4$ is
super-m-Zumkeller, and for no natural number $k \ge 2$ is $4$ a $k$-m-perfect number. This is the
paper's counterexample to the converse of Theorem 6.

Source: Harish Patodia, "Super m-Zumkeller Numbers", Theorem 6. -/
theorem_wanted isSuperMZumkeller_four_not_kmPerfect :
    IsSuperMZumkeller 4 ∧ ∀ k : ℕ, 2 ≤ k → ¬ IsKMPerfect k 4

end MathlibExt.NumberTheory.SuperMZumkellerWanted
