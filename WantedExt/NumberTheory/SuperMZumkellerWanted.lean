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

/-- `T(n)`, the product of all positive divisors of `n`. -/
def divisorProd (n : ℕ) : ℕ := ∏ d ∈ n.divisors, d

/-- `n` is *super-m-Zumkeller* if the set of positive divisors
of `T(n)` can be partitioned into two disjoint subsets with
equal products. -/
def IsSuperMZumkeller (n : ℕ) : Prop :=
  ∃ A : Finset ℕ, A ⊆ (divisorProd n).divisors ∧
    (∏ d ∈ A, d) = ∏ d ∈ (divisorProd n).divisors \ A, d

/-- `n` is *`k`-m-perfect* if `T(n) = n^k`. -/
def IsKMPerfect (k n : ℕ) : Prop := divisorProd n = n ^ k

/-- **Lemma 1**: `T(n)^2 = n^{τ(n)}` (the paper writes
`T(n) = n^{τ(n)/2}`).

Source: Harish Patodia, "Super m-Zumkeller Numbers", Lemma 1. -/
theorem_wanted divisorProd_sq (n : ℕ) (hn : 0 < n) :
    (divisorProd n) ^ 2 = n ^ (n.divisors.card)

/-- **Theorem 1**: a super-m-Zumkeller number `n ≥ 2` satisfies
`τ(n) ≥ 3`.

Source: Harish Patodia, "Super m-Zumkeller Numbers", Theorem 1. -/
theorem_wanted three_le_card_divisors_of_isSuperMZumkeller (n : ℕ)
    (hn : 2 ≤ n) (h : IsSuperMZumkeller n) :
    3 ≤ n.divisors.card

/-- **Theorem 2**: for `n ≥ 2`, `n` is super-m-Zumkeller if and
only if `8 ∣ α_i·τ(n)·τ(T(n))` for every prime exponent `α_i`
of `n`.

Source: Harish Patodia, "Super m-Zumkeller Numbers", Theorem 2. -/
theorem_wanted isSuperMZumkeller_iff (n : ℕ) (hn : 2 ≤ n) :
    IsSuperMZumkeller n ↔
      ∀ p ∈ n.primeFactors,
        8 ∣ (n.factorization p) * n.divisors.card *
          (divisorProd n).divisors.card

/-- **Theorem 3**: for prime `p` and `α ≥ 1`, `p^α` is
super-m-Zumkeller if and only if
`α ≡ 0, 2, 5, 7, 8, 10, 13, or 15 (mod 16)`.

Source: Harish Patodia, "Super m-Zumkeller Numbers", Theorem 3. -/
theorem_wanted isSuperMZumkeller_prime_pow_iff (p : ℕ)
    (hp : p.Prime) (a : ℕ) (ha : 1 ≤ a) :
    IsSuperMZumkeller (p ^ a) ↔
      a % 16 ∈ ({0, 2, 5, 7, 8, 10, 13, 15} : Finset ℕ)

/-- **Corollary 1**: the product of `r ≥ 3` distinct primes is
always super-m-Zumkeller.

Source: Harish Patodia, "Super m-Zumkeller Numbers",
Corollary 1. -/
theorem_wanted isSuperMZumkeller_prod_primes (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) (hcard : 3 ≤ s.card) :
    IsSuperMZumkeller (∏ p ∈ s, p)

/-- **Corollary 2 (i)**: `2^k·p·q` with `p, q` distinct odd
primes and `k` an odd positive integer is super-m-Zumkeller
(the proof's `τ(n) = (k+1)2^r` forces the `p_i` to be odd).

Source: Harish Patodia, "Super m-Zumkeller Numbers",
Corollary 2. -/
theorem_wanted isSuperMZumkeller_two_pow_mul_two_primes (k : ℕ)
    (hk : Odd k) (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : p ≠ q) :
    IsSuperMZumkeller ((2 : ℕ) ^ k * (p * q))

/-- **Corollary 2 (ii)**: `2^k·(product of `r ≥ 3` distinct
odd primes)` is super-m-Zumkeller for every `k` (the proof's
`τ(n) = (k+1)2^r` forces the `p_i` to be odd).

Source: Harish Patodia, "Super m-Zumkeller Numbers",
Corollary 2. -/
theorem_wanted isSuperMZumkeller_two_pow_mul_prod_primes (k : ℕ)
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (hs2 : 2 ∉ s)
    (hcard : 3 ≤ s.card) :
    IsSuperMZumkeller ((2 : ℕ) ^ k * ∏ p ∈ s, p)

/-- **Theorem 6**: every `k`-m-perfect number with `k ≥ 2` and
`k ≡ 0 (mod 4)` is super-m-Zumkeller.

Source: Harish Patodia, "Super m-Zumkeller Numbers", Theorem 6. -/
theorem_wanted isSuperMZumkeller_of_isKMPerfect (k n : ℕ)
    (hk : 2 ≤ k) (hk4 : k % 4 = 0) (h : IsKMPerfect k n) :
    IsSuperMZumkeller n

/-- **Theorem 6, failure of the converse**: `4` is
super-m-Zumkeller but is not `k`-m-perfect for any `k ≥ 2`
(the paper's counterexample).

Source: Harish Patodia, "Super m-Zumkeller Numbers", Theorem 6. -/
theorem_wanted isSuperMZumkeller_four_not_kmPerfect :
    IsSuperMZumkeller 4 ∧ ∀ k : ℕ, 2 ≤ k → ¬ IsKMPerfect k 4

end MathlibExt.NumberTheory.SuperMZumkellerWanted
