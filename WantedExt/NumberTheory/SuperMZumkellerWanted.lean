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
this paper that are correct as printed are formalized, here or in
the modules this file imports;
`isSuperMZumkeller_prime_pow_iff` is proved in
`MathlibExt.NumberTheory.SuperMZumkellerIsSuperMZumkellerPrimePowIff`,
and `isSuperMZumkeller_prod_primes` is proved in
`MathlibExt.NumberTheory.SuperMZumkellerIsSuperMZumkellerProdPrimes`.

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
public import MathlibExt.NumberTheory.SuperMZumkeller
public import MathlibExt.NumberTheory.SuperMZumkellerFactorization
public import MathlibExt.NumberTheory.SuperMZumkellerIsSuperMZumkellerFourNotKmPerfect
public import MathlibExt.NumberTheory.SuperMZumkellerIsSuperMZumkellerOfIsKMPerfect
public import MathlibExt.NumberTheory.SuperMZumkellerIsSuperMZumkellerPrimePowIff
public import MathlibExt.NumberTheory.SuperMZumkellerIsSuperMZumkellerProdPrimes

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.SuperMZumkellerWanted

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

end MathlibExt.NumberTheory.SuperMZumkellerWanted
