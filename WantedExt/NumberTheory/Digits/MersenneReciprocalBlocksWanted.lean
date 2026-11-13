/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Blocks in the decimal expansion of reciprocals of Mersenne primes (statements)

Statement-only targets from Amitabha Tripathi, *A Note on the Decimal Expansion of Reciprocals
of Mersenne Primes*. For a Mersenne prime `M = 2^p - 1` the expansion of `1/M` is purely
periodic (`gcd(10, M) = 1`) with period `L = ord_M(10)` = `orderOf (10 : ZMod M)`, and its
repeating block, read as an `L`-digit integer with leading zeros, is `(10^L - 1)/M`. When
`p ∣ L` the block is cut into `p` consecutive blocks of `ℓ = L/p` digits; the `k`-th block from
the left (`1 ≤ k ≤ p`) is `((10^L - 1)/M / 10^{ℓ(p-k)}) % 10^ℓ`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **The block-length power of ten is a power of two modulo the Mersenne prime.** Let $p$ be a
natural number such that $M = 2^p - 1$ is prime, let $L$ be the multiplicative order of $10$ modulo
$M$ (the period of the decimal expansion of $1/M$), and suppose that $p$ divides $L$. Then there is
a natural number $r$ with $1 \le r \le p - 1$ such that $10^{L/p} \equiv 2^r \pmod{M}$.

Source: Amitabha Tripathi, *A Note on the Decimal Expansion of Reciprocals of Mersenne Primes*,
INTEGERS 24 (2024), Article A14, Proposition 1 (`integers-2024-A14-prop-1`). -/
public theorem_wanted ten_pow_blockLength_modEq_two_pow (p : ℕ) (hM : (2 ^ p - 1).Prime)
    (hdvd : p ∣ orderOf (10 : ZMod (2 ^ p - 1))) :
    ∃ r ∈ Finset.Icc 1 (p - 1),
      10 ^ (orderOf (10 : ZMod (2 ^ p - 1)) / p) ≡ 2 ^ r [MOD 2 ^ p - 1]

/-- **Doubling recurrence for the blocks of $1/(2^p - 1)$.** Let $p$ be a natural number such
that $M = 2^p - 1$ is prime, let $L$ be the multiplicative order of $10$ modulo $M$ (the period of
the decimal expansion of $1/M$), and suppose that $p$ divides $L$. Put $\ell = L/p$ and let
$N = (10^L - 1)/M$ be the repeating block of $1/M$, read as an $L$-digit integer with leading
zeros. For $1 \le k \le p$ let $B_k = \lfloor N / 10^{\ell (p - k)} \rfloor \bmod 10^\ell$ be
the $k$-th block of $\ell$ digits of $N$ from the left, and extend the indices to all $j \ge 1$
by $B_j = B_k$ where $k = ((j - 1) \bmod p) + 1$. Let $r$ and $s$ be natural numbers with
$1 \le r \le p - 1$, $10^\ell \equiv 2^r \pmod{M}$ and $rs \equiv 1 \pmod{p}$. Then, as
integers:

(i) for every $k$ with $1 \le k \le p$, $B_{ks+1} = 2B_{(k-1)s+1} - 10^\ell$ if $k = p$,
$B_{ks+1} = 2B_{(k-1)s+1} + 1$ if $k = p - r$, and $B_{ks+1} = 2B_{(k-1)s+1}$ otherwise;

(ii) if $r = 1$, then for every $k$ with $1 \le k \le p$, $B_{k+1} = 2B_k - 10^\ell$ if $k = p$,
$B_{k+1} = 2B_k + 1$ if $k = p - 1$, and $B_{k+1} = 2B_k$ otherwise;

(iii) $B_1 + B_2 + \dots + B_p = 10^\ell - 1$.

Source: Amitabha Tripathi, *A Note on the Decimal Expansion of Reciprocals of Mersenne Primes*,
INTEGERS 24 (2024), Article A14, Theorem 1 (`integers-2024-A14-thm-1`). -/
public theorem_wanted mersenne_reciprocal_block_recurrence (p : ℕ) (hM : (2 ^ p - 1).Prime)
    (hdvd : p ∣ orderOf (10 : ZMod (2 ^ p - 1))) (r s : ℕ) (hr₁ : 1 ≤ r) (hr₂ : r ≤ p - 1)
    (hr : 10 ^ (orderOf (10 : ZMod (2 ^ p - 1)) / p) ≡ 2 ^ r [MOD 2 ^ p - 1])
    (hs : r * s ≡ 1 [MOD p]) :
    let L := orderOf (10 : ZMod (2 ^ p - 1))
    let ℓ := L / p
    let B : ℕ → ℤ := fun j =>
      (((10 ^ L - 1) / (2 ^ p - 1) / 10 ^ (ℓ * (p - ((j - 1) % p + 1)))) % 10 ^ ℓ : ℕ)
    (∀ k ∈ Finset.Icc 1 p,
      B (k * s + 1) =
        if k = p then 2 * B ((k - 1) * s + 1) - 10 ^ ℓ
        else if k = p - r then 2 * B ((k - 1) * s + 1) + 1
        else 2 * B ((k - 1) * s + 1)) ∧
    (r = 1 → ∀ k ∈ Finset.Icc 1 p,
      B (k + 1) =
        if k = p then 2 * B k - 10 ^ ℓ
        else if k = p - 1 then 2 * B k + 1
        else 2 * B k) ∧
    ∑ k ∈ Finset.Icc 1 p, B k = 10 ^ ℓ - 1

end

end MetaMathlibExt
