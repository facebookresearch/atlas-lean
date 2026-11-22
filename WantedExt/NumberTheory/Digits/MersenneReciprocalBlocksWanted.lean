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

/-- Proposition 1: let `2^p - 1` be prime and let `p` divide the period `L` of `1/(2^p - 1)`;
with blocks of length `ℓ = L/p`, `10^ℓ ≡ 2^r (mod 2^p - 1)` for some `r ∈ {1, …, p - 1}`.

Source: Amitabha Tripathi, *A Note on the Decimal Expansion of Reciprocals of Mersenne Primes*,
INTEGERS 24 (2024), Article A14, Proposition 1 (`integers-2024-A14-prop-1`). -/
public theorem_wanted ten_pow_blockLength_modEq_two_pow (p : ℕ) (hM : (2 ^ p - 1).Prime)
    (hdvd : p ∣ orderOf (10 : ZMod (2 ^ p - 1))) :
    ∃ r ∈ Finset.Icc 1 (p - 1),
      10 ^ (orderOf (10 : ZMod (2 ^ p - 1)) / p) ≡ 2 ^ r [MOD 2 ^ p - 1]

/-- Theorem 1: let `2^p - 1` be prime, let `p` divide the period `L` of `1/(2^p - 1)`, cut the
repeating block into `p` blocks `B_1, …, B_p` of length `ℓ = L/p`, let `1 ≤ r ≤ p - 1` with
`10^ℓ ≡ 2^r (mod 2^p - 1)`, and let `s ≡ r^{-1} (mod p)`. With block subscripts taken modulo
`p` in `{1, …, p}`:
(i) `B_{ks+1} = 2B_{(k-1)s+1}` for `1 ≤ k ≤ p - 1`, `k ≠ p - r`; `B_{ks+1} = 2B_{(k-1)s+1} + 1`
for `k = p - r`; `B_{ks+1} = 2B_{(k-1)s+1} - 10^ℓ` for `k = p`; in particular, when `r = 1`,
`B_{k+1} = 2B_k` for `1 ≤ k ≤ p - 2`, `B_p = 2B_{p-1} + 1` and `B_1 = 2B_p - 10^ℓ`;
(ii) `B_1 + ⋯ + B_p = 10^ℓ - 1`.
The extraction prints `s ≡ r-1 (mod p)` with its superscripts flattened (as in `2p - 1` for
`2^p - 1` and `10ℓ` for `10^ℓ`); the reading `s ≡ r - 1` fails at `p = 3` (`r = 1`, `s = 0`).
`B` is extended to all natural indices by `B j = B_{((j - 1) mod p) + 1}`; the identities are in
`ℤ`.

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
