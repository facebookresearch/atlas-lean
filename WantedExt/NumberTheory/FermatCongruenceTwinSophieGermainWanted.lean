/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.RingTheory.Coprime.Basic
public import MathlibExt.NumberTheory.CarmichaelNumber
public import MathlibExt.NumberTheory.SophieGermainPrime

/-!
# Fermat's congruence for twin and Sophie Germain primes

Statements from Takashi Agoh, *A Note on Fermat's Congruence*, INTEGERS 25 (2025),
Article A31. Carmichael numbers are `Nat.IsCarmichaelNumber` and Sophie Germain primes are
`Nat.IsSophieGermainPrime` (both from MathlibExt). The terms of the paper's chain
`q_1 = p`, `q_(j+1) = 2 q_j + 1` are written in closed form `q_(j+1) = 2 ^ j * (p + 1) - 1`.
Theorem 1.1 is stated for part (a) only: under `gcd(n, m) = 1` the fraction
`(a ^ (m - n) - 1) / (m - n)` of congruence (1.3) is read in `ZMod (nm)`, where `m - n` is a
unit; for parts (b) and (c) (`gcd(n, m) > 1`) the paper does not fix its meaning modulo `nm`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- Let `n ≥ 3` be odd with neither `n` nor `n + 2` a Carmichael number. Then `(n, n + 2)`
is a twin prime pair if and only if `2 a ^ (n + 1) ≡ (n + 2) a ^ 2 - n (mod n (n + 2))` for
every integer `a` coprime to `n (n + 2)`, and also if and only if
`n a ^ (n + 1) ≡ (n + 2) a ^ (n - 1) - 2 (mod n (n + 2))` for every such `a`.

Source: Takashi Agoh, *A Note on Fermat's Congruence*, INTEGERS 25 (2025), Article A31,
Theorem 3.1, Congruences (3.2) (`integers-2025-A31-thm-3-1`). -/
public theorem_wanted twinPrime_iff_forall_fermat_congruence {n : ℕ} (hodd : Odd n)
    (hn : 3 ≤ n) (hnc : ¬Nat.IsCarmichaelNumber n) (hn2c : ¬Nat.IsCarmichaelNumber (n + 2)) :
    ((n.Prime ∧ (n + 2).Prime) ↔ ∀ a : ℤ, IsCoprime a ((n : ℤ) * (n + 2)) →
        2 * a ^ (n + 1) ≡ (n + 2) * a ^ 2 - n [ZMOD (n : ℤ) * (n + 2)]) ∧
      ((n.Prime ∧ (n + 2).Prime) ↔ ∀ a : ℤ, IsCoprime a ((n : ℤ) * (n + 2)) →
        n * a ^ (n + 1) ≡ (n + 2) * a ^ (n - 1) - 2 [ZMOD (n : ℤ) * (n + 2)])

/-- **Alahmadi–Luca.** For every `n ≥ 0` and every odd prime `p`, the number `2 ^ n * p + 1`
is not a Carmichael number.

Source: Takashi Agoh, *A Note on Fermat's Congruence*, INTEGERS 25 (2025), Article A31,
Theorem 3.2, quoting A. Alahmadi and F. Luca, C. R. Math. Acad. Sci. Paris 360 (2022)
(`integers-2025-A31-thm-3-2`). -/
public theorem_wanted not_isCarmichaelNumber_two_pow_mul_prime_add_one (n : ℕ) {p : ℕ}
    (hp : p.Prime) (hodd : Odd p) : ¬Nat.IsCarmichaelNumber (2 ^ n * p + 1)

/-- A prime `p` is a Sophie Germain prime if and only if
`a ^ (2p) ≡ (2p + 1) a ^ (p + 1) - 2p (mod p (2p + 1))` for every integer `a` coprime to
`p (2p + 1)`, and also if and only if
`(2p + 1) a ^ (p - 1) ≡ p a ^ (2p) + p + 1 (mod p (2p + 1))` for every such `a`.

Source: Takashi Agoh, *A Note on Fermat's Congruence*, INTEGERS 25 (2025), Article A31,
Theorem 3.3, Congruences (3.5) (`integers-2025-A31-thm-3-3`). -/
public theorem_wanted isSophieGermainPrime_iff_forall_fermat_congruence {p : ℕ}
    (hp : p.Prime) :
    (Nat.IsSophieGermainPrime p ↔ ∀ a : ℤ, IsCoprime a ((p : ℤ) * (2 * p + 1)) →
        a ^ (2 * p) ≡ (2 * p + 1) * a ^ (p + 1) - 2 * p [ZMOD (p : ℤ) * (2 * p + 1)]) ∧
      (Nat.IsSophieGermainPrime p ↔ ∀ a : ℤ, IsCoprime a ((p : ℤ) * (2 * p + 1)) →
        (2 * p + 1) * a ^ (p - 1) ≡ p * a ^ (2 * p) + p + 1 [ZMOD (p : ℤ) * (2 * p + 1)])

/-- In a Sophie Germain prime chain `q_1 = p`, `q_(i+1) = 2 q_i + 1 = 2 ^ i * (p + 1) - 1`
whose first `j + 2` terms are prime, the consecutive primes `q = q_(j+1)` and
`q' = q_(j+2) = 2q + 1` satisfy, for every integer `a` coprime to `q q'`,
`a ^ (q' - 1) ≡ q' a ^ (q + 1) - 2q` and `q' a ^ (q - 1) ≡ q a ^ (q' - 1) + q + 1`
modulo `q q'`.

Source: Takashi Agoh, *A Note on Fermat's Congruence*, INTEGERS 25 (2025), Article A31,
Corollary 3.4, Congruences (3.8) (`integers-2025-A31-cor-3-4`). -/
public theorem_wanted sophieGermainChain_fermat_congruence {p j : ℕ}
    (hchain : ∀ i ≤ j + 1, (2 ^ i * (p + 1) - 1).Prime) (a : ℤ) :
    let q : ℕ := 2 ^ j * (p + 1) - 1
    let q' : ℕ := 2 ^ (j + 1) * (p + 1) - 1
    IsCoprime a ((q : ℤ) * q') →
      a ^ (q' - 1) ≡ q' * a ^ (q + 1) - 2 * q [ZMOD (q : ℤ) * q'] ∧
        q' * a ^ (q - 1) ≡ q * a ^ (q' - 1) + q + 1 [ZMOD (q : ℤ) * q']

/-- For an odd prime `p`, the Sophie Germain prime chain
`q_(j+1) = 2 ^ j * (p + 1) - 1` starting at `p` has length at most `ord_p(2)`: some term
`q_(j+1)` with `j ≤ ord_p(2)` is not prime.

Source: Takashi Agoh, *A Note on Fermat's Congruence*, INTEGERS 25 (2025), Article A31,
Theorem 3.5, quoting T. Agoh, Tatra Mt. Math. Publ. 20 (2000), Proposition 3.1
(`integers-2025-A31-thm-3-5`). -/
public theorem_wanted sophieGermainChain_length_le_orderOf_two {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) :
    ∃ j ≤ orderOf (2 : ZMod p), ¬(2 ^ j * (p + 1) - 1).Prime

/-- Theorem 1.1 (a): for coprime `0 < n < m`, congruence (1.3),
`a ^ (m - 1) ≡ (a ^ (m - n) - 1)/(m - n) · n + a ^ (m - n) ≡ (a ^ (m - n) - 1)/(m - n) · m + 1
(mod nm)`, holds for every integer `a` coprime to `nm` if and only if both `n` and `m` have the
Fermat property (`a ^ (k - 1) ≡ 1 (mod k)` for every `a` coprime to `k`). Since
`gcd(m - n, nm) = 1` when `gcd(n, m) = 1`, the division by `m - n` is read as multiplication by
the inverse of `m - n` in `ZMod (nm)`. The order `n < m` follows the paper's proof (for `m < n`
the exponent `m - n` is negative). Parts (b) and (c), about `gcd(n, m) > 1`, are not stated: there
`m - n` need not be invertible modulo `nm` and the paper does not say what the fraction means.

Source: Takashi Agoh, *A Note on Fermat's Congruence*, INTEGERS 25 (2025), Article A31,
Theorem 1.1 (a) (`integers-2025-A31-thm-1-1`). -/
public theorem_wanted forall_fermat_congruence_iff_of_coprime {n m : ℕ} (hn : 0 < n)
    (hnm : n < m) (hcop : Nat.Coprime n m) :
    (∀ a : ℤ, IsCoprime a ((n : ℤ) * m) →
        ((a : ZMod (n * m)) ^ (m - 1) =
            ((a : ZMod (n * m)) ^ (m - n) - 1) * ((m - n : ℕ) : ZMod (n * m))⁻¹ * n +
              (a : ZMod (n * m)) ^ (m - n) ∧
          ((a : ZMod (n * m)) ^ (m - n) - 1) * ((m - n : ℕ) : ZMod (n * m))⁻¹ * n +
              (a : ZMod (n * m)) ^ (m - n) =
            ((a : ZMod (n * m)) ^ (m - n) - 1) * ((m - n : ℕ) : ZMod (n * m))⁻¹ * m + 1)) ↔
      (∀ a : ℤ, IsCoprime a (n : ℤ) → a ^ (n - 1) ≡ 1 [ZMOD n]) ∧
        (∀ a : ℤ, IsCoprime a (m : ℤ) → a ^ (m - 1) ≡ 1 [ZMOD m])

end

end MetaMathlibExt
