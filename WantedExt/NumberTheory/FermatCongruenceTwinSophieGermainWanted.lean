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
public import MathlibExt.NumberTheory.FermatCongruenceCoprimeModuli
public import MathlibExt.NumberTheory.SophieGermainChainFermatCongruence
public import MathlibExt.NumberTheory.SophieGermainChainLength
public import MathlibExt.NumberTheory.SophieGermainPrime

/-!
# Fermat's congruence for twin and Sophie Germain primes

Statements from Takashi Agoh, *A Note on Fermat's Congruence*, INTEGERS 25 (2025),
Article A31. Carmichael numbers are `Nat.IsCarmichaelNumber` and Sophie Germain primes are
`Nat.IsSophieGermainPrime` (both from MathlibExt). The terms of the paper's chain
`q_1 = p`, `q_(j+1) = 2 q_j + 1` are written in closed form `q_(j+1) = 2 ^ j * (p + 1) - 1`.
Theorem 1.1 (a) is proved in `MathlibExt.NumberTheory.FermatCongruenceCoprimeModuli`: under
`gcd(n, m) = 1` the fraction `(a ^ (m - n) - 1) / (m - n)` of congruence (1.3) is read in
`ZMod (nm)`, where `m - n` is a unit. Parts (b) and (c) (`gcd(n, m) > 1`) are not stated, as the
paper does not fix the meaning of that fraction modulo `nm`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Fermat-type characterizations of twin primes.** Let $n \ge 3$ be odd, and suppose neither $n$
nor $n + 2$ is a Carmichael number. Then $n$ and $n + 2$ are both prime if and only if
$2a^{n+1} \equiv (n + 2)\,a^2 - n \pmod{n(n + 2)}$ for every integer $a$ coprime to $n(n + 2)$;
and $n$ and $n + 2$ are both prime if and only if
$n\,a^{n+1} \equiv (n + 2)\,a^{n-1} - 2 \pmod{n(n + 2)}$ for every integer $a$ coprime to
$n(n + 2)$.

Source: Takashi Agoh, *A Note on Fermat's Congruence*, INTEGERS 25 (2025), Article A31,
Theorem 3.1, Congruences (3.2) (`integers-2025-A31-thm-3-1`). -/
public theorem_wanted twinPrime_iff_forall_fermat_congruence {n : ℕ} (hodd : Odd n)
    (hn : 3 ≤ n) (hnc : ¬Nat.IsCarmichaelNumber n) (hn2c : ¬Nat.IsCarmichaelNumber (n + 2)) :
    ((n.Prime ∧ (n + 2).Prime) ↔ ∀ a : ℤ, IsCoprime a ((n : ℤ) * (n + 2)) →
        2 * a ^ (n + 1) ≡ (n + 2) * a ^ 2 - n [ZMOD (n : ℤ) * (n + 2)]) ∧
      ((n.Prime ∧ (n + 2).Prime) ↔ ∀ a : ℤ, IsCoprime a ((n : ℤ) * (n + 2)) →
        n * a ^ (n + 1) ≡ (n + 2) * a ^ (n - 1) - 2 [ZMOD (n : ℤ) * (n + 2)])

/-- **Alahmadi–Luca theorem on Carmichael numbers.** For every natural number $n$ and every odd
prime $p$, the number $2^n p + 1$ is not a Carmichael number.

Source: Takashi Agoh, *A Note on Fermat's Congruence*, INTEGERS 25 (2025), Article A31,
Theorem 3.2, quoting A. Alahmadi and F. Luca, C. R. Math. Acad. Sci. Paris 360 (2022)
(`integers-2025-A31-thm-3-2`). -/
public theorem_wanted not_isCarmichaelNumber_two_pow_mul_prime_add_one (n : ℕ) {p : ℕ}
    (hp : p.Prime) (hodd : Odd p) : ¬Nat.IsCarmichaelNumber (2 ^ n * p + 1)

/-- **Fermat-type characterizations of Sophie Germain primes.** Let $p$ be a prime. Then $p$ is a
Sophie Germain prime if and only if $a^{2p} \equiv (2p + 1)\,a^{p+1} - 2p \pmod{p(2p + 1)}$ for
every integer $a$ coprime to $p(2p + 1)$; and $p$ is a Sophie Germain prime if and only if
$(2p + 1)\,a^{p-1} \equiv p\,a^{2p} + p + 1 \pmod{p(2p + 1)}$ for every integer $a$ coprime to
$p(2p + 1)$.

Source: Takashi Agoh, *A Note on Fermat's Congruence*, INTEGERS 25 (2025), Article A31,
Theorem 3.3, Congruences (3.5) (`integers-2025-A31-thm-3-3`). -/
public theorem_wanted isSophieGermainPrime_iff_forall_fermat_congruence {p : ℕ}
    (hp : p.Prime) :
    (Nat.IsSophieGermainPrime p ↔ ∀ a : ℤ, IsCoprime a ((p : ℤ) * (2 * p + 1)) →
        a ^ (2 * p) ≡ (2 * p + 1) * a ^ (p + 1) - 2 * p [ZMOD (p : ℤ) * (2 * p + 1)]) ∧
      (Nat.IsSophieGermainPrime p ↔ ∀ a : ℤ, IsCoprime a ((p : ℤ) * (2 * p + 1)) →
        (2 * p + 1) * a ^ (p - 1) ≡ p * a ^ (2 * p) + p + 1 [ZMOD (p : ℤ) * (2 * p + 1)])

end

end MetaMathlibExt
