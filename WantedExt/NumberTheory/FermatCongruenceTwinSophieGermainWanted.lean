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
public import MathlibExt.NumberTheory.FermatCongruenceTwinPrimes
public import MathlibExt.NumberTheory.SophieGermainChainFermatCongruence
public import MathlibExt.NumberTheory.SophieGermainChainLength
public import MathlibExt.NumberTheory.SophieGermainPrime
public import MathlibExt.NumberTheory.SophieGermainPrimeFermatCongruence

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

/-- **Alahmadi–Luca theorem on Carmichael numbers.** For every natural number $n$ and every odd
prime $p$, the number $2^n p + 1$ is not a Carmichael number.

Source: Takashi Agoh, *A Note on Fermat's Congruence*, INTEGERS 25 (2025), Article A31,
Theorem 3.2, quoting A. Alahmadi and F. Luca, C. R. Math. Acad. Sci. Paris 360 (2022)
(`integers-2025-A31-thm-3-2`). -/
public theorem_wanted not_isCarmichaelNumber_two_pow_mul_prime_add_one (n : ℕ) {p : ℕ}
    (hp : p.Prime) (hodd : Odd p) : ¬Nat.IsCarmichaelNumber (2 ^ n * p + 1)

end

end MetaMathlibExt
