/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.Enumerative.Partition.GeneralizedCubicPartition

/-!
# Congruences for generalized cubic partitions modulo primes

Statements from Russelle Guadalupe, *A Note on Congruences for Generalized Cubic Partitions
Modulo Primes*, INTEGERS 25 (2025), Article A20.

A generalized cubic partition of `n` (Amdeberhan, Sellers, and Singh) is a partition of `n`
whose even parts may appear in `c ≥ 1` colors; `a_c(n)` counts them, with
`∑ a_c(n) qⁿ = 1/(f_1 f_2^{c-1})`, where `f_k = (q^k; q^k)_∞` is `qEulerProduct k`.
The imported `GeneralizedCubicPartition` module defines `a_c(n)` as the `n`th coefficient of
that quotient in `ℤ⟦X⟧` (the denominator has constant coefficient `1`, so it is a unit).
`c = 1` gives the partition function and `c = 2` Chan's cubic partitions.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Amdeberhan–Sellers–Singh congruences.** For every natural number $n$, the generalized
cubic partition numbers satisfy $a_3(7n + 4) \equiv 0 \pmod{7}$ and
$a_5(11n + 10) \equiv 0 \pmod{11}$.

Source: Russelle Guadalupe, *A Note on Congruences for Generalized Cubic Partitions Modulo
Primes*, INTEGERS 25 (2025), Article A20, Theorem 1 (quoting Amdeberhan, Sellers, and
Singh), Equations (1) and (2). -/
public theorem_wanted generalizedCubicPartitionCount_seven_eleven (n : ℕ) :
    (7 : ℤ) ∣ generalizedCubicPartitionCount 3 (7 * n + 4) ∧
      (11 : ℤ) ∣ generalizedCubicPartitionCount 5 (11 * n + 10)

/-- **Generalized cubic partition congruences modulo primes $p \ge 7$, $p \equiv 3, 7 \pmod 8$.**
Let $a_c(n)$ be the generalized cubic partition numbers and let $p \ge 7$ be a prime with
$p \equiv 3$ or $p \equiv 7 \pmod 8$. Then
$a_{p-6}\bigl(pn + 13(p^2 - 1)/24\bigr) \equiv 0 \pmod p$ for every natural number $n$.

Since $24 \mid p^2 - 1$, the shift $13(p^2 - 1)/24$ is a natural number.

Source: Russelle Guadalupe, *A Note on Congruences for Generalized Cubic Partitions Modulo
Primes*, INTEGERS 25 (2025), Article A20, Theorem 3, Equation (13). -/
public theorem_wanted generalizedCubicPartitionCount_prime_three_seven_mod_eight {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hp8 : p % 8 = 3 ∨ p % 8 = 7) (n : ℕ) :
    (p : ℤ) ∣ generalizedCubicPartitionCount (p - 6) (p * n + 13 * (p ^ 2 - 1) / 24)

end

end MetaMathlibExt
