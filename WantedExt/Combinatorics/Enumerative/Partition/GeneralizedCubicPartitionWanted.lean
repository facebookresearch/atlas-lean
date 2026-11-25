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
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Generalized cubic partition congruences for primes $p \equiv 5, 7 \pmod 8$.** Let $a_c(n)$
be the generalized cubic partition numbers, let $p$ be a prime with $p \equiv 5$ or
$p \equiv 7 \pmod 8$, and let $l$ be a natural number with $p \mid 8l + 3$. Then
$a_{p-4}(pn + l) \equiv 0 \pmod p$ for every natural number $n$.

The source assumes $0 \le l \le p - 1$; the statement for a larger $l$ follows from the one for
$l \bmod p$, which satisfies the same divisibility.

Source: Russelle Guadalupe, *A Note on Congruences for Generalized Cubic Partitions Modulo
Primes*, INTEGERS 25 (2025), Article A20, Theorem 2, Equation (9). -/
public theorem_wanted generalizedCubicPartitionCount_prime_five_seven_mod_eight {p : ℕ}
    (hp : p.Prime) (hp8 : p % 8 = 5 ∨ p % 8 = 7) {l : ℕ} (hdvd : p ∣ 8 * l + 3) (n : ℕ) :
    (p : ℤ) ∣ generalizedCubicPartitionCount (p - 4) (p * n + l)

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
