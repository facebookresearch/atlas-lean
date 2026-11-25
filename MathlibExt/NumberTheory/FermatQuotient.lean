/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import Mathlib.FieldTheory.Finite.Basic
@[expose] public section

/-!
# Fermat quotient

This module defines the integer-valued Fermat quotient `q_p(a)` for a
prime modulus `p` and integer `a` coprime to `p`.
-/

namespace Int

/-- **Fermat quotient.** For a prime $p$ and an integer $a$ coprime to $p$, the Fermat quotient
is the integer $q_p(a) = (a^{p-1} - 1)/p$, where $/$ is integer division rounding down. The
division is exact, since $p$ divides $a^{p-1} - 1$ by Fermat's little theorem. -/
@[nolint unusedArguments]
def fermatQuotient (p : ℕ) (_hp : Nat.Prime p) (a : ℤ)
    (_ha : IsCoprime a (p : ℤ)) : ℤ :=
  (a ^ (p - 1) - 1) / (p : ℤ)

/-- **Formula for the Fermat quotient.** For a prime $p$ and an integer $a$ coprime to $p$, the
Fermat quotient satisfies $q_p(a) = (a^{p-1} - 1)/p$, where $/$ is integer division rounding
down. -/
theorem fermatQuotient_eq (p : ℕ) (hp : Nat.Prime p) (a : ℤ)
    (ha : IsCoprime a (p : ℤ)) :
    fermatQuotient p hp a ha = (a ^ (p - 1) - 1) / (p : ℤ) :=
  rfl

/-- **Fermat quotient times the prime.** For a prime $p$ and an integer $a$ coprime to $p$, the
Fermat quotient $q_p(a)$ satisfies $p \, q_p(a) = a^{p-1} - 1$. -/
theorem natCast_mul_fermatQuotient (p : ℕ) (hp : Nat.Prime p) (a : ℤ)
    (ha : IsCoprime a (p : ℤ)) :
    (p : ℤ) * fermatQuotient p hp a ha = a ^ (p - 1) - 1 := by
  unfold fermatQuotient
  exact Int.mul_ediv_cancel' (Int.prime_dvd_pow_sub_one hp ha)

end Int
