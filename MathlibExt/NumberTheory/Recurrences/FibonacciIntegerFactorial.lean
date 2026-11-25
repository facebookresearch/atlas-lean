/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Nat.ModEq
public import MathlibExt.NumberTheory.PrimitiveDivisor
import MathlibExt.NumberTheory.Recurrences.FibonacciPrimeDivisibility

/-!
# Carmichael's congruence for Fibonacci numbers

A primitive prime divisor of the Fibonacci number at index `m > 12` is congruent to
`1` or `-1` modulo `m`.
-/

namespace MetaMathlibExt

/-- **Carmichael's congruence for primitive prime divisors of Fibonacci numbers.** Let $F_n$
denote the $n$-th Fibonacci number. For every natural number $m > 12$, every primitive prime
divisor $p$ of $F_m$ (a prime $p$ that divides $F_m$ but divides no $F_n$ with $0 < n < m$)
satisfies $p \equiv \pm 1 \pmod{m}$, that is, $p \equiv 1 \pmod{m}$ or $p + 1 \equiv 0 \pmod{m}$.

This is the congruence half of Carmichael's theorem; the existence of a primitive prime divisor
of $F_m$ for $m > 12$ is a separate statement.

Source: Florian Luca, *`F_4 F_5^6 F_7 F_8^4 F_9 F_{10}^2 F_{12}^5 F_{14} F_{15}^{-1}
F_{18} F_{24} F_{30} = 36!`*, INTEGERS 24 (2024), Article A72, Theorem 2
(Primitive Divisor Theorem, quoting R. D. Carmichael) (`integers-2024-A72-thm-2`). -/
public theorem primitive_prime_dvd_fib_modEq_one_or_neg_one {m p : ℕ} (hm : 12 < m)
    (hp : IntegerSequence.IsPrimitivePrimeDivisor (fun n => (Nat.fib n : ℤ)) m p) :
    p ≡ 1 [MOD m] ∨ p + 1 ≡ 0 [MOD m] := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hp.not_dvd_of_lt (s := 3) (by decide) (by omega) (by decide)
  have hp5 : p ≠ 5 := by
    rintro rfl
    exact hp.not_dvd_of_lt (s := 5) (by decide) (by omega) (by decide)
  -- Primitivity forces gcd(m, n) = m whenever p divides F_n.
  have dvd_index {n : ℕ} (hn : p ∣ Nat.fib n) : m ∣ n := by
    have hd : p ∣ Nat.fib (m.gcd n) := by
      rw [Nat.fib_gcd]
      exact Nat.dvd_gcd (Int.natCast_dvd_natCast.mp hp.dvd) hn
    have hle := hp.toIsPrimitiveDivisor.le_of_dvd
      (Nat.gcd_pos_of_pos_left n hp.one_le) (Int.natCast_dvd_natCast.mpr hd)
    exact Nat.gcd_eq_left_iff_dvd.mp (le_antisymm (Nat.gcd_le_left n hp.one_le) hle)
  have : Fact p.Prime := ⟨hp.prime⟩
  have h := dvd_index (fib_prime_dvd_fib_of_legendre_sub p hp5 (lt_of_le_of_ne hp.two_le hp2.symm))
  split at h
  · exact Or.inl ((Nat.modEq_iff_dvd' hp.prime.pos).mpr h).symm
  · exact Or.inr (Nat.modEq_zero_iff_dvd.mpr h)

end MetaMathlibExt
