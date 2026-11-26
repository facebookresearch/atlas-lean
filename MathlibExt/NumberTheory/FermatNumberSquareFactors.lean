/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.NumberTheory.Fermat
public import MathlibExt.NumberTheory.WieferichPrime
import MathlibExt.NumberTheory.FermatNumbersModPrime
import MathlibExt.NumberTheory.GeneralizedFermatWieferich

/-!
# Squared prime factors of Fermat numbers

The square of a prime divisor of a Fermat number divides that Fermat number exactly when
the prime satisfies the base-two Wieferich congruence.
-/

namespace MetaMathlibExt

/-- **Squared prime factors of Fermat numbers.** Let $F_n = 2^{2^n} + 1$ be the $n$-th Fermat
number, and let $p$ be a prime dividing $F_n$. Then $p^2$ divides $F_n$ if and only if
$2^{p-1} \equiv 1 \pmod{p^2}$.

Source: Klaška, *Several Notes on Jakóbczyk's Hypothesis on Fermat Numbers*,
INTEGERS 26 (2026), Article A77, Theorem 3 (`integers-2026-A77-thm-3`), citing
Křížek, Luca, and Somer. -/
public theorem sq_dvd_fermatNumber_iff {n p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ Nat.fermatNumber n) :
    p ^ 2 ∣ Nat.fermatNumber n ↔ 2 ^ (p - 1) ≡ 1 [MOD p ^ 2] := by
  have hp2 : p ≠ 2 := fun h => (Nat.odd_fermatNumber n).not_two_dvd_nat (h ▸ hdvd)
  have hcop : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  have horder := (prime_dvd_fermatNumber_iff_orderOf_two n p hp hp2).mp hdvd
  simpa only [Nat.fermatNumber, Nat.cast_ofNat, horder, and_true] using
    sq_dvd_pow_two_pow_add_one_iff_wieferich (n := n) hp hp2 hcop

/-- **Squared prime factors of Fermat numbers via Wieferich primes and orders.** Let
$F_n = 2^{2^n} + 1$ be the $n$-th Fermat number. For every natural number $n$ and every odd prime
$p$, $p^2$ divides $F_n$ if and only if $p$ is a Wieferich prime (to base $2$) and the
multiplicative order of $2$ modulo $p$ is $2^{n+1}$.

This follows from the criterion that a prime $p$ dividing $F_n$ satisfies $p^2 \mid F_n$ exactly
when $2^{p-1} \equiv 1 \pmod{p^2}$, since an odd prime $p$ divides $F_n$ exactly when the order
of $2$ modulo $p$ is $2^{n+1}$.

Source: Klaška, *Several Notes on Jakóbczyk's Hypothesis on Fermat Numbers*,
INTEGERS 26 (2026), Article A77, Theorem 5, Equation (11)
(`integers-2026-A77-thm-5`). -/
public theorem sq_dvd_fermatNumber_iff_wieferich_orderOf {n p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) :
    p ^ 2 ∣ Nat.fermatNumber n ↔ p.IsWieferichPrime ∧ orderOf (2 : ZMod p) = 2 ^ (n + 1) := by
  have hcop : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  simpa only [Nat.fermatNumber, Nat.isWieferichPrime_iff_modEq, hp, true_and, Nat.cast_ofNat] using
    sq_dvd_pow_two_pow_add_one_iff_wieferich (a := 2) (n := n) hp hp2 hcop

end MetaMathlibExt
