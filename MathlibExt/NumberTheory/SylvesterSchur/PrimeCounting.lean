/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic.IntervalCases

/-!
# Prime-counting estimates for Sylvester-Schur

This file contains the prime-counting estimates and the basic large-prime extraction
lemmas used in the Sylvester--Schur proof.
-/

@[expose] public section

namespace Nat.SylvesterSchur

open scoped BigOperators

open Finset Nat

/-! ### Prime-counting estimates -/

/-- **Negating the no-large-prime condition for $\binom{N}{r}$.** Let $N$ and $r$ be natural
numbers. If it is not the case that every prime dividing $\binom{N}{r}$ is at most $r$, then some
prime $p$ with $r < p$ divides $\binom{N}{r}$. -/
theorem exists_large_prime_dvd_choose_of_not_forall_prime_dvd_le {N r : ℕ}
    (hsmall : ¬ ∀ p : ℕ, p.Prime → p ∣ Nat.choose N r → p ≤ r) :
    ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
  by_contra h
  exact hsmall fun p hp hdvd => le_of_not_gt fun hgt => h ⟨p, hp, hgt, hdvd⟩

/-- **A prime divisor of $\binom{N}{r}$ above $r$ from an upper bound below the lower bound.**
Let $N$, $r$ and $U$ be natural numbers, and let $m = \max(N + 1 - r, 0)$. Suppose that
$\binom{N}{r} \le U$ whenever every prime dividing $\binom{N}{r}$ is at most $r$, and that
$U < m^r / r!$ as rational numbers. Then some prime $p$ with $r < p$ divides $\binom{N}{r}$.

The quotient $m^r / r!$ is the standard lower bound for $\binom{N}{r}$. -/
theorem exists_large_prime_dvd_choose_of_upper_lt_lower {N r U : ℕ}
    (hupper :
      (∀ p : ℕ, p.Prime → p ∣ Nat.choose N r → p ≤ r) → Nat.choose N r ≤ U)
    (hbound : (U : ℚ) < ((N + 1 - r : ℕ) ^ r : ℚ) / (r ! : ℚ)) :
    ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
  apply exists_large_prime_dvd_choose_of_not_forall_prime_dvd_le
  intro hsmall
  have hupper_q : ((Nat.choose N r : ℕ) : ℚ) ≤ (U : ℚ) := by
    exact_mod_cast hupper hsmall
  have hlower :
      ((N + 1 - r : ℕ) ^ r : ℚ) / (r ! : ℚ) ≤ ((Nat.choose N r : ℕ) : ℚ) :=
    Nat.pow_le_choose (α := ℚ) r N
  exact (not_lt_of_ge (hlower.trans hupper_q)) hbound

/-- **At most $r - 1$ primes up to $r$.** For every natural number $r \ge 2$, the number
$\pi(r)$ of primes $p \le r$ satisfies $\pi(r) \le r - 1$, since all such primes lie in
$\{2, \dots, r\}$. -/
theorem primeCounting_le_sub_one {r : ℕ} (hr : 2 ≤ r) :
    Nat.primeCounting r ≤ r - 1 := by
  rw [Nat.primeCounting, ← Nat.primesBelow_card_eq_primeCounting' (r + 1)]
  have hsubset :
      (r + 1).primesBelow ⊆ Finset.Icc 2 r := by
    intro p hp
    rw [Finset.mem_Icc]
    exact ⟨(Nat.prime_of_mem_primesBelow hp).two_le, by
      have hlt := Nat.lt_of_mem_primesBelow hp
      omega⟩
  exact (Finset.card_le_card hsubset).trans_eq (by rw [card_Icc]; omega)

/-- **At most $\lfloor r/2 \rfloor + 1$ primes up to $r$.** For every natural number $r$, the
number $\pi(r)$ of primes $p \le r$ satisfies $\pi(r) \le \lfloor r/2 \rfloor + 1$. -/
theorem primeCounting_le_half_add_one (r : ℕ) :
    Nat.primeCounting r ≤ r / 2 + 1 := by
  by_cases hr : r ≤ 1
  · have hz : Nat.primeCounting r = 0 := Nat.primeCounting_eq_zero_iff.mpr hr
    omega
  · have hr2 : 2 ≤ r := by omega
    have h :=
      Nat.primeCounting'_add_le (a := 2) (k := 3) (by decide) (by decide) (r - 2)
    have harg : 3 + (r - 2) = r + 1 := by omega
    have hpi3 : Nat.primeCounting' 3 = 1 := by decide
    have htot : Nat.totient 2 = 1 := by decide
    rw [harg, hpi3, htot, one_mul] at h
    change Nat.primeCounting' (r + 1) ≤ r / 2 + 1
    omega

/- An explicit prime-counting bound from residue classes modulo `30`.  Beyond the primes below
`31`, every prime is coprime to `30`, and Mathlib's `Nat.primeCounting'_add_le` counts at most
one residue-class block plus a tail. -/
private lemma primeCounting_le_mod_thirty (r : ℕ) :
    Nat.primeCounting r ≤ 10 + 8 * ((r - 30) / 30 + 1) := by
  by_cases hr : r ≤ 30
  · have hmono : Nat.primeCounting r ≤ Nat.primeCounting 30 :=
      Nat.monotone_primeCounting hr
    have hpi30 : Nat.primeCounting 30 = 10 := by decide
    omega
  · have h :=
      Nat.primeCounting'_add_le (a := 30) (k := 31) (by decide) (by decide) (r - 30)
    have harg : 31 + (r - 30) = r + 1 := by omega
    have hpi31 : Nat.primeCounting' 31 = 10 := by decide
    have htot : Nat.totient 30 = 8 := by decide
    rw [harg, hpi31, htot] at h
    change Nat.primeCounting' (r + 1) ≤ 10 + 8 * ((r - 30) / 30 + 1)
    exact h

/-- **Erdős's $3r/8$ prime-counting bound.** For every natural number $r \ge 38$, the number
$\pi(r)$ of primes $p \le r$ satisfies $\pi(r) \le \lfloor 3r/8 \rfloor$.

The infinite tail follows from the residue-class estimate modulo $30$; the range
$38 \le r < 91$ is checked directly. -/
theorem primeCounting_le_three_mul_div_eight {r : ℕ} (hr : 38 ≤ r) :
    Nat.primeCounting r ≤ 3 * r / 8 := by
  by_cases h91 : 91 ≤ r
  · exact (primeCounting_le_mod_thirty r).trans (by omega)
  · interval_cases r <;> decide +kernel

end Nat.SylvesterSchur
