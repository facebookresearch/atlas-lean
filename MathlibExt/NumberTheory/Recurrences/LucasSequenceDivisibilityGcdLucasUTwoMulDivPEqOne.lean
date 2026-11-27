/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import MathlibExt.NumberTheory.LucasSequence
public import MathlibExt.NumberTheory.PrimitiveDivisor
public import MathlibExt.NumberTheory.Recurrences.LucasDiscriminantGcd
public import MathlibExt.NumberTheory.Recurrences.LucasParityDivisibility
public import MathlibExt.NumberTheory.Recurrences.LucasSequenceFirstKind
public import MathlibExt.NumberTheory.Recurrences.NondegenerateLucasPair
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Prime.Defs
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # Coprimality of `U_{2n} / P` and `P`

This module proves `gcd_lucasU_two_mul_div_p_eq_one`: for Lucas sequence parameters
`(P, Q)` with `gcd P Q = 1` and `P ≠ 0`, if `n` is a positive natural number with
`gcd n P = 1`, then `gcd (U_{2n} / P) P = 1`.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Lemma 2.6, "in particular" claim.
-/

namespace MetaMathlibExt

/-- **Recurrence for the even subsequence.** For Lucas sequence parameters `(P, Q)` and every
natural number `a`, `U_{a+4} = (P ^ 2 - 2 * Q) * U_{a+2} - Q ^ 2 * U_a`. -/
private theorem lucasU_even_add_four (L : LucasSequenceParams) (a : ℕ) :
    lucasU L (a + 4) = (L.p ^ 2 - 2 * L.q) * lucasU L (a + 2) - L.q ^ 2 * lucasU L a := by
  have r1 := lucasU_add_two L (a + 2)
  have r2 := lucasU_add_two L (a + 1)
  have r3 := lucasU_add_two L a
  rw [show a + 2 + 2 = a + 4 by omega, show a + 2 + 1 = a + 3 by omega] at r1
  rw [show a + 1 + 2 = a + 3 by omega, show a + 1 + 1 = a + 2 by omega] at r2
  linear_combination r1 + L.p * r2 + L.q * r3

/-- **The quotient `U_{2m+2} / P` modulo `P`.** For Lucas sequence parameters `(P, Q)` and every
natural number `m`, `P ^ 2` divides `U_{2 * m + 2} - P * ((-1) ^ m * (m + 1) * Q ^ m)`. -/
private theorem lucasU_two_mul_sub (L : LucasSequenceParams) (m : ℕ) :
    L.p ^ 2 ∣ lucasU L (2 * m + 2) -
      L.p * ((-1 : ℤ) ^ m * ((m + 1 : ℕ) : ℤ) * L.q ^ m) := by
  induction m using Nat.twoStepInduction with
  | zero =>
    rw [show 2 * 0 + 2 = 2 by omega, show lucasU L 2 = L.p by simp [lucasU]]
    simp
  | one =>
    rw [show 2 * 1 + 2 = 4 by omega]
    refine ⟨L.p, by simp only [lucasU, pow_one, Nat.cast_add, Nat.cast_one]; ring⟩
  | more n ih1 ih2 =>
    obtain ⟨s, hs⟩ := ih2
    obtain ⟨t, ht⟩ := ih1
    have hW := lucasU_even_add_four L (2 * n + 2)
    rw [show 2 * (n + 2) + 2 = 2 * n + 2 + 4 by omega]
    rw [show 2 * (n + 1) + 2 = 2 * n + 2 + 2 by omega] at hs
    have he : (-1 : ℤ) ^ (n + 2) * ((n + 2 + 1 : ℕ) : ℤ) * L.q ^ (n + 2) =
        -2 * L.q * ((-1 : ℤ) ^ (n + 1) * ((n + 1 + 1 : ℕ) : ℤ) * L.q ^ (n + 1)) -
          L.q ^ 2 * ((-1 : ℤ) ^ n * ((n + 1 : ℕ) : ℤ) * L.q ^ n) := by
      simp only [pow_add, Nat.cast_add, Nat.cast_one]
      ring
    refine ⟨lucasU L (2 * n + 2 + 2) - 2 * L.q * s - L.q ^ 2 * t, ?_⟩
    linear_combination hW - L.p * he - 2 * L.q * hs - L.q ^ 2 * ht

/-- **A common divisor of a coprime pair divides one.** If an integer divides two integers
with `Int.gcd` equal to `1`, then it divides `1`. -/
private theorem dvd_one_of_dvd_of_gcd_eq_one {d a b : ℤ} (hda : d ∣ a) (hdb : d ∣ b)
    (h : Int.gcd a b = 1) : d ∣ 1 := by
  have hsum : d ∣ a * Int.gcdA a b + b * Int.gcdB a b :=
    dvd_add (dvd_mul_of_dvd_left hda _) (dvd_mul_of_dvd_left hdb _)
  rw [← Int.gcd_eq_gcd_ab, h] at hsum
  simpa using hsum

/-- **Coprimality of $U_{2n}/P$ and $P$.** Let $P$ and $Q$ be integers with $Q \ne 0$, $P \ne 0$
and $\gcd(P, Q) = 1$, and let $(U_n)$ be the Lucas sequence $U(P, Q)$. If $n$ is a positive
integer with $\gcd(n, P) = 1$, then $\gcd(U_{2n}/P, P) = 1$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Lemma 2.6, "in particular" claim
(`integers-2025-A107-lem-2-6`). -/
public theorem gcd_lucasU_two_mul_div_p_eq_one
    (L : LucasSequenceParams) (hcop : Int.gcd L.p L.q = 1) (hP : L.p ≠ 0)
    (n : ℕ) (hn : 0 < n) (hnP : Int.gcd n L.p = 1) :
    Int.gcd (lucasU L (2 * n) / L.p) L.p = 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (by omega : n ≠ 0)
  have hdiv : L.p ∣ lucasU L (2 * (m + 1)) :=
    (p_dvd_lucasU_two_mul_and_lucasV_of_odd L).1 (m + 1)
  have hU : L.p * (lucasU L (2 * (m + 1)) / L.p) = lucasU L (2 * (m + 1)) :=
    Int.mul_ediv_cancel' hdiv
  have hcongr := lucasU_two_mul_sub L m
  rw [show 2 * m + 2 = 2 * (m + 1) by omega] at hcongr
  obtain ⟨T, hT⟩ := hcongr
  have hAP : L.p ∣ lucasU L (2 * (m + 1)) / L.p -
      (-1 : ℤ) ^ m * ((m + 1 : ℕ) : ℤ) * L.q ^ m := by
    refine ⟨T, ?_⟩
    have hcancel : L.p * (lucasU L (2 * (m + 1)) / L.p -
        (-1 : ℤ) ^ m * ((m + 1 : ℕ) : ℤ) * L.q ^ m) = L.p * (L.p * T) := by
      linear_combination hT + hU
    exact mul_left_cancel₀ hP hcancel
  have hnat : Nat.gcd (lucasU L (2 * (m + 1)) / L.p).natAbs L.p.natAbs = 1 := by
    rw [Nat.eq_one_iff_not_exists_prime_dvd]
    intro q hq hdivq
    have hqA : q ∣ (lucasU L (2 * (m + 1)) / L.p).natAbs :=
      dvd_trans hdivq (Nat.gcd_dvd_left _ _)
    have hqP : q ∣ L.p.natAbs := dvd_trans hdivq (Nat.gcd_dvd_right _ _)
    have hqA' : (q : ℤ) ∣ lucasU L (2 * (m + 1)) / L.p :=
      Int.dvd_natAbs.mp (by exact_mod_cast hqA)
    have hqP' : (q : ℤ) ∣ L.p := Int.dvd_natAbs.mp (by exact_mod_cast hqP)
    have hsub : (q : ℤ) ∣ lucasU L (2 * (m + 1)) / L.p -
        (-1 : ℤ) ^ m * ((m + 1 : ℕ) : ℤ) * L.q ^ m := dvd_trans hqP' hAP
    have he' : (q : ℤ) ∣ (-1 : ℤ) ^ m * ((m + 1 : ℕ) : ℤ) * L.q ^ m := by
      have h := dvd_sub hqA' hsub
      rwa [sub_sub_cancel] at h
    have hprime : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
    rcases hprime.dvd_mul.mp he' with h12 | hQ
    · rcases hprime.dvd_mul.mp h12 with hneg | hmn
      · have h1 : (q : ℤ) ∣ 1 := dvd_neg.mp (hprime.dvd_of_dvd_pow hneg)
        have h1nat : q ∣ 1 := by exact_mod_cast h1
        rw [Nat.dvd_one] at h1nat
        have hlt := hq.one_lt
        omega
      · have h1 : (q : ℤ) ∣ 1 := dvd_one_of_dvd_of_gcd_eq_one hmn hqP' hnP
        have h1nat : q ∣ 1 := by exact_mod_cast h1
        rw [Nat.dvd_one] at h1nat
        have hlt := hq.one_lt
        omega
    · have hqQ : (q : ℤ) ∣ L.q := hprime.dvd_of_dvd_pow hQ
      have h1 : (q : ℤ) ∣ 1 := dvd_one_of_dvd_of_gcd_eq_one hqP' hqQ hcop
      have h1nat : q ∣ 1 := by exact_mod_cast h1
      rw [Nat.dvd_one] at h1nat
      have hlt := hq.one_lt
      omega
  exact hnat

end MetaMathlibExt
