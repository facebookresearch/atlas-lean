/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Algebra.Order.Ring.Abs
import MathlibExt.NumberTheory.UnitaryDivisorCount
public import Mathlib.Algebra.Ring.Parity
public import MathlibExt.NumberTheory.SZumkeller

/-!
# No odd unitary s-Zumkeller numbers

There is no odd unitary s-Zumkeller number. The number `1` has no proper unitary
divisors, so it has no split into two nonempty parts, which `IsUnitarySZumkeller`
requires. For odd `n > 1`, the squares of the proper unitary divisors are odd and
odd in number, so their sum is odd and cannot split into two equal parts.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 13.
-/

namespace MetaMathlibExt

-- The full divisor is a unitary divisor of a nonzero number.
private theorem self_mem_unitaryDivisors {n : ℕ} (hn : n ≠ 0) :
    n ∈ Nat.unitaryDivisors n := by
  refine Nat.mem_unitaryDivisors.mpr ⟨dvd_rfl, hn, ?_⟩
  rw [Nat.div_self (Nat.pos_of_ne_zero hn)]
  exact Nat.coprime_one_right n

-- An odd `n > 1` has an odd number of proper unitary divisors.
private theorem odd_card_erase_unitaryDivisors {n : ℕ} (ho : Odd n) (hn : 1 < n) :
    Odd ((Nat.unitaryDivisors n).erase n).card := by
  have hn0 : n ≠ 0 := by obtain ⟨k, hk⟩ := ho; omega
  have hcard := card_unitaryDivisors n hn0
  have hkpos : 0 < n.primeFactors.card :=
    Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr hn)
  have hEven : Even (Nat.unitaryDivisors n).card := by
    rw [hcard, even_iff_two_dvd]
    exact dvd_pow_self 2 (by omega)
  have hcard0 : (Nat.unitaryDivisors n).card ≠ 0 := by
    rw [hcard]
    exact pow_ne_zero _ (by decide)
  rw [Finset.card_erase_of_mem (self_mem_unitaryDivisors hn0)]
  obtain ⟨t, ht⟩ := hEven
  exact ⟨t - 1, by omega⟩

/-- There is no odd unitary s-Zumkeller number.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 13. -/
public theorem not_isUnitarySZumkeller_of_odd (n : ℕ) (ho : Odd n) :
    ¬ IsUnitarySZumkeller n := by
  intro h
  by_cases hn1 : n = 1
  · subst hn1
    have h1 : ¬ IsUnitarySZumkeller 1 := by
      unfold IsUnitarySZumkeller
      decide
    exact h1 h
  · obtain ⟨A, hA, _, _, hbal⟩ := h
    have hlt : 1 < n := by obtain ⟨k, hk⟩ := ho; omega
    have hOddCard := odd_card_erase_unitaryDivisors ho hlt
    have hall : ∀ d ∈ (Nat.unitaryDivisors n).erase n, Odd (d ^ 2) :=
      fun d hd => (Odd.of_dvd_nat ho
        (Nat.dvd_of_mem_unitaryDivisors (Finset.mem_of_mem_erase hd))).pow
    have hOddSum : Odd (∑ d ∈ (Nat.unitaryDivisors n).erase n, d ^ 2) := by
      rw [Finset.odd_sum_iff_odd_card_odd]
      simpa only [Finset.filter_true_of_mem hall] using hOddCard
    have hEvenSum : Even (∑ d ∈ (Nat.unitaryDivisors n).erase n, d ^ 2) := by
      have hsum := Finset.sum_sdiff (f := fun d : ℕ => d ^ 2) hA
      exact ⟨∑ d ∈ A, d ^ 2, by omega⟩
    exact (Nat.not_even_iff_odd.mpr hOddSum) hEvenSum

end MetaMathlibExt
