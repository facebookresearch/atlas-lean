/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SZumkeller
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Algebra.Order.Ring.Abs

/-!
# Odd s-Zumkeller numbers are squares

Every odd s-Zumkeller number is a perfect square, as follows from the parity
of its divisor count.

Reference: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 7.
-/

namespace MetaMathlibExt

/-- **Odd s-Zumkeller numbers are perfect squares.** Every odd s-Zumkeller number is a perfect
square.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 7. -/
public theorem isSquare_of_isSZumkeller_odd (n : ℕ) (h : IsSZumkeller n) (ho : Odd n) :
    IsSquare n := by
  classical
  obtain ⟨A, hA, _, _, hbal⟩ := h
  have hsum : Even (∑ d ∈ n.properDivisors, d ^ 2) := by
    rw [← Finset.sum_sdiff (f := fun d : ℕ => d ^ 2) hA, ← hbal]
    exact ⟨_, rfl⟩
  have hcard : Even n.properDivisors.card := by
    have hfilter : {d ∈ n.properDivisors | Odd (d ^ 2)} = n.properDivisors :=
      Finset.filter_eq_self.mpr fun d hd =>
        (ho.of_dvd_nat (Nat.mem_properDivisors.mp hd).1).pow
    simpa only [hfilter] using (Finset.even_sum_iff_even_card_odd (fun d : ℕ => d ^ 2)).mp hsum
  have hn : n ≠ 0 := by
    rintro rfl
    simp at ho
  have hdiv : Odd n.divisors.card := by
    simpa only [← Nat.insert_self_properDivisors hn,
      Finset.card_insert_of_notMem Nat.self_notMem_properDivisors] using hcard.add_one
  rw [Nat.card_divisors hn] at hdiv
  apply Nat.isSquare_iff_even_factorization.mpr
  intro p hp
  by_cases hpn : p ∣ n
  · have hfactor : Odd (n.factorization p + 1) :=
      hdiv.of_dvd_nat (Finset.dvd_prod_of_mem (fun p => n.factorization p + 1)
        (Nat.mem_primeFactors.mpr ⟨hp, hpn, hn⟩))
    simpa only [Nat.odd_add_one, Nat.not_odd_iff_even] using hfactor
  · simp [Nat.factorization_eq_zero_of_not_dvd hpn]

end MetaMathlibExt
