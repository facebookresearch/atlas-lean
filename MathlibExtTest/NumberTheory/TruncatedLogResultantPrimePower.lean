/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.IntervalCases
import MathlibExt.NumberTheory.TruncatedLogResultantPrimePower

open MetaMathlibExt Polynomial

example : ¬ (5 : ℤ) ∣ truncatedLogResultantProduct 5 :=
  not_dvd_truncatedLogResultantProduct_of_prime_power (p := 5) (e := 1)
    (hp := by decide) (hp4 := by decide) (he := by decide)

example : ¬ (5 : ℤ) ∣ truncatedLogResultantProduct 25 :=
  not_dvd_truncatedLogResultantProduct_of_prime_power (p := 5) (e := 2)
    (hp := by decide) (hp4 := by decide) (he := by decide)

-- The even-power theorem also applies to primes congruent to 3 modulo 4.
example : ¬ (3 : ℤ) ∣ truncatedLogResultantProduct 9 :=
  not_dvd_truncatedLogResultantProduct_of_even_power (p := 3) (e := 1)
    (hp := by decide) (hp2 := by decide) (he := by decide)

example : ¬ (5 : ℤ) ∣ truncatedLogResultantProduct 625 :=
  not_dvd_truncatedLogResultantProduct_of_even_power (p := 5) (e := 2)
    (hp := by decide) (hp2 := by decide) (he := by decide)

-- Reducing the integer coefficients gives X^9; the geometric sum has degree 8
-- and constant coefficient 1. This computes the residue without either nondivisibility theorem.
example : (truncatedLogResultantProduct 9 : ZMod 3) = 1 := by
  let f : ℤ[X] := ∑ i ∈ Finset.range 9, (X : ℤ[X]) ^ i
  let g := scaledTruncatedLogPolynomial 9
  let φ := Int.castRingHom (ZMod 3)
  have hL : truncatedLogLcm 9 = 2520 := by
    rw [truncatedLogLcm.eq_def]
    decide
  have hm : g.map φ = X ^ 9 := by
    dsimp only [g]
    simp only [scaledTruncatedLogPolynomial.eq_def, hL, Polynomial.map_add, Polynomial.map_sum,
      Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, φ,
      Int.coe_castRingHom, Int.cast_natCast]
    rw [show (↑(2520 : ℕ) : ZMod 3) = 0 by decide, map_zero, zero_add, Finset.sum_eq_single 9]
    · rw [show (↑(2520 / 9 : ℕ) : ZMod 3) = 1 by decide, map_one, one_mul]
    · intro j hj hne
      have hz : (↑(2520 / j : ℕ) : ZMod 3) = 0 := by
        obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hj
        interval_cases j <;> first | contradiction | decide
      rw [hz, map_zero, zero_mul]
    · simp
  have hf : f.natDegree = 8 := by
    dsimp only [f]
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · apply Polynomial.natDegree_sum_le_of_forall_le
      intro i hi
      rw [natDegree_X_pow]
      exact Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    · simp [coeff_X_pow]
  have hg : g.natDegree = 9 := by
    apply le_antisymm _ (by simpa only [hm, natDegree_X_pow] using
      (natDegree_map_le (p := g) (f := φ)))
    dsimp only [g]
    rw [scaledTruncatedLogPolynomial.eq_def]
    refine (natDegree_add_le _ _).trans (max_le (by simp) ?_)
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    exact (natDegree_C_mul_le _ _).trans (by simpa using (Finset.mem_Icc.mp hi).2)
  have hc : (f.map φ).coeff 0 = 1 := by
    simp [f, coeff_X_pow]
  rw [truncatedLogResultantProduct.eq_def]
  change φ (f.resultant g f.natDegree g.natDegree) = 1
  rw [← resultant_map_map, hf, hg, hm,
    resultant_X_pow_right _ _ _ (hf ▸ natDegree_map_le), hc]
  decide
