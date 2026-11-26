/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.InfiniteRieselRepintegers

/-! # Tests for infinitely many Riesel repintegers -/

namespace MathlibExtTest.NumberTheory.InfiniteRieselRepintegers

open MetaMathlibExt

private def covering : Finset (ℕ × ℕ × ℕ) :=
  {(0, 2, 3), (2, 3, 7), (1, 4, 5), (7, 8, 17), (7, 12, 13), (3, 24, 241)}

private theorem covering_509203 : IsRieselCoveringData 509203 covering := by
  refine ⟨?_, ?_, ?_⟩
  · have hcheck : ∀ j : Fin 24, ∃ s ∈ covering, s.2.1 ∣ 24 ∧
        (j.val : ℤ) ≡ (s.1 : ℤ) [ZMOD (s.2.1 : ℤ)] := by decide +kernel
    intro z
    have hnonneg : 0 ≤ z % 24 := Int.emod_nonneg _ (by decide)
    have hlt : z % 24 < 24 := Int.emod_lt_of_pos _ (by decide)
    let j : Fin 24 := ⟨(z % 24).toNat, by omega⟩
    obtain ⟨s, hs, hm, hr⟩ := hcheck j
    refine ⟨((s.1 : ℤ), s.2.1), Finset.mem_image_of_mem _ hs, ?_⟩
    have hred : z ≡ z % 24 [ZMOD 24] := by simp [Int.ModEq]
    have hdiv : (s.2.1 : ℤ) ∣ (24 : ℤ) := by exact_mod_cast hm
    have hj : (j.val : ℤ) = z % 24 := Int.toNat_of_nonneg hnonneg
    rw [hj] at hr
    exact (hred.of_dvd hdiv).trans hr
  · change ∀ x ∈ covering, ∀ y ∈ covering, x.2.2 = y.2.2 → x = y
    decide +kernel
  · decide +kernel

private theorem riesel_509203 : IsRieselNumber 509203 := by
  refine ⟨by decide, ?_⟩
  intro n _
  have hcheck : ∀ j : Fin 24, ∃ p ∈ [3, 7, 5, 17, 13, 241],
      2 ≤ p ∧ p ≤ 241 ∧ 2 ^ 24 ≡ 1 [MOD p] ∧ 509203 * 2 ^ j.val ≡ 1 [MOD p] := by decide
  obtain ⟨p, _, hp, hple, hperiod, hr⟩ := hcheck ⟨n % 24, Nat.mod_lt _ (by decide)⟩
  have hpow : 2 ^ n ≡ 2 ^ (n % 24) [MOD p] := by
    conv_lhs => rw [← Nat.mod_add_div n 24, pow_add, pow_mul]
    simpa only [one_pow, mul_one] using (hperiod.pow (n / 24)).mul_left (2 ^ (n % 24))
  have hdvd : p ∣ 509203 * 2 ^ n - 1 := ((hpow.mul_left 509203).trans hr).symm.dvd'
  have hle : 509203 ≤ 509203 * 2 ^ n := Nat.le_mul_of_pos_right _ (by positivity)
  exact Nat.not_prime_of_dvd_of_lt hdvd hp (by omega)

-- Base two repeats a block of more than one digit, and tests the minimum allowed base.
example : {t : ℕ | 1 ≤ t ∧ IsRieselNumber (repstring 2 509203 0 t)}.Infinite :=
  infinite_riesel_repintegers riesel_509203 covering_509203 le_rfl

-- In odd base three the theorem still gives odd Riesel repintegers, at unbounded lengths.
example (M : ℕ) : ∃ t : ℕ, M < t ∧ Odd (repstring 3 509203 0 t) ∧
    ¬ (repstring 3 509203 0 t * 2 - 1).Prime := by
  obtain ⟨t, ht, hMt⟩ := (infinite_riesel_repintegers (b := 3) riesel_509203 covering_509203
    (by decide)).exists_gt M
  exact ⟨t, hMt, ht.2.1, by simpa using ht.2.2 1 le_rfl⟩

end MathlibExtTest.NumberTheory.InfiniteRieselRepintegers
