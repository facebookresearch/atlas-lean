/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.MultiplicativeTriangularAdditive

/-!
# Tests for Park's vanishing lemma

The indicator of the divisors of 3 realizes the hypotheses, including the nonzero value at 3.
-/

namespace MathlibExt.NumberTheory.ArithmeticFunction.MultiplicativeTriangularAdditiveWanted

private noncomputable def divisorIndicator : ArithmeticFunction ℂ :=
  ⟨fun n ↦ if n ∣ 3 then 1 else 0, rfl⟩

private theorem sum_eq_two_or_ge_four {n : ℕ} (hn : IsSumTwoPositiveTriangular n) :
    n = 2 ∨ 4 ≤ n := by
  obtain ⟨a, b, ha, hb, hab⟩ := hn
  have gap (k : ℕ) (hk : 1 ≤ k) : k * (k + 1) = 2 ∨ 6 ≤ k * (k + 1) := by
    obtain rfl | h := eq_or_lt_of_le hk
    · exact Or.inl rfl
    · exact Or.inr (Nat.mul_le_mul h (Nat.succ_le_succ h))
  rcases gap a ha with ha | ha <;> rcases gap b hb with hb | hb <;> omega

example (n : ℕ) (hlo : 4 ≤ n) (hhi : n ≤ 21) : divisorIndicator n = 0 := by
  apply multiplicative_additive_on_sum_two_triangular_zero_of_three_ne_zero divisorIndicator
    ?_ ?_ rfl one_ne_zero n hlo hhi
  · refine ⟨rfl, fun {a b} hab ↦ ?_⟩
    have h : a * b ∣ 3 ↔ a ∣ 3 ∧ b ∣ 3 :=
      ⟨fun hd ↦ ⟨dvd_trans (dvd_mul_right a b) hd, dvd_trans (dvd_mul_left b a) hd⟩,
       fun ⟨ha, hb⟩ ↦ hab.mul_dvd_of_dvd_of_dvd ha hb⟩
    by_cases ha : a ∣ 3 <;> by_cases hb : b ∣ 3 <;> simp [divisorIndicator, h, ha, hb]
  · intro a b ha hb
    have vanish (k : ℕ) (hk : k = 2 ∨ 4 ≤ k) : divisorIndicator k = 0 := by
      have h : ¬ k ∣ 3 := fun hd ↦ by
        rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h <;> omega
      simp [divisorIndicator, h]
    have ha' := sum_eq_two_or_ge_four ha
    have hb' := sum_eq_two_or_ge_four hb
    rw [vanish a ha', vanish b hb', vanish (a + b) (Or.inr (by omega)), add_zero]

end MathlibExt.NumberTheory.ArithmeticFunction.MultiplicativeTriangularAdditiveWanted
