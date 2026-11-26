/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.MultiplicativeTriangularAdditive

/-!
# Tests for Park's identity and vanishing lemmas

The indicators of the divisors of 3 and 5 realize the two possible nonzero exceptional values.
The indicator of the divisors of 1 realizes vanishing throughout the interval. The identity
arithmetic function realizes the case with nonzero value at 2.
-/

namespace MathlibExt.NumberTheory.ArithmeticFunction.MultiplicativeTriangularAdditiveWanted

private noncomputable def divisorIndicator (p : ℕ) [NeZero p] : ArithmeticFunction ℂ :=
  ⟨fun n ↦ if n ∣ p then 1 else 0, by simp [NeZero.ne p]⟩

private theorem divisorIndicator_multiplicative (p : ℕ) [NeZero p] :
    (divisorIndicator p).IsMultiplicative := by
  refine ⟨by simp [divisorIndicator], fun {a b} hab ↦ ?_⟩
  have h : a * b ∣ p ↔ a ∣ p ∧ b ∣ p :=
    ⟨fun hd ↦ ⟨dvd_trans (dvd_mul_right a b) hd, dvd_trans (dvd_mul_left b a) hd⟩,
     fun ⟨ha, hb⟩ ↦ hab.mul_dvd_of_dvd_of_dvd ha hb⟩
  by_cases ha : a ∣ p <;> by_cases hb : b ∣ p <;> simp [divisorIndicator, h, ha, hb]

private theorem small_triangular_sums {n : ℕ} (hn : IsSumTwoPositiveTriangular n) :
    n = 2 ∨ n = 4 ∨ 6 ≤ n := by
  obtain ⟨a, b, ha, hb, hab⟩ := hn
  have gap (k : ℕ) (hk : 1 ≤ k) :
      k * (k + 1) = 2 ∨ k * (k + 1) = 6 ∨ 12 ≤ k * (k + 1) := by
    have cases : k = 1 ∨ k = 2 ∨ 3 ≤ k := by omega
    rcases cases with rfl | rfl | h
    · decide
    · decide
    · exact Or.inr (Or.inr (Nat.mul_le_mul h (Nat.succ_le_succ h)))
  rcases gap a ha with ha | ha | ha <;> rcases gap b hb with hb | hb | hb <;> omega

private theorem divisorIndicator_add {p : ℕ} [NeZero p] (hp : p = 3 ∨ p = 5)
    (a b : ℕ) (ha : IsSumTwoPositiveTriangular a) (hb : IsSumTwoPositiveTriangular b) :
    divisorIndicator p (a + b) = divisorIndicator p a + divisorIndicator p b := by
  have prime : p.Prime := by rcases hp with rfl | rfl <;> decide
  have vanish (k : ℕ) (hk : k = 2 ∨ k = 4 ∨ 6 ≤ k) : divisorIndicator p k = 0 := by
    have h : ¬ k ∣ p := fun hd ↦ by
      rcases (Nat.dvd_prime prime).mp hd with h | h <;> omega
    simp [divisorIndicator, h]
  have ha' := small_triangular_sums ha
  have hb' := small_triangular_sums hb
  rw [vanish a ha', vanish b hb', vanish (a + b) (by omega), add_zero]

example (n : ℕ) (hlo : 4 ≤ n) (hhi : n ≤ 21) : divisorIndicator 3 n = 0 :=
  multiplicative_additive_on_sum_two_triangular_zero_of_three_ne_zero (divisorIndicator 3)
    (divisorIndicator_multiplicative 3) (divisorIndicator_add (Or.inl rfl))
    rfl one_ne_zero n hlo hhi

example (n : ℕ) (hlo : 2 ≤ n) (hhi : n ≤ 21) (hn5 : n ≠ 5) : divisorIndicator 5 n = 0 :=
  multiplicative_additive_on_sum_two_triangular_zero_of_five_ne_zero (divisorIndicator 5)
    (divisorIndicator_multiplicative 5) (divisorIndicator_add (Or.inr rfl))
    rfl one_ne_zero n hlo hhi hn5

example (n : ℕ) (hlo : 2 ≤ n) (hhi : n ≤ 21) : divisorIndicator 1 n = 0 := by
  have vanish (k : ℕ) (hk : 2 ≤ k) : divisorIndicator 1 k = 0 := by
    simp [divisorIndicator, show k ≠ 1 by omega]
  refine multiplicative_additive_on_sum_two_triangular_zero_of_all_zero (divisorIndicator 1)
    (divisorIndicator_multiplicative 1) ?_ rfl rfl rfl n hlo hhi
  intro a b ha hb
  have ha' := small_triangular_sums ha
  have hb' := small_triangular_sums hb
  rw [vanish a (by omega), vanish b (by omega), vanish (a + b) (by omega), add_zero]

private noncomputable def natIdentity : ArithmeticFunction ℂ :=
  ⟨fun n ↦ (n : ℂ), Nat.cast_zero⟩

-- The identity satisfies all the hypotheses, including nonvanishing at 2.
example : natIdentity 2 = 2 := by
  have hmul : natIdentity.IsMultiplicative :=
    ⟨Nat.cast_one, fun {a b} _ ↦ Nat.cast_mul a b⟩
  have hadd (a b : ℕ) (_ha : IsSumTwoPositiveTriangular a) (_hb : IsSumTwoPositiveTriangular b) :
      natIdentity (a + b) = natIdentity a + natIdentity b := Nat.cast_add a b
  exact multiplicative_additive_on_sum_two_triangular_eq_id_le_21 natIdentity hmul hadd
    two_ne_zero 2 (by decide)

-- Both endpoints are included for an arbitrary function satisfying the hypotheses.
example (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ a b : ℕ, IsSumTwoPositiveTriangular a →
      IsSumTwoPositiveTriangular b → f (a + b) = f a + f b)
    (hf2 : f 2 ≠ 0) : f 0 = 0 ∧ f 21 = 21 :=
  let hid := multiplicative_additive_on_sum_two_triangular_eq_id_le_21 f hf hadd hf2
  ⟨by simpa only [Nat.cast_zero] using hid 0 (by decide), hid 21 (by decide)⟩

end MathlibExt.NumberTheory.ArithmeticFunction.MultiplicativeTriangularAdditiveWanted
