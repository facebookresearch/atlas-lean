/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Digits.ReverseDivisor
import MathlibExt.NumberTheory.Digits.ReverseDivisibility
import MathlibExt.NumberTheory.Digits.ReverseDivisorCoprime
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Ring

/-!
# The positive integers with property $P^*$

A positive integer divides the decimal reversal of every multiple if and only if
it divides $99$.

Source: Mohamed Ayad and Rachid Bouchenna, "Which Integer Divides the Reverse of Any
of Its Multiples?", INTEGERS 25 (2025), Article A37, Theorem 3.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.Digits.ReverseDivisorWanted

private theorem exists_reversal_identity (d : ℕ) (ds : List ℕ) (p : ℕ)
    (hd : 0 < d) (hd10 : d < 10) (hds : ∀ x ∈ ds, x < 10) :
    ∃ m : ℕ, m + 1 = 10 * Nat.ofDigits 10 (d :: ds) + 10 ^ (ds.length + p + 2) ∧
      10 * Nat.reverseDigits 10 m + 10 ^ (ds.length + p + 2) =
        10 + 90 * 10 ^ (ds.length + p + 2) +
          10 ^ (p + 2) * Nat.ofDigits 10 (d :: ds).reverse := by
  let l := (9 :: (d - 1) :: ds) ++ List.replicate p 0 ++ [1]
  have hl : Nat.digits 10 (Nat.ofDigits 10 l) = l := by
    apply Nat.digits_ofDigits 10 (by decide)
    · intro x hx
      simp only [l, List.mem_append, List.mem_cons, List.mem_replicate,
        List.not_mem_nil, or_false] at hx
      rcases hx with ((rfl | rfl | hx) | ⟨_, rfl⟩) | rfl
      · decide
      · omega
      · exact hds _ hx
      · decide
      · decide
    · intro h
      simp [l]
  refine ⟨Nat.ofDigits 10 l, ?_, ?_⟩
  · simp only [l, Nat.ofDigits_append, Nat.ofDigits_replicate_zero,
      Nat.ofDigits_cons, Nat.ofDigits_nil, List.length_append,
      List.length_cons, List.length_replicate, mul_zero, add_zero, mul_one]
    rw [show ds.length + 1 + 1 + p = ds.length + p + 2 by omega]
    omega
  · rw [Nat.reverseDigits, hl]
    simp only [l, List.reverse_append, List.reverse_replicate, List.reverse_singleton,
      Nat.ofDigits_append, Nat.ofDigits_singleton, Nat.ofDigits_replicate_zero,
      List.length_replicate, Nat.ofDigits_reverse_cons, List.length_cons,
      List.length_nil]
    rw [show d = d - 1 + 1 by omega]
    simp only [Nat.add_sub_cancel, pow_add, pow_succ]
    ring

private theorem dvd_ninety_nine (n : ℕ) (hn : 1 ≤ n) (hP : HasPropertyPStar n) :
    n ∣ 99 := by
  have hcop : Nat.Coprime n 10 := by
    by_contra h
    exact not_hasPropertyPStar_of_not_coprime n hn h hP
  obtain ⟨d, ds, hdigits⟩ : ∃ d ds, Nat.digits 10 n = d :: ds := by
    cases h : Nat.digits 10 n with
    | nil =>
      have hz := Nat.ofDigits_digits 10 n
      rw [h, Nat.ofDigits_nil] at hz
      omega
    | cons d ds => exact ⟨d, ds, rfl⟩
  have hnDigits : Nat.ofDigits 10 (d :: ds) = n := by
    rw [← hdigits, Nat.ofDigits_digits]
  have hd10 : d < 10 := Nat.digits_lt_base (by decide) (by rw [hdigits]; simp)
  have hds : ∀ x ∈ ds, x < 10 := by
    intro x hx
    exact Nat.digits_lt_base (by decide) (by rw [hdigits]; simp [hx])
  have hd : 0 < d := by
    by_contra h
    have hd0 : d = 0 := by omega
    have h10 : 10 ∣ n := by
      rw [← hnDigits, hd0, Nat.ofDigits_cons, zero_add]
      exact dvd_mul_right _ _
    have := hcop.symm.eq_one_of_dvd h10
    norm_num at this
  let k := n.totient * (ds.length + 2)
  let p := k - (ds.length + 2)
  have hle : ds.length + 2 ≤ k :=
    Nat.le_mul_of_pos_left _ (Nat.totient_pos.mpr hn)
  have hkp : ds.length + p + 2 = k := by dsimp [p]; omega
  have hpow : 10 ^ (ds.length + p + 2) ≡ 1 [MOD n] := by
    simpa only [hkp, k, pow_mul, one_pow] using
      (Nat.ModEq.pow_totient hcop.symm).pow (ds.length + 2)
  obtain ⟨m, hm, hr⟩ := exists_reversal_identity d ds p hd hd10 hds
  rw [hnDigits] at hm
  have hm0 : m ≡ 0 [MOD n] := by
    apply (Nat.ModEq.refl 1).add_right_cancel
    rw [hm]
    simpa only [mul_zero] using (dvd_rfl.modEq_zero_nat.mul_left 10).add hpow
  have hmr : Nat.reverseDigits 10 m ≡ 0 [MOD n] :=
    (hP m (Nat.modEq_zero_iff_dvd.mp hm0)).modEq_zero_nat
  have hnr : Nat.ofDigits 10 (d :: ds).reverse ≡ 0 [MOD n] := by
    simpa only [Nat.reverseDigits, hdigits] using (hP n dvd_rfl).modEq_zero_nat
  have h99 : 1 ≡ 100 [MOD n] := calc
    1 = 0 + 1 := rfl
    _ ≡ 10 * Nat.reverseDigits 10 m + 10 ^ (ds.length + p + 2) [MOD n] := by
      simpa only [mul_zero] using ((hmr.mul_left 10).add hpow).symm
    _ = 10 + 90 * 10 ^ (ds.length + p + 2) +
        10 ^ (p + 2) * Nat.ofDigits 10 (d :: ds).reverse := hr
    _ ≡ 10 + 90 * 1 + 0 [MOD n] := by
      simpa only [mul_zero] using
        ((Nat.ModEq.refl 10).add (hpow.mul_left 90)).add (hnr.mul_left (10 ^ (p + 2)))
    _ = 100 := by norm_num
  exact (Nat.modEq_iff_dvd' (by decide : 1 ≤ 100)).mp h99

/-- **The positive integers with property $P^*$ are the divisors of $99$.** A natural number
$n \ge 1$ has property $P^*$ if and only if $n$ divides $99$.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Theorem 3. -/
theorem hasPropertyPStar_iff_dvd (n : ℕ) (hn : 1 ≤ n) :
    HasPropertyPStar n ↔ n ∣ 99 := by
  constructor
  · exact dvd_ninety_nine n hn
  · intro h m hm
    exact dvd_reverseDigits_of_dvd 10 n (by decide) h m hm

end MathlibExt.NumberTheory.Digits.ReverseDivisorWanted
