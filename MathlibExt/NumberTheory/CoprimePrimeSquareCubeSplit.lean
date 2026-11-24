/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.GCD
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.RingTheory.Int.Basic

/-! # Splitting a prime square times a cube into coprime factors -/

namespace MetaMathlibExt

/-- **Splitting $RS = p^2 C^3$ when $R$ and $S$ are coprime.** Let $p$ be a prime and let $R$,
$S$, $C$ be integers with $RS = p^2 C^3$ and $\gcd(R, S) = 1$. Then there are integers $C_1$,
$C_2$ such that either $R = C_1^3$ and $S = p^2 C_2^3$, or $R = p^2 C_1^3$ and $S = C_2^3$.

Source: Jialai She, *Nonexistence of Consecutive Powerful Triplets Around Cubes
with Prime-Square Factors*, INTEGERS 25 (2025), Article A103, Lemma 1
(`integers-2025-A103-lem-1`). -/
public theorem cube_split_of_mul_eq_prime_sq_mul_cube_of_gcd_eq_one
    {p : ℕ} (hp : p.Prime) {R S C : ℤ} (h : R * S = (p : ℤ) ^ 2 * C ^ 3)
    (hg : Int.gcd R S = 1) :
    ∃ C₁ C₂ : ℤ, (R = C₁ ^ 3 ∧ S = (p : ℤ) ^ 2 * C₂ ^ 3) ∨
      (R = (p : ℤ) ^ 2 * C₁ ^ 3 ∧ S = C₂ ^ 3) := by
  have hp' := Nat.prime_iff_prime_int.mp hp
  have hcop := Int.isCoprime_iff_gcd_eq_one.mpr hg
  -- Strip the whole prime square from the factor that can contain it.
  have split {a b : ℤ} (hab : IsCoprime a b) (hprod : a * b = (p : ℤ) ^ 2 * C ^ 3)
      (ha : ¬ (p : ℤ) ∣ a) : ∃ x y : ℤ, a = x ^ 3 ∧ b = (p : ℤ) ^ 2 * y ^ 3 := by
    have hd : (p : ℤ) ^ 2 ∣ a * b := ⟨C ^ 3, hprod⟩
    obtain ⟨b', hb'⟩ := hp'.pow_dvd_of_dvd_mul_left 2 ha hd
    -- Only the nonzero prime square is cancelled, so this also works when C = 0.
    have hcube : a * b' = C ^ 3 := by
      rw [hb', mul_left_comm] at hprod
      exact mul_left_cancel₀ (pow_ne_zero 2 hp'.ne_zero) hprod
    have hab' : IsCoprime a b' := by
      rw [hb'] at hab
      exact hab.of_mul_right_right
    -- The exponent is odd, so the witnesses are signed integer cube roots.
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := Int.eq_pow_of_mul_eq_pow_odd hab' (by decide : Odd 3) hcube
    exact ⟨x, y, hx, by rw [hb', hy]⟩
  by_cases hR : (p : ℤ) ∣ R
  · have hS : ¬ (p : ℤ) ∣ S := fun hS => hp'.not_isUnit (hcop.isUnit_of_dvd' hR hS)
    obtain ⟨y, x, hy, hx⟩ := split hcop.symm (by rwa [mul_comm S R]) hS
    exact ⟨x, y, Or.inr ⟨hx, hy⟩⟩
  · obtain ⟨x, y, hx, hy⟩ := split hcop h hR
    exact ⟨x, y, Or.inl ⟨hx, hy⟩⟩

end MetaMathlibExt
