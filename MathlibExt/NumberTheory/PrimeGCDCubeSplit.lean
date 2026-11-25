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
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Splitting a prime square times a cube

Suppose `R * S = p ^ 2 * C ^ 3` and both `p` and `g = gcd(R, S)` are prime.
After dividing both factors by `g`, both quotients are cubes if `g = p`. Otherwise,
removing one further factor of `g` and one factor of `p ^ 2` leaves two cubes.
These two coefficients can occur in the same quotient or in opposite quotients.
-/

namespace MetaMathlibExt

/-- **Splitting $RS = p^2 C^3$ when $\gcd(R, S)$ is prime.** Let $p$ be a prime and let $R$, $S$,
$C$ be integers with $RS = p^2 C^3$ such that $g = \gcd(R, S)$ is prime. Then there are
integers $C_1$, $C_2$ such that one of the following holds: $R = g C_1^3$ and $S = g C_2^3$;
or $R = g C_1^3$ and $S = g^2 p^2 C_2^3$; or $S = g C_1^3$ and $R = g^2 p^2 C_2^3$; or
$R = g p^2 C_1^3$ and $S = g^2 C_2^3$; or $S = g p^2 C_1^3$ and $R = g^2 C_2^3$.

Source: Jialai She, *Nonexistence of Consecutive Powerful Triplets Around Cubes
with Prime-Square Factors*, INTEGERS 25 (2025), Article A103, Lemma 1
(`integers-2025-A103-lem-1`). -/
public theorem cube_split_of_mul_eq_prime_sq_mul_cube_of_gcd_prime
    {p : ℕ} (hp : p.Prime) {R S C : ℤ} (h : R * S = (p : ℤ) ^ 2 * C ^ 3)
    (hg : (Int.gcd R S).Prime) :
    ∃ C₁ C₂ : ℤ,
      (R = (Int.gcd R S : ℤ) * C₁ ^ 3 ∧ S = (Int.gcd R S : ℤ) * C₂ ^ 3) ∨
      (R = (Int.gcd R S : ℤ) * C₁ ^ 3 ∧
        S = (Int.gcd R S : ℤ) ^ 2 * (p : ℤ) ^ 2 * C₂ ^ 3) ∨
      (S = (Int.gcd R S : ℤ) * C₁ ^ 3 ∧
        R = (Int.gcd R S : ℤ) ^ 2 * (p : ℤ) ^ 2 * C₂ ^ 3) ∨
      (R = (Int.gcd R S : ℤ) * (p : ℤ) ^ 2 * C₁ ^ 3 ∧
        S = (Int.gcd R S : ℤ) ^ 2 * C₂ ^ 3) ∨
      (S = (Int.gcd R S : ℤ) * (p : ℤ) ^ 2 * C₁ ^ 3 ∧
        R = (Int.gcd R S : ℤ) ^ 2 * C₂ ^ 3) := by
  obtain ⟨r, s, hrs, hR, hS⟩ := Int.exists_gcd_one hg.pos
  set g := Int.gcd R S
  have hcop := Int.isCoprime_iff_gcd_eq_one.mpr hrs
  have hg' := Nat.prime_iff_prime_int.mp hg
  have hp' := Nat.prime_iff_prime_int.mp hp
  have hprod : (g : ℤ) ^ 2 * (r * s) = (p : ℤ) ^ 2 * C ^ 3 := by
    rw [hR, hS] at h
    linear_combination h
  by_cases heq : g = p
  · rw [← heq] at hprod
    have hrsCube := mul_left_cancel₀ (pow_ne_zero 2 hg'.ne_zero) hprod
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := Int.eq_pow_of_mul_eq_pow_odd hcop (by decide : Odd 3) hrsCube
    exact ⟨x, y, Or.inl ⟨by rw [hR, hx, mul_comm], by rw [hS, hy, mul_comm]⟩⟩
  have hgp : IsCoprime (g : ℤ) ((p : ℤ) ^ 2) :=
    ((Nat.coprime_primes hg hp).mpr heq).isCoprime.pow_right
  -- Since the gcd cannot come from the prime square, it divides the cube root.
  have hgC : (g : ℤ) ∣ C := by
    apply hg'.dvd_of_dvd_pow (n := 3)
    apply hgp.dvd_of_dvd_mul_left
    rw [← hprod]
    exact (dvd_pow_self _ (by decide : 2 ≠ 0)).mul_right _
  obtain ⟨c, hc⟩ := hgC
  have hreduced : r * s = g * (p : ℤ) ^ 2 * c ^ 3 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hg'.ne_zero)
    rw [hc] at hprod
    linear_combination hprod
  have hgdvd : (g : ℤ) ∣ r ∨ (g : ℤ) ∣ s :=
    hg'.dvd_or_dvd ⟨_, hreduced.trans (mul_assoc ..)⟩
  have hpdvd : (p : ℤ) ^ 2 ∣ r ∨ (p : ℤ) ^ 2 ∣ s := by
    have hd : (p : ℤ) ^ 2 ∣ r * s := ⟨g * c ^ 3, by rw [hreduced]; ring⟩
    by_cases hpr : (p : ℤ) ∣ r
    · exact Or.inl (hp'.pow_dvd_of_dvd_mul_right 2
        (fun hps => hp'.not_isUnit (hcop.isUnit_of_dvd' hpr hps)) hd)
    · exact Or.inr (hp'.pow_dvd_of_dvd_mul_left 2 hpr hd)
  -- After assigning both coefficients, the remaining coprime factors are cubes.
  have split {u v : ℤ} (hu : u ∣ r) (hv : v ∣ s) (huv : u * v = g * (p : ℤ) ^ 2) :
      ∃ x y : ℤ, R = g * u * x ^ 3 ∧ S = g * v * y ^ 3 := by
    obtain ⟨a, ha⟩ := hu
    obtain ⟨b, hb⟩ := hv
    rw [ha, hb] at hcop hreduced
    have hab : a * b = c ^ 3 := by
      apply mul_left_cancel₀ (a := u * v) (by
        rw [huv]
        exact mul_ne_zero hg'.ne_zero (pow_ne_zero 2 hp'.ne_zero))
      rw [← huv] at hreduced
      linear_combination hreduced
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := Int.eq_pow_of_mul_eq_pow_odd
      hcop.of_mul_left_right.of_mul_right_right (by decide : Odd 3) hab
    exact ⟨x, y, by rw [hR, ha, hx]; ring, by rw [hS, hb, hy]; ring⟩
  rcases hgdvd with hgr | hgs <;> rcases hpdvd with hpr | hps
  · obtain ⟨x, y, hx, hy⟩ := split (hgp.mul_dvd hgr hpr) (one_dvd s) (mul_one _)
    exact ⟨y, x, Or.inr (Or.inr (Or.inl ⟨by simpa using hy, by rw [hx]; ring⟩))⟩
  · obtain ⟨x, y, hx, hy⟩ := split hgr hps rfl
    exact ⟨y, x, Or.inr (Or.inr (Or.inr (Or.inr ⟨hy, by simpa [pow_two] using hx⟩)))⟩
  · obtain ⟨x, y, hx, hy⟩ := split hpr hgs (mul_comm ..)
    exact ⟨x, y, Or.inr (Or.inr (Or.inr (Or.inl ⟨hx, by simpa [pow_two] using hy⟩)))⟩
  · obtain ⟨x, y, hx, hy⟩ := split (one_dvd r) (hgp.mul_dvd hgs hps) (one_mul _)
    exact ⟨x, y, Or.inr (Or.inl ⟨by simpa using hx, by rw [hy]; ring⟩)⟩

end MetaMathlibExt
