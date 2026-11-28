/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.GeneralizedFermatExponents
import MathlibExt.NumberTheory.PrimeCubeSquareNeighbors

/-!
# A Diophantine obstruction for consecutive powerful numbers

We rule out `64 * x ^ 6 - 1` being a product of two prime cubes and a square.
-/

set_option autoImplicit false

namespace MathlibExt.NumberTheory.PowerfulNumbersWanted

private theorem sq_mod_eight_ne_seven (u : ℕ) : u ^ 2 % 8 ≠ 7 := by
  have hu := Nat.mod_lt u (by decide : 0 < 8)
  rw [pow_two, Nat.mul_mod]
  generalize u % 8 = r at hu ⊢
  interval_cases r <;> decide

-- After removing the specified divisors, the coprime quotients have square product.
private theorem squares_of_coprime_factors {a b d e y : ℕ} (hab : a.Coprime b)
    (hd₀ : d ≠ 0) (he₀ : e ≠ 0) (hd : d ∣ a) (he : e ∣ b) (h : a * b = d * e * y ^ 2) :
    ∃ u v : ℕ, a = d * u ^ 2 ∧ b = e * v ^ 2 := by
  obtain ⟨a', rfl⟩ := hd
  obtain ⟨b', rfl⟩ := he
  have hc := hab.of_dvd (dvd_mul_left a' d) (dvd_mul_left b' e)
  have hs : a' * b' = y ^ 2 := by
    apply mul_left_cancel₀ (mul_ne_zero hd₀ he₀)
    calc
      d * e * (a' * b') = d * a' * (e * b') := by ac_rfl
      _ = _ := h
  have square_left {m n : ℕ} (hc' : m.Coprime n) (hmn : m * n = y ^ 2) : IsSquare m := by
    rw [Nat.isSquare_iff_even_factorization]
    intro r hr
    by_cases hm : r ∈ m.primeFactorsList
    · rw [← Nat.factorization_eq_of_coprime_left hc' hm, hmn]
      exact Nat.isSquare_iff_even_factorization.mp ⟨y, pow_two y⟩ r hr
    · rw [← Nat.primeFactorsList_count_eq, List.count_eq_zero_of_not_mem hm]
      exact ⟨0, rfl⟩
  obtain ⟨u, hu⟩ := square_left hc hs
  obtain ⟨v, hv⟩ := square_left hc.symm (by rwa [mul_comm b' a'])
  exact ⟨u, v, by rw [hu, pow_two], by rw [hv, pow_two]⟩

/-- **No integer solutions of $64x^6 - 1 = p^3 q^3 y^2$ with $p$, $q$ prime.** There are no
integers $x$, $y$ and primes $p$, $q$ with $64 x^6 - 1 = p^3 q^3 y^2$.

Source: Tsz Ho Chan, "A Note on Three Consecutive Powerful Numbers",
Corollary 1. -/
public theorem not_exists_sixty_four_mul_pow_six_sub_one_eq :
    ¬ ∃ (p q : ℕ) (x y : ℤ),
      p.Prime ∧ q.Prime ∧
        64 * x ^ 6 - 1 = (p : ℤ) ^ 3 * (q : ℤ) ^ 3 * y ^ 2 := by
  rintro ⟨p, q, x, y, hp, hq, h⟩
  by_cases hx : x = 0
  · have hnonneg : 0 ≤ (p : ℤ) ^ 3 * (q : ℤ) ^ 3 * y ^ 2 := by positivity
    norm_num [hx] at h
    omega
  let t := 2 * x.natAbs
  have hx₀ : 0 < x.natAbs := Int.natAbs_pos.mpr hx
  have ht₂ : 2 ≤ t := by dsimp [t]; omega
  have ht : 0 < t := by omega
  have ht₃ : 1 < t ^ 3 := (by decide : 1 < (2 : ℕ) ^ 3).trans_le (Nat.pow_le_pow_left ht₂ _)
  have ht₈ : t ^ 3 % 8 = 0 := by
    apply Nat.mod_eq_zero_of_dvd
    exact ⟨x.natAbs ^ 3, by dsimp [t]; rw [mul_pow]; rfl⟩
  let a := t ^ 3 - 1
  let b := t ^ 3 + 1
  have ha₀ : a ≠ 0 := by dsimp [a]; omega
  have hb₀ : b ≠ 0 := by dsimp [b]; omega
  have ha₈ : a % 8 = 7 := by dsimp [a]; omega
  have hb₈ : b % 8 = 1 := by dsimp [b]; omega
  have hb_add : b = a + 2 := by dsimp [a, b]; omega
  have hab : a.Coprime b := by
    rw [hb_add, Nat.coprime_self_add_right, Nat.coprime_two_right, Nat.odd_iff]
    omega
  have ha_int : (a : ℤ) = (t : ℤ) ^ 3 - 1 := by simp [a, Nat.cast_sub ht₃.le]
  have hb_int : (b : ℤ) = (t : ℤ) ^ 3 + 1 := by simp [b]
  have ht₆ : (t : ℤ) ^ 6 = 64 * x ^ 6 := by
    push_cast [t]
    rw [mul_pow, (show Even (6 : ℕ) by decide).pow_abs]
    norm_num
  have hab_eq : a * b = p ^ 3 * q ^ 3 * y.natAbs ^ 2 := by
    have hz : (a : ℤ) * (b : ℤ) = (p : ℤ) ^ 3 * (q : ℤ) ^ 3 * y ^ 2 := by
      rw [ha_int, hb_int, ← h]
      linear_combination ht₆
    simpa only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] using congrArg Int.natAbs hz
  -- When the primes coincide, the entire product would be a square, but it is 7 modulo 8.
  by_cases hpq : p = q
  · subst q
    apply sq_mod_eight_ne_seven (p ^ 3 * y.natAbs)
    rw [mul_pow, pow_two (p ^ 3), ← hab_eq, Nat.mul_mod, ha₈, hb₈]
  have hp₀ : p ^ 3 ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hq₀ : q ^ 3 ≠ 0 := pow_ne_zero _ hq.ne_zero
  have hpc : (p ^ 3).Coprime (q ^ 3) := ((Nat.coprime_primes hp hq).mpr hpq).pow 3 3
  have hpd : p ^ 3 ∣ a * b := hab_eq ▸ dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have hqd : q ^ 3 ∣ a * b := hab_eq ▸ dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  have split_cube {r : ℕ} (hr : r.Prime) (hd : r ^ 3 ∣ a * b) : r ^ 3 ∣ a ∨ r ^ 3 ∣ b :=
    (hab.isPrimePow_dvd_mul ((isPrimePow_nat_iff _).mpr ⟨r, 3, hr, by decide, rfl⟩)).mp hd
  have split_neighbors {r s : ℕ} (hr : r.Prime) (hs : s.Prime) (hra : r ^ 3 ∣ a) (hsb : s ^ 3 ∣ b)
      (he : a * b = r ^ 3 * s ^ 3 * y.natAbs ^ 2) : False := by
    obtain ⟨u, v, hu, hv⟩ := squares_of_coprime_factors hab (pow_ne_zero _ hr.ne_zero)
      (pow_ne_zero _ hs.ne_zero) hra hsb he
    have hu₀ : 0 < u := Nat.pos_of_ne_zero (by rintro rfl; simp [ha₀] at hu)
    have hv₀ : 0 < v := Nat.pos_of_ne_zero (by rintro rfl; simp [hb₀] at hv)
    exact not_exists_prime_cube_square_neighbors_of_cube
      ⟨r, s, t, u, v, hr, hs, ht, hu₀, hv₀, by rw [← ha_int]; exact_mod_cast hu,
        by rw [← hb_int]; exact_mod_cast hv⟩
  rcases split_cube hp hpd with hpa | hpb <;> rcases split_cube hq hqd with hqa | hqb
  · -- Both cubes divide the lower neighbor, so the upper neighbor is a square.
    obtain ⟨_, v, -, hv⟩ := squares_of_coprime_factors hab (mul_ne_zero hp₀ hq₀) one_ne_zero
      (hpc.mul_dvd_of_dvd_of_dvd hpa hqa) (one_dvd b) (by simpa using hab_eq)
    have hv_eq : t ^ 3 + 1 = v ^ 2 := by simpa [b] using hv
    have hv₀ : v ≠ 0 := by rintro rfl; simp at hv_eq
    have ht_eq := MetaMathlibExt.eq_two_of_sq_eq_cube_add_one (x := (t : ℚ)) (y := (v : ℚ))
      (by exact_mod_cast ht.ne') (by exact_mod_cast hv₀) (by exact_mod_cast hv_eq.symm)
    have ht' : t = 2 := by exact_mod_cast ht_eq
    have h63 : p ^ 3 ∣ 63 := by simpa [a, b, ht'] using hpd
    have hp₃le := Nat.le_of_dvd (by decide : 0 < 63) h63
    have hp_lt : p < 4 := by
      by_contra! hle
      have := Nat.pow_le_pow_left hle 3
      omega
    have hp_le := hp.two_le
    interval_cases p <;> norm_num at h63
  · exact split_neighbors hp hq hpa hqb hab_eq
  · exact split_neighbors hq hp hqa hpb (by simpa only [mul_comm (p ^ 3) (q ^ 3)] using hab_eq)
  · -- Both cubes divide the upper neighbor, leaving a square congruent to 7 modulo 8.
    obtain ⟨u, _, hu, -⟩ := squares_of_coprime_factors hab one_ne_zero (mul_ne_zero hp₀ hq₀)
      (one_dvd a) (hpc.mul_dvd_of_dvd_of_dvd hpb hqb) (by simpa using hab_eq)
    rw [one_mul] at hu
    exact sq_mod_eight_ne_seven u (by rwa [← hu])

end MathlibExt.NumberTheory.PowerfulNumbersWanted
