/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Card
public import MathlibExt.NumberTheory.PolygonalNumber
import Mathlib.NumberTheory.SumFourSquares
import Mathlib.Tactic
import MathlibExt.NumberTheory.QuadraticForms.LegendreThreeSquare

/-!
# Fermat's polygonal number theorem

This file proves Gauss's three-triangular-number theorem, Cauchy's four-square
lemma with a prescribed sum, and Fermat's theorem that every natural number is
a sum of at most `s` nonnegative `s`-gonal numbers.

Wikipedia states the theorem for positive integers; the Lean statement also covers `n = 0`
(the empty sum, and `Nat.polygonalNumber s 0 = 0`).

## References

* A.-L. Cauchy, *Démonstration du théorème général de Fermat sur les nombres polygones*,
  Mém. Sci. Math. Phys. Inst. France (1) 14 (1813-15), 177-220 = *Oeuvres* (2) vol. 6, 320-353.
* M. B. Nathanson, *A short proof of Cauchy's polygonal number theorem*,
  Proc. Amer. Math. Soc. 99 (1987), 22-24.
* M. B. Nathanson, *Additive Number Theory: The Classical Bases*, GTM 164, Springer (1996),
  Ch. 1.
* *Fermat polygonal number theorem*, Wikipedia,
  <https://en.wikipedia.org/wiki/Fermat_polygonal_number_theorem>.
-/

open scoped BigOperators

namespace Nat

private theorem fermatPoly_even_sq_mod_eight {n : ℕ} (hn : Even n) :
    n ^ 2 % 8 = 0 ∨ n ^ 2 % 8 = 4 := by
  obtain ⟨k, rfl⟩ := hn
  rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · left
    have h : (j + j + (j + j)) ^ 2 = 8 * (2 * j ^ 2) := by ring
    rw [h]
    simp
  · right
    have h : (2 * j + 1 + (2 * j + 1)) ^ 2 = 8 * (2 * j ^ 2 + 2 * j) + 4 := by
      ring
    rw [h]
    omega

private theorem fermatPoly_odd_sq_mod_eight {n : ℕ} (hn : Odd n) : n ^ 2 % 8 = 1 := by
  obtain ⟨k, rfl⟩ := hn
  rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · have hsq : (2 * (j + j) + 1) ^ 2 = 8 * (2 * j ^ 2 + j) + 1 := by ring
    rw [hsq]
    omega
  · have hsq : (2 * (2 * j + 1) + 1) ^ 2 = 8 * (2 * j ^ 2 + 3 * j + 1) + 1 := by
      ring
    rw [hsq]
    omega

private theorem fermatPoly_sq_mod_eight (n : ℕ) :
    n ^ 2 % 8 = 0 ∨ n ^ 2 % 8 = 1 ∨ n ^ 2 % 8 = 4 := by
  rcases Nat.even_or_odd n with hn | hn
  · rcases fermatPoly_even_sq_mod_eight hn with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl (fermatPoly_odd_sq_mod_eight hn))

private theorem fermatPoly_odd_iff_sq_mod_eight_eq_one (n : ℕ) :
    Odd n ↔ n ^ 2 % 8 = 1 := by
  constructor
  · exact fermatPoly_odd_sq_mod_eight
  · intro hn
    rcases Nat.even_or_odd n with he | ho
    · rcases fermatPoly_even_sq_mod_eight he with h | h <;> omega
    · exact ho

private theorem fermatPoly_not_exceptional_of_mod_eight_eq_three
    {n : ℕ} (hn : n % 8 = 3) : ¬ ∃ a b : ℕ, n = 4 ^ a * (8 * b + 7) := by
  rintro ⟨a, b, rfl⟩
  cases a with
  | zero => omega
  | succ a =>
      cases a with
      | zero => omega
      | succ a =>
          have hpow : 8 ∣ 4 ^ (Nat.succ (Nat.succ a)) := by
            refine ⟨2 * 4 ^ a, ?_⟩
            simp [pow_succ]
            ring
          have hzero : (4 ^ (Nat.succ (Nat.succ a)) * (8 * b + 7)) % 8 = 0 :=
            Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left hpow _)
          have hzero' : (4 ^ (a + 1 + 1) * (8 * b + 7)) % 8 = 0 := by
            simpa only [Nat.succ_eq_add_one] using hzero
          omega

private theorem fermatPoly_twice_triangular (n : ℕ) :
    2 * (n * (n + 1) / 2) = n * (n + 1) := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have h : (k + k) * (k + k + 1) = 2 * (k * (k + k + 1)) := by ring
    rw [h]
    simp
  · have h : (2 * k + 1) * (2 * k + 1 + 1) = 2 * ((2 * k + 1) * (k + 1)) := by
      ring
    rw [h]
    simp

@[expose] public section

/-- **Gauss's Eureka theorem.** Every natural number $n$ is a sum of three triangular numbers:
there are natural numbers $x, y, z$ with $n = T_x + T_y + T_z$, where $T_m = m(m + 1)/2$ is the
$m$-th triangular ($3$-gonal) number, so that $T_0 = 0$.

Source: C. F. Gauss, *Disquisitiones Arithmeticae* (1801), as cited in Nathanson (1987), whose
introduction gives the equivalent form used here: `8n + 3` is a sum of three odd squares. -/
theorem exists_eq_add_add_triangular (n : ℕ) :
    ∃ x y z : ℕ, n = polygonalNumber 3 x + polygonalNumber 3 y + polygonalNumber 3 z := by
  have hmod : (8 * n + 3) % 8 = 3 := by omega
  obtain ⟨x, y, z, hxyz⟩ :=
    Nat.exists_three_squares_of_not_four_pow_mul_eight_mul_add_seven (8 * n + 3)
      (fermatPoly_not_exceptional_of_mod_eight_eq_three hmod)
  have hsumMod : (x ^ 2 % 8 + y ^ 2 % 8 + z ^ 2 % 8) % 8 = 3 := by
    calc
      (x ^ 2 % 8 + y ^ 2 % 8 + z ^ 2 % 8) % 8 =
          (x ^ 2 + y ^ 2 + z ^ 2) % 8 := by simp [Nat.add_mod]
      _ = (8 * n + 3) % 8 := congrArg (· % 8) hxyz
      _ = 3 := hmod
  have hmods : x ^ 2 % 8 = 1 ∧ y ^ 2 % 8 = 1 ∧ z ^ 2 % 8 = 1 := by
    rcases fermatPoly_sq_mod_eight x with hx | hx | hx <;>
      rcases fermatPoly_sq_mod_eight y with hy | hy | hy <;>
      rcases fermatPoly_sq_mod_eight z with hz | hz | hz <;> omega
  have hxodd := (fermatPoly_odd_iff_sq_mod_eight_eq_one x).mpr hmods.1
  have hyodd := (fermatPoly_odd_iff_sq_mod_eight_eq_one y).mpr hmods.2.1
  have hzodd := (fermatPoly_odd_iff_sq_mod_eight_eq_one z).mpr hmods.2.2
  obtain ⟨a, rfl⟩ := hxodd
  obtain ⟨b, rfl⟩ := hyodd
  obtain ⟨c, rfl⟩ := hzodd
  refine ⟨a, b, c, ?_⟩
  rw [polygonalNumber_three, polygonalNumber_three, polygonalNumber_three]
  have ha := fermatPoly_twice_triangular a
  have hb := fermatPoly_twice_triangular b
  have hc := fermatPoly_twice_triangular c
  nlinarith

end

private theorem fermatPoly_order_three_squares {n x y z : ℕ}
    (h : x ^ 2 + y ^ 2 + z ^ 2 = n) :
    ∃ x' y' z' : ℕ, z' ≤ y' ∧ y' ≤ x' ∧ x' ^ 2 + y' ^ 2 + z' ^ 2 = n := by
  rcases le_total x y with hxy | hyx
  · rcases le_total y z with hyz | hzy
    · exact ⟨z, y, x, hxy, hyz, by rw [← h]; ring⟩
    · rcases le_total x z with hxz | hzx
      · exact ⟨y, z, x, hxz, hzy, by rw [← h]; ring⟩
      · exact ⟨y, x, z, hzx, hxy, by rw [← h]; ring⟩
  · rcases le_total x z with hxz | hzx
    · exact ⟨z, x, y, hyx, hxz, by rw [← h]; ring⟩
    · rcases le_total y z with hyz | hzy
      · exact ⟨x, z, y, hyz, hzx, by rw [← h]; ring⟩
      · exact ⟨x, y, z, hzy, hyx, h⟩

private theorem fermatPoly_sum_three_sq_le (x y z : ℕ) :
    (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  nlinarith [two_mul_le_add_sq x y, two_mul_le_add_sq x z, two_mul_le_add_sq y z]

private theorem fermatPoly_two_dvd_int_add_of_odd {x y : ℕ} (hx : Odd x) (hy : Odd y) :
    (2 : ℤ) ∣ (x : ℤ) + (y : ℤ) := by
  obtain ⟨p, hp⟩ := hx
  obtain ⟨q, hq⟩ := hy
  refine ⟨(p : ℤ) + q + 1, ?_⟩
  norm_num [hp, hq]
  ring

private theorem fermatPoly_two_dvd_int_sub_of_odd {x y : ℕ} (hx : Odd x) (hy : Odd y) :
    (2 : ℤ) ∣ (x : ℤ) - (y : ℤ) := by
  obtain ⟨p, hp⟩ := hx
  obtain ⟨q, hq⟩ := hy
  refine ⟨(p : ℤ) - q, ?_⟩
  norm_num [hp, hq]
  ring

private theorem fermatPoly_exists_signed_dvd_four {b x y z : ℕ}
    (hb : Odd b) (hx : Odd x) (hy : Odd y) (hz : Odd z) :
    ∃ w : ℤ, (w = (z : ℤ) ∨ w = -(z : ℤ)) ∧
      (4 : ℤ) ∣ (b : ℤ) + x + y + w := by
  obtain ⟨B, hB⟩ := hb
  obtain ⟨X, hX⟩ := hx
  obtain ⟨Y, hY⟩ := hy
  obtain ⟨Z, hZ⟩ := hz
  rcases Nat.even_or_odd (B + X + Y + Z) with ⟨r, hr⟩ | ⟨r, hr⟩
  · refine ⟨(z : ℤ), Or.inl rfl, (r : ℤ) + 1, ?_⟩
    norm_num [hB, hX, hY, hZ] at ⊢
    have hr' : (B : ℤ) + X + Y + Z = r + r := by exact_mod_cast hr
    omega
  · refine ⟨-(z : ℤ), Or.inr rfl, (r : ℤ) + 1 - Z, ?_⟩
    norm_num [hB, hX, hY, hZ] at ⊢
    have hr' : B + X + Y + Z = 2 * r + 1 := hr
    omega

@[expose] public section

/-- **Cauchy's lemma.** Let $a$ and $b$ be odd natural numbers with $b^2 < 4a$ and
$3a < b^2 + 2b + 4$. Then there are natural numbers $s, t, u, v$ with
$a = s^2 + t^2 + u^2 + v^2$ and $b = s + t + u + v$.

Source: M. B. Nathanson, *A short proof of Cauchy's polygonal number theorem*,
Proc. Amer. Math. Soc. 99 (1987), 22-24, "Cauchy's Lemma"; originally Cauchy (1813-15). -/
theorem exists_sum_four_sq_eq_and_sum_eq_of_odd {a b : ℕ}
    (ha : a % 2 = 1) (hb : b % 2 = 1) (hba : b ^ 2 < 4 * a)
    (hab : 3 * a < b ^ 2 + 2 * b + 4) :
    ∃ s t u v : ℕ, a = s ^ 2 + t ^ 2 + u ^ 2 + v ^ 2 ∧ b = s + t + u + v := by
  have haOdd : Odd a := Nat.odd_iff.mpr ha
  have hbOdd : Odd b := Nat.odd_iff.mpr hb
  set d := 4 * a - b ^ 2 with hd
  have hdadd : d + b ^ 2 = 4 * a := by
    dsimp [d]
    omega
  obtain ⟨A, hA⟩ := haOdd
  have haMod : (4 * a) % 8 = 4 := by
    rw [hA]
    omega
  have hbSqMod : b ^ 2 % 8 = 1 := fermatPoly_odd_sq_mod_eight hbOdd
  have hdMod : d % 8 = 3 := by
    have h : (d % 8 + b ^ 2 % 8) % 8 = (4 * a) % 8 := by
      rw [← Nat.add_mod]
      exact congrArg (· % 8) hdadd
    have hdlt := Nat.mod_lt d (by norm_num : 0 < 8)
    omega
  obtain ⟨x₀, y₀, z₀, hxyz₀⟩ :=
    Nat.exists_three_squares_of_not_four_pow_mul_eight_mul_add_seven d
      (fermatPoly_not_exceptional_of_mod_eight_eq_three hdMod)
  obtain ⟨x, y, z, hzy, hyx, hxyz⟩ := fermatPoly_order_three_squares hxyz₀
  have hsumMod : (x ^ 2 % 8 + y ^ 2 % 8 + z ^ 2 % 8) % 8 = 3 := by
    calc
      (x ^ 2 % 8 + y ^ 2 % 8 + z ^ 2 % 8) % 8 =
          (x ^ 2 + y ^ 2 + z ^ 2) % 8 := by simp [Nat.add_mod]
      _ = d % 8 := congrArg (· % 8) hxyz
      _ = 3 := hdMod
  have hmods : x ^ 2 % 8 = 1 ∧ y ^ 2 % 8 = 1 ∧ z ^ 2 % 8 = 1 := by
    rcases fermatPoly_sq_mod_eight x with hx | hx | hx <;>
      rcases fermatPoly_sq_mod_eight y with hy | hy | hy <;>
      rcases fermatPoly_sq_mod_eight z with hz | hz | hz <;> omega
  have hx : Odd x := (fermatPoly_odd_iff_sq_mod_eight_eq_one x).mpr hmods.1
  have hy : Odd y := (fermatPoly_odd_iff_sq_mod_eight_eq_one y).mpr hmods.2.1
  have hz : Odd z := (fermatPoly_odd_iff_sq_mod_eight_eq_one z).mpr hmods.2.2
  have hsumSq := fermatPoly_sum_three_sq_le x y z
  have hsumLt : x + y + z < b + 4 := by
    have hsqLt : (x + y + z) ^ 2 < (b + 4) ^ 2 := by
      calc
        (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := hsumSq
        _ < (b + 4) ^ 2 := by nlinarith
    exact (Nat.pow_lt_pow_iff_left (by decide : 2 ≠ 0)).mp hsqLt
  obtain ⟨w, hw, hdiv4⟩ := fermatPoly_exists_signed_dvd_four hbOdd hx hy hz
  let B : ℤ := b
  let X : ℤ := x
  let Y : ℤ := y
  let S : ℤ := (B + X + Y + w) / 4
  let T : ℤ := (B + X) / 2 - S
  let U : ℤ := (B + Y) / 2 - S
  let V : ℤ := (B + w) / 2 - S
  have hS4 : 4 * S = B + X + Y + w := by
    dsimp [S]
    exact Int.mul_ediv_cancel' hdiv4
  have hBXdiv : (2 : ℤ) ∣ B + X := by
    simpa [B, X] using fermatPoly_two_dvd_int_add_of_odd hbOdd hx
  have hBYdiv : (2 : ℤ) ∣ B + Y := by
    simpa [B, Y] using fermatPoly_two_dvd_int_add_of_odd hbOdd hy
  have hBWdiv : (2 : ℤ) ∣ B + w := by
    rcases hw with hw | hw
    · simpa [B, hw] using fermatPoly_two_dvd_int_add_of_odd hbOdd hz
    · rw [hw]
      change (2 : ℤ) ∣ B - (z : ℤ)
      simpa [B] using fermatPoly_two_dvd_int_sub_of_odd hbOdd hz
  have hT2 : 2 * (T + S) = B + X := by
    dsimp [T]
    simpa using Int.mul_ediv_cancel' hBXdiv
  have hU2 : 2 * (U + S) = B + Y := by
    dsimp [U]
    simpa using Int.mul_ediv_cancel' hBYdiv
  have hV2 : 2 * (V + S) = B + w := by
    dsimp [V]
    simpa using Int.mul_ediv_cancel' hBWdiv
  have hT4 : 4 * T = B + X - Y - w := by linarith
  have hU4 : 4 * U = B - X + Y - w := by linarith
  have hV4 : 4 * V = B - X - Y + w := by linarith
  have hsumInt : S + T + U + V = B := by linarith
  have hrootSqNat : b ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = 4 * a := by omega
  have hrootSq : B ^ 2 + X ^ 2 + Y ^ 2 + w ^ 2 = 4 * (a : ℤ) := by
    rcases hw with hw | hw
    · norm_num [B, X, Y, hw]
      exact_mod_cast hrootSqNat
    · norm_num [B, X, Y, hw]
      exact_mod_cast hrootSqNat
  have hfourSq : S ^ 2 + T ^ 2 + U ^ 2 + V ^ 2 = (a : ℤ) := by
    have hscaled :
        16 * (S ^ 2 + T ^ 2 + U ^ 2 + V ^ 2) =
          4 * (B ^ 2 + X ^ 2 + Y ^ 2 + w ^ 2) := by
      calc
        16 * (S ^ 2 + T ^ 2 + U ^ 2 + V ^ 2) =
            (4 * S) ^ 2 + (4 * T) ^ 2 + (4 * U) ^ 2 + (4 * V) ^ 2 := by ring
        _ = (B + X + Y + w) ^ 2 + (B + X - Y - w) ^ 2 +
              (B - X + Y - w) ^ 2 + (B - X - Y + w) ^ 2 := by
              rw [hS4, hT4, hU4, hV4]
        _ = 4 * (B ^ 2 + X ^ 2 + Y ^ 2 + w ^ 2) := by ring
    rw [hrootSq] at hscaled
    nlinarith only [hscaled]
  have hsumLtInt : (X + Y + (z : ℤ)) < B + 4 := by
    dsimp [B, X, Y]
    exact_mod_cast hsumLt
  have hVnum : -4 < B - X - Y + w := by
    rcases hw with hw | hw
    · rw [hw]
      dsimp [B, X, Y]
      omega
    · rw [hw]
      dsimp [B, X, Y]
      omega
  have hVnonneg : 0 ≤ V := by omega
  have hSnonneg : 0 ≤ S := by
    have hXY : 0 ≤ X + Y := by positivity
    omega
  have hTnonneg : 0 ≤ T := by
    rcases hw with hw | hw
    · have hzx : (z : ℤ) ≤ X := by
        dsimp [X]
        exact_mod_cast hzy.trans hyx
      rw [hw] at hT4 hV4
      omega
    · have hX : 0 ≤ X := by positivity
      have hz0 : 0 ≤ (z : ℤ) := by positivity
      rw [hw] at hT4 hV4
      omega
  have hUnonneg : 0 ≤ U := by
    rcases hw with hw | hw
    · have hzyInt : (z : ℤ) ≤ Y := by
        dsimp [Y]
        exact_mod_cast hzy
      rw [hw] at hU4 hV4
      omega
    · have hY : 0 ≤ Y := by positivity
      have hz0 : 0 ≤ (z : ℤ) := by positivity
      rw [hw] at hU4 hV4
      omega
  refine ⟨S.toNat, T.toNat, U.toNat, V.toNat, ?_, ?_⟩
  · rw [← Int.ofNat_inj]
    push_cast
    rw [Int.toNat_of_nonneg hSnonneg, Int.toNat_of_nonneg hTnonneg,
      Int.toNat_of_nonneg hUnonneg, Int.toNat_of_nonneg hVnonneg]
    exact hfourSq.symm
  · rw [← Int.ofNat_inj]
    push_cast
    rw [Int.toNat_of_nonneg hSnonneg, Int.toNat_of_nonneg hTnonneg,
      Int.toNat_of_nonneg hUnonneg, Int.toNat_of_nonneg hVnonneg]
    exact hsumInt.symm

end

end Nat

namespace MetaMathlibExt

private theorem fermatPoly_of_fin_sum {s n N : ℕ} (hN : N ≤ s) (f : Fin N → ℕ)
    (hn : n = ∑ i, Nat.polygonalNumber s (f i)) :
    ∃ (t : Finset ℕ) (k : ℕ → ℕ), t.card ≤ s ∧
      n = ∑ i ∈ t, Nat.polygonalNumber s (k i) := by
  let k : ℕ → ℕ := fun i ↦ if h : i < N then f ⟨i, h⟩ else 0
  refine ⟨Finset.range N, k, by simpa using hN, ?_⟩
  rw [hn, ← Fin.sum_univ_eq_sum_range (fun i ↦ Nat.polygonalNumber s (k i)) N]
  apply Finset.sum_congr rfl
  intro i hi
  simp [k, i.isLt]

private theorem fermatPoly_four_polygonal_sum {m d b p q u v : ℕ}
    (hsq : 2 * d + b = p ^ 2 + q ^ 2 + u ^ 2 + v ^ 2)
    (hsum : b = p + q + u + v) :
    m * d + b = Nat.polygonalNumber (m + 2) p + Nat.polygonalNumber (m + 2) q +
      Nat.polygonalNumber (m + 2) u + Nat.polygonalNumber (m + 2) v := by
  have hp : 2 * Nat.choose p 2 + p = p ^ 2 := by
    simpa [Nat.polygonalNumber] using Nat.polygonalNumber_four p
  have hq : 2 * Nat.choose q 2 + q = q ^ 2 := by
    simpa [Nat.polygonalNumber] using Nat.polygonalNumber_four q
  have hu : 2 * Nat.choose u 2 + u = u ^ 2 := by
    simpa [Nat.polygonalNumber] using Nat.polygonalNumber_four u
  have hv : 2 * Nat.choose v 2 + v = v ^ 2 := by
    simpa [Nat.polygonalNumber] using Nat.polygonalNumber_four v
  have hchoose : Nat.choose p 2 + Nat.choose q 2 + Nat.choose u 2 + Nat.choose v 2 = d := by
    omega
  simp only [Nat.polygonalNumber]
  have hm : m + 2 - 2 = m := by omega
  rw [hm]
  calc
    m * d + b = m * (Nat.choose p 2 + Nat.choose q 2 + Nat.choose u 2 +
        Nat.choose v 2) + (p + q + u + v) := by rw [hchoose, hsum]
    _ = m * Nat.choose p 2 + p + (m * Nat.choose q 2 + q) +
        (m * Nat.choose u 2 + u) + (m * Nat.choose v 2 + v) := by ring

private theorem fermatPoly_four_add_ones {m n p q u v r : ℕ} (hm : 2 ≤ m)
    (hr : r ≤ m - 2)
    (hn : n = Nat.polygonalNumber (m + 2) p + Nat.polygonalNumber (m + 2) q +
      Nat.polygonalNumber (m + 2) u + Nat.polygonalNumber (m + 2) v + r) :
    ∃ (t : Finset ℕ) (k : ℕ → ℕ), t.card ≤ m + 2 ∧
      n = ∑ i ∈ t, Nat.polygonalNumber (m + 2) (k i) := by
  let f : Fin (r + 4) → ℕ :=
    Fin.cases p (Fin.cases q (Fin.cases u (Fin.cases v (fun _ : Fin r ↦ 1))))
  apply fermatPoly_of_fin_sum (f := f)
  · omega
  rw [hn]
  simp [f, Fin.sum_univ_succ]
  omega

private def fermatPolyRoute (m n : ℕ) : Prop :=
  ∃ d b r : ℕ, b % 2 = 1 ∧ r ≤ m - 2 ∧ n = m * d + b + r ∧
    (b : ℤ) ^ 2 - 4 * b < 8 * d ∧ 6 * (d : ℤ) < b ^ 2 - b + 4

private theorem fermatPolyRoute_sound {m n : ℕ} (hm : 3 ≤ m) (h : fermatPolyRoute m n) :
    ∃ (t : Finset ℕ) (k : ℕ → ℕ), t.card ≤ m + 2 ∧
      n = ∑ i ∈ t, Nat.polygonalNumber (m + 2) (k i) := by
  obtain ⟨d, b, r, hb, hr, hn, hlo, hhi⟩ := h
  have ha : (2 * d + b) % 2 = 1 := by omega
  have hlo' : (b : ℤ) ^ 2 < 4 * (2 * (d : ℤ) + b) := by linarith
  have hhi' : 3 * (2 * (d : ℤ) + b) < (b : ℤ) ^ 2 + 2 * b + 4 := by linarith
  have hloNat : b ^ 2 < 4 * (2 * d + b) := by exact_mod_cast hlo'
  have hhiNat : 3 * (2 * d + b) < b ^ 2 + 2 * b + 4 := by exact_mod_cast hhi'
  obtain ⟨p, q, u, v, hsq, hsum⟩ :=
    Nat.exists_sum_four_sq_eq_and_sum_eq_of_odd ha hb hloNat hhiNat
  have hpoly := fermatPoly_four_polygonal_sum (m := m) hsq hsum
  have hnpoly : n = Nat.polygonalNumber (m + 2) p + Nat.polygonalNumber (m + 2) q +
      Nat.polygonalNumber (m + 2) u + Nat.polygonalNumber (m + 2) v + r := by omega
  exact fermatPoly_four_add_ones (m := m) (p := p) (q := q) (u := u) (v := v)
    (by omega) hr hnpoly

private theorem fermatPoly_large_lower_ineq {m q rho d c r : ℕ}
    (hm : 3 ≤ m) (hc : 2 ≤ c) (hr : r ≤ m - 2)
    (heq : m * d + c + r = m * q + rho)
    (hbound : 3 * (c : ℤ) ^ 2 - 4 * c + 8 < 24 * q) :
    (c : ℤ) ^ 2 - 4 * c < 8 * d := by
  have hmZ : (3 : ℤ) ≤ m := by exact_mod_cast hm
  have hcZ : (2 : ℤ) ≤ c := by exact_mod_cast hc
  have hrZ : (r : ℤ) + 2 ≤ m := by exact_mod_cast (show r + 2 ≤ m by omega)
  have heqZ : (m : ℤ) * d + c + r = m * q + rho := by exact_mod_cast heq
  let A : ℤ := 8 * q - c ^ 2 + 4 * c - 8
  have hA : 0 < A := by
    dsimp [A]
    nlinarith
  have hmulA : 3 * A ≤ (m : ℤ) * A := mul_le_mul_of_nonneg_right hmZ hA.le
  have hmul : (m : ℤ) * ((c : ℤ) ^ 2 - 4 * c) < 8 * m * d := by
    dsimp [A] at hmulA
    nlinarith
  have hmul' : (m : ℤ) * ((c : ℤ) ^ 2 - 4 * c) < m * (8 * d) := by
    calc
      (m : ℤ) * ((c : ℤ) ^ 2 - 4 * c) < 8 * m * d := hmul
      _ = m * (8 * d) := by ring
  exact (Int.mul_lt_mul_left (show (0 : ℤ) < m by positivity)).mp hmul'

private theorem fermatPoly_large_upper_ineq {q d b c : ℕ} (hdq : d ≤ q) (hb : 1 ≤ b)
    (hbc : b ≤ c) (hgood : 6 * (q : ℤ) < b ^ 2 - b + 4) :
    6 * (d : ℤ) < c ^ 2 - c + 4 := by
  have hdqZ : (d : ℤ) ≤ q := by exact_mod_cast hdq
  have hbZ : (1 : ℤ) ≤ b := by exact_mod_cast hb
  have hbcZ : (b : ℤ) ≤ c := by exact_mod_cast hbc
  have hprod : 0 ≤ ((c : ℤ) - b) * (c + b - 1) :=
    mul_nonneg (by omega) (by omega)
  nlinarith

private theorem fermatPoly_large_candidates (q : ℕ) (hq : 120 ≤ q) :
    ∃ b : ℕ, b % 2 = 1 ∧ 2 ≤ b ∧
      6 * (q : ℤ) < b ^ 2 - b + 4 ∧
      ∀ c : ℕ, b ≤ c → c ≤ b + 2 →
        3 * (c : ℤ) ^ 2 - 4 * c + 8 < 24 * q := by
  let u := Nat.sqrt (6 * q)
  let b0 := if u % 2 = 0 then u + 1 else u + 2
  let good : Prop := 6 * (q : ℤ) < (b0 : ℤ) ^ 2 - b0 + 4
  let b := if good then b0 else b0 + 2
  have huSq : u ^ 2 ≤ 6 * q := by simpa [u] using Nat.sqrt_le' (6 * q)
  have huNext : 6 * q < (u + 1) ^ 2 := by
    simpa [u, Nat.succ_eq_add_one, pow_two] using Nat.lt_succ_sqrt (6 * q)
  have hu26 : 26 ≤ u := by
    change 26 ≤ Nat.sqrt (6 * q)
    rw [Nat.le_sqrt]
    nlinarith
  have hb0bounds : u + 1 ≤ b0 ∧ b0 ≤ u + 2 := by
    dsimp [b0]
    split <;> omega
  have hb0odd : b0 % 2 = 1 := by
    dsimp [b0]
    split <;> rename_i h
    · omega
    · have huMod := Nat.mod_lt u (by norm_num : 0 < 2)
      omega
  have hbbounds : b0 ≤ b ∧ b ≤ b0 + 2 := by
    dsimp [b]
    split <;> omega
  have hbodd : b % 2 = 1 := by
    dsimp [b]
    split <;> omega
  have hb2 : 2 ≤ b := by omega
  have hgood : 6 * (q : ℤ) < b ^ 2 - b + 4 := by
    dsimp [b]
    split
    · assumption
    · have huNextZ : 6 * (q : ℤ) < ((u : ℤ) + 1) ^ 2 := by exact_mod_cast huNext
      have hb0Z : (u : ℤ) + 1 ≤ b0 := by exact_mod_cast hb0bounds.1
      have hprod : 0 ≤ ((b0 : ℤ) - (u + 1)) * (b0 + (u + 1)) := by positivity
      have htarget : 6 * (q : ℤ) < ((b0 : ℤ) + 2) ^ 2 - (b0 + 2) + 4 := by
        nlinarith only [huNextZ, hb0Z, hprod]
      simpa only [Nat.cast_add, Nat.cast_ofNat] using htarget
  refine ⟨b, hbodd, hb2, hgood, ?_⟩
  intro c hbc hcb
  by_cases hg : good
  · have hbEq : b = b0 := by simp [b, hg]
    have hc : c ≤ u + 4 := by omega
    have hcLower : u + 1 ≤ c := by omega
    have haux : 20 * u + 52 < 6 * q := by nlinarith
    have hauxZ : 20 * (u : ℤ) + 52 < 6 * q := by exact_mod_cast haux
    have huSqZ : (u : ℤ) ^ 2 ≤ 6 * q := by exact_mod_cast huSq
    have hcZ : (c : ℤ) ≤ u + 4 := by exact_mod_cast hc
    have hcLowerZ : (u : ℤ) + 1 ≤ c := by exact_mod_cast hcLower
    have hprod : 0 ≤ ((u : ℤ) + 4 - c) * ((u : ℤ) + 4 + c) := by positivity
    nlinarith only [hauxZ, huSqZ, hcLowerZ, hprod]
  · have huEven : u % 2 = 0 := by
      by_contra huEven
      have huMod := Nat.mod_lt u (by norm_num : 0 < 2)
      have hb0Eq : b0 = u + 2 := by simp [b0, huEven]
      have huNextZ : 6 * (q : ℤ) < ((u : ℤ) + 1) ^ 2 := by exact_mod_cast huNext
      have : good := by
        dsimp [good]
        rw [hb0Eq]
        change 6 * (q : ℤ) < ((u : ℤ) + 2) ^ 2 - ((u : ℤ) + 2) + 4
        nlinarith only [huNextZ]
      exact hg this
    have hb0Eq : b0 = u + 1 := by simp [b0, huEven]
    have hbEq : b = b0 + 2 := by simp [b, hg]
    have hc : c ≤ u + 5 := by omega
    have hnot : (b0 : ℤ) ^ 2 - b0 + 4 ≤ 6 * q := by
      dsimp [good] at hg
      omega
    rw [hb0Eq] at hnot
    norm_num only [Nat.cast_add, Nat.cast_one] at hnot
    have hcZ : (c : ℤ) ≤ u + 5 := by exact_mod_cast hc
    have hu26Z : (26 : ℤ) ≤ u := by exact_mod_cast hu26
    have hprodC : 0 ≤ ((u : ℤ) + 5 - c) * ((u : ℤ) + 5 + c) := by positivity
    have hprodU : 0 ≤ ((u : ℤ) - 26) * ((u : ℤ) + 4) := by positivity
    nlinarith only [hnot, hprodC, hprodU]

private theorem fermatPolyRoute_of_large {m n : ℕ} (hm : 3 ≤ m) (hn : 120 * m ≤ n) :
    fermatPolyRoute m n := by
  let q := n / m
  let rho := n % m
  have hmpos : 0 < m := by omega
  have hq : 120 ≤ q := by
    dsimp [q]
    exact (Nat.le_div_iff_mul_le hmpos).mpr hn
  have hdecomp : n = m * q + rho := by
    have h := Nat.div_add_mod n m
    dsimp [q, rho]
    omega
  obtain ⟨b, hbodd, hb2, hgood, hbound⟩ := fermatPoly_large_candidates q hq
  have hbq : b + 2 ≤ q := by
    have h := hbound (b + 2) (by omega) (by omega)
    by_contra hc
    push Not at hc
    norm_num only [Nat.cast_add, Nat.cast_ofNat] at h
    have hqZ : (120 : ℤ) ≤ q := by exact_mod_cast hq
    have hcZ : (q : ℤ) < b + 2 := by exact_mod_cast hc
    nlinarith
  have hbn : b ≤ n := by
    have hqn : q ≤ n := by
      dsimp [q]
      exact Nat.div_le_self n m
    omega
  let r0 := (n - b) % m
  let d := (n - b) / m
  have hr0lt : r0 < m := by simpa [r0] using Nat.mod_lt (n - b) hmpos
  have hn0 : n = m * d + b + r0 := by
    have h := Nat.div_add_mod (n - b) m
    change m * d + r0 = n - b at h
    omega
  have hdq : d ≤ q := by
    dsimp [d, q]
    exact Nat.div_le_div_right (Nat.sub_le n b)
  by_cases hr : r0 ≤ m - 2
  · refine ⟨d, b, r0, hbodd, hr, hn0, ?_, ?_⟩
    · apply fermatPoly_large_lower_ineq (m := m) (q := q) (rho := rho)
        (d := d) (c := b) (r := r0) hm hb2 hr
      · omega
      · exact hbound b (by omega) (by omega)
    · exact fermatPoly_large_upper_ineq (q := q) (b := b) hdq (by omega) (by omega) hgood
  · have hrEq : r0 = m - 1 := by omega
    have hr' : m - 3 ≤ m - 2 := by omega
    have heq : n = m * d + (b + 2) + (m - 3) := by omega
    refine ⟨d, b + 2, m - 3, by omega, hr', heq, ?_, ?_⟩
    · apply fermatPoly_large_lower_ineq (m := m) (q := q) (rho := rho)
        (d := d) (c := b + 2) (r := m - 3) hm (by omega) hr'
      · omega
      · exact hbound (b + 2) (by omega) (by omega)
    · exact fermatPoly_large_upper_ineq (q := q) (b := b) hdq (by omega) (by omega) hgood

private def fermatPolyRouteAtB (m n b : ℕ) : Bool :=
  let r := (n - b) % m
  let d := (n - b) / m
  decide (b ≤ n ∧ r ≤ m - 2 ∧
    (b : ℤ) ^ 2 - 4 * b < 8 * d ∧ 6 * (d : ℤ) < (b : ℤ) ^ 2 - b + 4)

private def fermatPolyRouteB (m n : ℕ) : Bool :=
  (List.range 17).any fun j ↦ fermatPolyRouteAtB m n (2 * j + 1)

private theorem fermatPolyRouteB_sound {m n : ℕ}
    (h : fermatPolyRouteB m n = true) : fermatPolyRoute m n := by
  rw [fermatPolyRouteB, List.any_eq_true] at h
  obtain ⟨j, _, h⟩ := h
  let b := 2 * j + 1
  let r := (n - b) % m
  let d := (n - b) / m
  change fermatPolyRouteAtB m n b = true at h
  simp only [fermatPolyRouteAtB, decide_eq_true_eq] at h
  change b ≤ n ∧ r ≤ m - 2 ∧
    (b : ℤ) ^ 2 - 4 * b < 8 * d ∧ 6 * (d : ℤ) < (b : ℤ) ^ 2 - b + 4 at h
  obtain ⟨hbn, hr, hlo, hhi⟩ := h
  have hb : b % 2 = 1 := by simp [b]
  have hnsub : n - b = m * d + r := by
    simpa [d, r] using (Nat.div_add_mod (n - b) m).symm
  have hn : n = m * d + b + r := by omega
  exact ⟨d, b, r, hb, hr, hn, hlo, hhi⟩

private theorem fermatPoly_list_add_ones {m n r : ℕ} (ks : List ℕ)
    (hlen : ks.length + r ≤ m + 2)
    (hn : n = (ks.map (Nat.polygonalNumber (m + 2))).sum + r) :
    ∃ (t : Finset ℕ) (k : ℕ → ℕ), t.card ≤ m + 2 ∧
      n = ∑ i ∈ t, Nat.polygonalNumber (m + 2) (k i) := by
  let all := ks ++ List.replicate r 1
  apply fermatPoly_of_fin_sum (f := fun i ↦ all.get i)
  · simpa [all] using hlen
  have hof : List.ofFn (fun i ↦ Nat.polygonalNumber (m + 2) (all.get i)) =
      all.map (Nat.polygonalNumber (m + 2)) := by
    simp
  rw [hn, ← List.sum_ofFn]
  rw [hof]
  simp [all]

private def fermatPolyFamB (m n : ℕ) : Bool :=
  decide (n = m * 2 + 4 ∨ n = m * 3 + 4 ∨ n = m * 4 + 6 ∨
    n = m * 5 + 6 ∨ n = m * 6 + 6 ∨ n = m * 8 + 8 ∨
    n = m * 9 + 8 ∨ n = m * 10 + 8 ∨ n = m * 13 + 10 ∨
    n = m * 14 + 10 ∨ n = m * 15 + 10 ∨ n = m * 19 + 12 ∨
    n = m * 20 + 12 ∨ n = m * 21 + 12 ∨ n = m * 27 + 14 ∨
    n = m * 28 + 14 ∨ n = m * 36 + 16)

private theorem fermatPolyFamB_sound {m n : ℕ} (hm : 3 ≤ m)
    (h : fermatPolyFamB m n = true) :
    ∃ (t : Finset ℕ) (k : ℕ → ℕ), t.card ≤ m + 2 ∧
      n = ∑ i ∈ t, Nat.polygonalNumber (m + 2) (k i) := by
  have hf := of_decide_eq_true h
  rcases hf with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · apply fermatPoly_list_add_ones (ks := [2, 2]) (r := 0)
    · norm_num
    · rw [h]
      norm_num [Nat.polygonalNumber, Nat.choose]
      omega
  · apply fermatPoly_list_add_ones (ks := [3]) (r := 1)
    · norm_num
    · rw [h]
      norm_num [Nat.polygonalNumber, Nat.choose]
  · apply fermatPoly_list_add_ones (ks := [2, 3]) (r := 1)
    · norm_num
      omega
    · rw [h]
      norm_num [Nat.polygonalNumber, Nat.choose]
      omega
  · apply fermatPoly_list_add_ones (ks := [2, 2, 2, 2]) (r := m - 2)
    · norm_num
      omega
    · rw [h]
      norm_num [Nat.polygonalNumber, Nat.choose]
      omega
  · apply fermatPoly_list_add_ones (ks := [4]) (r := 2)
    · norm_num
      omega
    · rw [h]
      norm_num [Nat.polygonalNumber, Nat.choose]
  · apply fermatPoly_list_add_ones (ks := [2, 2, 4]) (r := 0)
    · norm_num
      omega
    · rw [h]
      norm_num [Nat.polygonalNumber, Nat.choose]
      omega
  · apply fermatPoly_list_add_ones (ks := [3, 4]) (r := 1)
    · norm_num
      omega
    · rw [h]
      norm_num [Nat.polygonalNumber, Nat.choose]
      omega
  · apply fermatPoly_list_add_ones (ks := [5]) (r := 3)
    · norm_num
      omega
    · rw [h]
      norm_num [Nat.polygonalNumber, Nat.choose]
  · apply fermatPoly_list_add_ones (ks := [3, 5]) (r := 2)
    · norm_num
      omega
    · rw [h]
      norm_num [Nat.polygonalNumber, Nat.choose]
      omega
  · apply fermatPoly_list_add_ones (ks := [2, 3, 5]) (r := 0)
    · norm_num
      omega
    · rw [h]
      norm_num [Nat.polygonalNumber, Nat.choose]
      omega
  · apply fermatPoly_list_add_ones (ks := [6]) (r := 4)
    · norm_num
      omega
    · rw [h]
      norm_num [Nat.polygonalNumber, Nat.choose]
  · apply fermatPoly_list_add_ones (ks := [2, 3, 6]) (r := 1)
    · norm_num
      omega
    · rw [h]
      norm_num [Nat.polygonalNumber, Nat.choose]
      omega
  · apply fermatPoly_list_add_ones (ks := [5, 5]) (r := 2)
    · norm_num
      omega
    · rw [h]
      norm_num [Nat.polygonalNumber, Nat.choose]
      omega
  · apply fermatPoly_list_add_ones (ks := [4, 6]) (r := 2)
    · norm_num
      omega
    · rw [h]
      norm_num [Nat.polygonalNumber, Nat.choose]
      omega
  · apply fermatPoly_list_add_ones (ks := [4, 7]) (r := 3)
    · norm_num
      omega
    · rw [h]
      norm_num [Nat.polygonalNumber, Nat.choose]
      omega
  · apply fermatPoly_list_add_ones (ks := [2, 4, 7]) (r := 1)
    · norm_num
      omega
    · rw [h]
      norm_num [Nat.polygonalNumber, Nat.choose]
      omega
  · apply fermatPoly_list_add_ones (ks := [6, 7]) (r := 3)
    · norm_num
      omega
    · rw [h]
      norm_num [Nat.polygonalNumber, Nat.choose]
      omega

private theorem fermatPoly_ones {m n : ℕ} (hn : n ≤ m + 2) :
    ∃ (t : Finset ℕ) (k : ℕ → ℕ), t.card ≤ m + 2 ∧
      n = ∑ i ∈ t, Nat.polygonalNumber (m + 2) (k i) := by
  apply fermatPoly_of_fin_sum (f := fun _ : Fin n ↦ 1) hn
  simp

private def fermatPolySmallGoodB (m n : ℕ) : Bool :=
  fermatPolyRouteB m n || fermatPolyFamB m n || decide (n ≤ m + 2)

private theorem fermatPolySmallGoodB_sound {m n : ℕ} (hm : 3 ≤ m)
    (h : fermatPolySmallGoodB m n = true) :
    ∃ (t : Finset ℕ) (k : ℕ → ℕ), t.card ≤ m + 2 ∧
      n = ∑ i ∈ t, Nat.polygonalNumber (m + 2) (k i) := by
  simp only [fermatPolySmallGoodB, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with (h | h) | h
  · exact fermatPolyRoute_sound hm (fermatPolyRouteB_sound h)
  · exact fermatPolyFamB_sound hm h
  · exact fermatPoly_ones (by omega)

private theorem fermatPoly_check_m3 : ∀ n < 120 * 3, fermatPolySmallGoodB 3 n = true := by
  decide +kernel

private theorem fermatPoly_check_m4 : ∀ n < 120 * 4, fermatPolySmallGoodB 4 n = true := by
  decide +kernel

private theorem fermatPoly_check_m5 : ∀ n < 120 * 5, fermatPolySmallGoodB 5 n = true := by
  decide +kernel

private theorem fermatPoly_check_m6 : ∀ n < 120 * 6, fermatPolySmallGoodB 6 n = true := by
  decide +kernel

private theorem fermatPoly_check_m7 : ∀ n < 120 * 7, fermatPolySmallGoodB 7 n = true := by
  decide +kernel

private theorem fermatPoly_check_m8 : ∀ n < 120 * 8, fermatPolySmallGoodB 8 n = true := by
  decide +kernel

private theorem fermatPoly_check_m9 : ∀ n < 120 * 9, fermatPolySmallGoodB 9 n = true := by
  decide +kernel

private theorem fermatPoly_check_m10 : ∀ n < 120 * 10, fermatPolySmallGoodB 10 n = true := by
  decide +kernel

private theorem fermatPoly_check_m11 : ∀ n < 120 * 11, fermatPolySmallGoodB 11 n = true := by
  decide +kernel

private theorem fermatPoly_check_m12 : ∀ n < 120 * 12, fermatPolySmallGoodB 12 n = true := by
  decide +kernel

private theorem fermatPoly_check_m13 : ∀ n < 120 * 13, fermatPolySmallGoodB 13 n = true := by
  decide +kernel

private theorem fermatPoly_check_m14 : ∀ n < 120 * 14, fermatPolySmallGoodB 14 n = true := by
  decide +kernel

private theorem fermatPoly_check_m15 : ∀ n < 120 * 15, fermatPolySmallGoodB 15 n = true := by
  decide +kernel

private theorem fermatPoly_check_m16 : ∀ n < 120 * 16, fermatPolySmallGoodB 16 n = true := by
  decide +kernel

private theorem fermatPoly_check_m17 : ∀ n < 120 * 17, fermatPolySmallGoodB 17 n = true := by
  decide +kernel

private theorem fermatPoly_check_m18 : ∀ n < 120 * 18, fermatPolySmallGoodB 18 n = true := by
  decide +kernel

private theorem fermatPoly_check_m19 : ∀ n < 120 * 19, fermatPolySmallGoodB 19 n = true := by
  decide +kernel

private theorem fermatPoly_check_m20 : ∀ n < 120 * 20, fermatPolySmallGoodB 20 n = true := by
  decide +kernel

private theorem fermatPoly_check_m21 : ∀ n < 120 * 21, fermatPolySmallGoodB 21 n = true := by
  decide +kernel

private theorem fermatPoly_check_m22 : ∀ n < 120 * 22, fermatPolySmallGoodB 22 n = true := by
  decide +kernel

-- The larger bounded tables need additional kernel reduction depth.
set_option maxRecDepth 2000 in
private theorem fermatPoly_check_m23 : ∀ n < 120 * 23, fermatPolySmallGoodB 23 n = true := by
  decide +kernel

set_option maxRecDepth 2000 in
private theorem fermatPoly_check_m24 : ∀ n < 120 * 24, fermatPolySmallGoodB 24 n = true := by
  decide +kernel

set_option maxRecDepth 2000 in
private theorem fermatPoly_check_m25 : ∀ n < 120 * 25, fermatPolySmallGoodB 25 n = true := by
  decide +kernel

set_option maxRecDepth 2000 in
private theorem fermatPoly_check_m26 : ∀ n < 120 * 26, fermatPolySmallGoodB 26 n = true := by
  decide +kernel

set_option maxRecDepth 2000 in
private theorem fermatPoly_check_m27 : ∀ n < 120 * 27, fermatPolySmallGoodB 27 n = true := by
  decide +kernel

set_option maxRecDepth 2000 in
private theorem fermatPoly_check_m28 : ∀ n < 120 * 28, fermatPolySmallGoodB 28 n = true := by
  decide +kernel

set_option maxRecDepth 2000 in
private theorem fermatPoly_check_m29 : ∀ n < 120 * 29, fermatPolySmallGoodB 29 n = true := by
  decide +kernel

set_option maxRecDepth 2000 in
private theorem fermatPoly_check_m30 : ∀ n < 120 * 30, fermatPolySmallGoodB 30 n = true := by
  decide +kernel

set_option maxRecDepth 2000 in
private theorem fermatPoly_check_m31 : ∀ n < 120 * 31, fermatPolySmallGoodB 31 n = true := by
  decide +kernel

set_option maxRecDepth 2000 in
private theorem fermatPoly_check_m32 : ∀ n < 120 * 32, fermatPolySmallGoodB 32 n = true := by
  decide +kernel

set_option maxRecDepth 2000 in
private theorem fermatPoly_check_m33 : ∀ n < 120 * 33, fermatPolySmallGoodB 33 n = true := by
  decide +kernel


private theorem fermatPoly_check_small_m {m n : ℕ} (hm : 3 ≤ m) (hm34 : m < 34)
    (hn : n < 120 * m) : fermatPolySmallGoodB m n = true := by
  interval_cases m
  · exact fermatPoly_check_m3 n (by omega)
  · exact fermatPoly_check_m4 n (by omega)
  · exact fermatPoly_check_m5 n (by omega)
  · exact fermatPoly_check_m6 n (by omega)
  · exact fermatPoly_check_m7 n (by omega)
  · exact fermatPoly_check_m8 n (by omega)
  · exact fermatPoly_check_m9 n (by omega)
  · exact fermatPoly_check_m10 n (by omega)
  · exact fermatPoly_check_m11 n (by omega)
  · exact fermatPoly_check_m12 n (by omega)
  · exact fermatPoly_check_m13 n (by omega)
  · exact fermatPoly_check_m14 n (by omega)
  · exact fermatPoly_check_m15 n (by omega)
  · exact fermatPoly_check_m16 n (by omega)
  · exact fermatPoly_check_m17 n (by omega)
  · exact fermatPoly_check_m18 n (by omega)
  · exact fermatPoly_check_m19 n (by omega)
  · exact fermatPoly_check_m20 n (by omega)
  · exact fermatPoly_check_m21 n (by omega)
  · exact fermatPoly_check_m22 n (by omega)
  · exact fermatPoly_check_m23 n (by omega)
  · exact fermatPoly_check_m24 n (by omega)
  · exact fermatPoly_check_m25 n (by omega)
  · exact fermatPoly_check_m26 n (by omega)
  · exact fermatPoly_check_m27 n (by omega)
  · exact fermatPoly_check_m28 n (by omega)
  · exact fermatPoly_check_m29 n (by omega)
  · exact fermatPoly_check_m30 n (by omega)
  · exact fermatPoly_check_m31 n (by omega)
  · exact fermatPoly_check_m32 n (by omega)
  · exact fermatPoly_check_m33 n (by omega)

private theorem fermatPoly_small_of_small_m {m n : ℕ} (hm : 3 ≤ m) (hm34 : m < 34)
    (hn : n < 120 * m) :
    ∃ (t : Finset ℕ) (k : ℕ → ℕ), t.card ≤ m + 2 ∧
      n = ∑ i ∈ t, Nat.polygonalNumber (m + 2) (k i) :=
  fermatPolySmallGoodB_sound hm (fermatPoly_check_small_m hm hm34 hn)

private def fermatPolyRoutePairAtB (q rho b : ℕ) : Bool :=
  decide ((b ≤ rho ∧ (b : ℤ) ^ 2 - 4 * b < 8 * (q : ℤ) ∧
      6 * (q : ℤ) < (b : ℤ) ^ 2 - b + 4) ∨
    (rho + 2 ≤ b ∧ 1 ≤ q ∧
      (b : ℤ) ^ 2 - 4 * b < 8 * ((q - 1 : ℕ) : ℤ) ∧
      6 * ((q - 1 : ℕ) : ℤ) < (b : ℤ) ^ 2 - b + 4))

private def fermatPolyRoutePairB (q rho : ℕ) : Bool :=
  (List.range 17).any fun j ↦ fermatPolyRoutePairAtB q rho (2 * j + 1)

private theorem fermatPolyRoutePairB_sound {m n q rho : ℕ} (hm : 34 ≤ m) (hrho : rho < m)
    (hn : n = m * q + rho) (h : fermatPolyRoutePairB q rho = true) :
    fermatPolyRoute m n := by
  rw [fermatPolyRoutePairB, List.any_eq_true] at h
  obtain ⟨j, hjmem, h⟩ := h
  let b := 2 * j + 1
  change fermatPolyRoutePairAtB q rho b = true at h
  simp only [fermatPolyRoutePairAtB, decide_eq_true_eq] at h
  have hj : j < 17 := List.mem_range.mp hjmem
  have hb34 : b < 34 := by simp [b]; omega
  have hb : b % 2 = 1 := by simp [b]
  rcases h with ⟨hbrho, hlo, hhi⟩ | ⟨hbrho, hq, hlo, hhi⟩
  · refine ⟨q, b, rho - b, hb, ?_, ?_, hlo, hhi⟩
    · have hb1 : 1 ≤ b := by
        have hbmod := Nat.mod_lt b (by norm_num : 0 < 2)
        omega
      omega
    · omega
  · have hbm : b ≤ m + rho := by omega
    refine ⟨q - 1, b, m + rho - b, hb, ?_, ?_, hlo, hhi⟩
    · omega
    · have hmul : m * (q - 1) + m = m * q := by
        calc
          m * (q - 1) + m = m * ((q - 1) + 1) := by ring
          _ = m * q := by rw [Nat.sub_add_cancel hq]
      omega

private theorem fermatPolyRoutePairB_high_sound {m n q rho : ℕ} (hm : 34 ≤ m)
    (hrho : rho < m) (hrho34 : 34 ≤ rho) (hn : n = m * q + rho)
    (h : fermatPolyRoutePairB q 34 = true) : fermatPolyRoute m n := by
  rw [fermatPolyRoutePairB, List.any_eq_true] at h
  obtain ⟨j, hjmem, h⟩ := h
  let b := 2 * j + 1
  change fermatPolyRoutePairAtB q 34 b = true at h
  simp only [fermatPolyRoutePairAtB, decide_eq_true_eq] at h
  have hj : j < 17 := List.mem_range.mp hjmem
  have hblt : b < 34 := by simp [b]; omega
  have hb : b % 2 = 1 := by simp [b]
  rcases h with ⟨hb34, hlo, hhi⟩ | ⟨hb36, hq, hlo, hhi⟩
  · refine ⟨q, b, rho - b, hb, ?_, ?_, hlo, hhi⟩
    · have hb1 : 1 ≤ b := by
        have hbmod := Nat.mod_lt b (by norm_num : 0 < 2)
        omega
      omega
    · omega
  · omega

private def fermatPolyFamPairB (q rho : ℕ) : Bool :=
  decide ((q = 2 ∧ rho = 4) ∨ (q = 3 ∧ rho = 4) ∨ (q = 4 ∧ rho = 6) ∨
    (q = 5 ∧ rho = 6) ∨ (q = 6 ∧ rho = 6) ∨ (q = 8 ∧ rho = 8) ∨
    (q = 9 ∧ rho = 8) ∨ (q = 10 ∧ rho = 8) ∨ (q = 13 ∧ rho = 10) ∨
    (q = 14 ∧ rho = 10) ∨ (q = 15 ∧ rho = 10) ∨ (q = 19 ∧ rho = 12) ∨
    (q = 20 ∧ rho = 12) ∨ (q = 21 ∧ rho = 12) ∨ (q = 27 ∧ rho = 14) ∨
    (q = 28 ∧ rho = 14) ∨ (q = 36 ∧ rho = 16))

private def fermatPolyPairGoodB (q rho : ℕ) : Bool :=
  fermatPolyRoutePairB q rho || fermatPolyFamPairB q rho ||
    decide (q = 0 ∨ (q = 1 ∧ rho ≤ 2))

private theorem fermatPoly_check_large_pairs :
    ∀ q < 120, ∀ rho ≤ 34, fermatPolyPairGoodB q rho = true := by
  decide +kernel

private theorem fermatPolyFamPairB_lift {m n q rho : ℕ} (hn : n = m * q + rho)
    (h : fermatPolyFamPairB q rho = true) : fermatPolyFamB m n = true := by
  simp only [fermatPolyFamPairB, decide_eq_true_eq] at h
  simp only [fermatPolyFamB, decide_eq_true_eq]
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega

private theorem fermatPoly_small_of_large_m {m n : ℕ} (hm : 34 ≤ m) (hn : n < 120 * m) :
    ∃ (t : Finset ℕ) (k : ℕ → ℕ), t.card ≤ m + 2 ∧
      n = ∑ i ∈ t, Nat.polygonalNumber (m + 2) (k i) := by
  let q := n / m
  let rho := n % m
  have hmpos : 0 < m := by omega
  have hq : q < 120 := by
    dsimp [q]
    apply (Nat.div_lt_iff_lt_mul hmpos).mpr
    simpa [mul_comm] using hn
  have hrho : rho < m := by simpa [rho] using Nat.mod_lt n hmpos
  have hdecomp : n = m * q + rho := by
    have h := Nat.div_add_mod n m
    dsimp [q, rho]
    omega
  by_cases hrho34 : rho ≤ 34
  · have hgood := fermatPoly_check_large_pairs q hq rho hrho34
    simp only [fermatPolyPairGoodB, Bool.or_eq_true, decide_eq_true_eq] at hgood
    rcases hgood with (hroute | hfam) | hones
    · exact fermatPolyRoute_sound (by omega) <|
        fermatPolyRoutePairB_sound hm hrho hdecomp hroute
    · exact fermatPolyFamB_sound (by omega) <|
        fermatPolyFamPairB_lift hdecomp hfam
    · apply fermatPoly_ones
      rcases hones with hq0 | ⟨hq1, hrho2⟩
      · rw [hq0] at hdecomp
        omega
      · rw [hq1] at hdecomp
        omega
  · have hgood := fermatPoly_check_large_pairs q hq 34 (by omega)
    simp only [fermatPolyPairGoodB, Bool.or_eq_true, decide_eq_true_eq] at hgood
    rcases hgood with (hroute | hfam) | hones
    · exact fermatPolyRoute_sound (by omega) <|
        fermatPolyRoutePairB_high_sound hm hrho (by omega) hdecomp hroute
    · have : fermatPolyFamPairB q 34 = false := by simp [fermatPolyFamPairB]
      rw [this] at hfam
      contradiction
    · apply fermatPoly_ones
      rcases hones with hq0 | ⟨hq1, hfalse⟩
      · rw [hq0] at hdecomp
        omega
      · omega

private theorem fermatPoly_three_case (n : ℕ) :
    ∃ (t : Finset ℕ) (k : ℕ → ℕ), t.card ≤ 3 ∧
      n = ∑ i ∈ t, Nat.polygonalNumber 3 (k i) := by
  obtain ⟨x, y, z, hn⟩ := Nat.exists_eq_add_add_triangular n
  let f : Fin 3 → ℕ := Fin.cases x (Fin.cases y (Fin.cases z Fin.elim0))
  apply fermatPoly_of_fin_sum (f := f) (by omega)
  simpa [f, Fin.sum_univ_succ, add_assoc] using hn

private theorem fermatPoly_four_case (n : ℕ) :
    ∃ (t : Finset ℕ) (k : ℕ → ℕ), t.card ≤ 4 ∧
      n = ∑ i ∈ t, Nat.polygonalNumber 4 (k i) := by
  obtain ⟨p, q, u, v, hn⟩ := Nat.sum_four_squares n
  let f : Fin 4 → ℕ :=
    Fin.cases p (Fin.cases q (Fin.cases u (Fin.cases v Fin.elim0)))
  apply fermatPoly_of_fin_sum (f := f) (by omega)
  simp [f, Fin.sum_univ_succ, Nat.polygonalNumber_four]
  omega

@[expose] public section

/-- **Fermat polygonal number theorem.** For every natural number $s \ge 3$, every natural
number $n$ is a sum of at most $s$ $s$-gonal numbers: there are a finite set $T$ with at most $s$
elements and natural numbers $k_i$ for $i \in T$ such that $n = \sum_{i \in T} P_s(k_i)$, where
$P_s(m) = (s - 2)\binom{m}{2} + m$ is the $m$-th $s$-gonal number. The $k_i$ may repeat, and
since $P_s(0) = 0$ the case $n = 0$ is the empty sum.

The cases $s = 3$ and $s = 4$ follow from Gauss's three-triangular-number theorem and Lagrange's
four-square theorem. For $s \ge 5$, Cauchy's lemma and Nathanson's argument for
$n \ge 120(s - 2)$ (Nathanson 1987, Theorem 1) are combined with explicit families of
representations for small $n$ and a finite computation for the remaining cases.

Proves `Wanted` entry `fermat_polygonal_number_theorem`.

Source: https://en.wikipedia.org/wiki/Fermat_polygonal_number_theorem.
-/
theorem fermat_polygonal_number_theorem : ∀ (s n : ℕ), 3 ≤ s →
    ∃ (t : Finset ℕ) (k : ℕ → ℕ), t.card ≤ s ∧
      n = ∑ i ∈ t, Nat.polygonalNumber s (k i) := by
  intro s n hs
  rcases eq_or_lt_of_le hs with hs3 | hs3
  · subst s
    exact fermatPoly_three_case n
  by_cases hs4 : s = 4
  · subst s
    exact fermatPoly_four_case n
  have hs5 : 5 ≤ s := by omega
  let m := s - 2
  have hm : 3 ≤ m := by omega
  have hms : m + 2 = s := by
    dsimp [m]
    omega
  by_cases hnLarge : 120 * m ≤ n
  · simpa [hms] using fermatPolyRoute_sound hm (fermatPolyRoute_of_large hm hnLarge)
  · have hnSmall : n < 120 * m := by omega
    by_cases hm34 : m < 34
    · simpa [hms] using fermatPoly_small_of_small_m hm hm34 hnSmall
    · simpa [hms] using fermatPoly_small_of_large_m (by omega) hnSmall

end

end MetaMathlibExt
