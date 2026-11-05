/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.DirichletCharacter.Quadratic
public import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.DirichletCharacter.KroneckerJacobiOdd

@[expose] public section

section
namespace MetaMathlibExt

private theorem coprime_two_iff_odd (n : ℕ) : Nat.Coprime n 2 ↔ Odd n := by
  constructor
  · intro h
    rw [← Nat.not_even_iff_odd]
    rintro ⟨k, rfl⟩
    have h2 : 2 ∣ Nat.gcd (k + k) 2 :=
      Nat.dvd_gcd ⟨k, (two_mul k).symm⟩ dvd_rfl
    unfold Nat.Coprime at h
    rw [h] at h2
    exact absurd h2 (by decide)
  · exact Odd.coprime_two_right

private theorem coprime_four_iff_odd (n : ℕ) : Nat.Coprime n 4 ↔ Odd n := by
  have h42 : (4 : ℕ) = 2 * 2 := rfl
  rw [h42, Nat.coprime_mul_iff_right]
  constructor
  · exact fun h => Iff.mp (coprime_two_iff_odd n) h.1
  · exact fun h => ⟨Iff.mpr (coprime_two_iff_odd n) h, Iff.mpr (coprime_two_iff_odd n) h⟩

private theorem coprime_eight_iff_odd (n : ℕ) : Nat.Coprime n 8 ↔ Odd n := by
  have h82 : (8 : ℕ) = 4 * 2 := rfl
  rw [h82, Nat.coprime_mul_iff_right]
  constructor
  · exact fun h => Iff.mp (coprime_two_iff_odd n) h.2
  · exact fun h => ⟨Iff.mpr (coprime_four_iff_odd n) h, Iff.mpr (coprime_two_iff_odd n) h⟩

private theorem kroneckerSym_pow_two (D : ℤ) (hD : D ≠ -1) (e : ℕ) :
    kroneckerSym D (2 ^ e) = kroneckerAtTwo D ^ e := by
  induction e with
  | zero => simp [kroneckerSym]
  | succ e ih =>
    rw [pow_succ', pow_succ', kroneckerSym_mul D hD 2 (2 ^ e), kroneckerSym_two D, ih]

private theorem chi4_eq_zero_of_even (n : ℕ) (he : Even n) :
    ZMod.χ₄ ((n : ℕ) : ZMod 4) = 0 := by
  rw [ZMod.χ₄_nat_eq_if_mod_four]
  have h2 : n % 2 = 0 := Nat.even_iff.mp he
  simp [h2]

private theorem chi4_sq_of_odd (t : ℕ) (ht : Odd t) :
    (ZMod.χ₄ ((t : ℕ) : ZMod 4)) ^ 2 = 1 := by
  rw [ZMod.χ₄_nat_eq_if_mod_four]
  have ht2 : t % 2 = 1 := Nat.odd_iff.mp ht
  simp [ht2]

private theorem atTwo_eq_jacobi (D : ℤ) (hD4 : D % 4 = 1) :
    kroneckerAtTwo D = jacobiSym 2 D.natAbs := by
  have hNodd : Odd D.natAbs := by rw [Nat.odd_iff]; omega
  rw [jacobiSym.at_two hNodd, ZMod.χ₈_nat_eq_if_mod_eight]
  have hD2 : D % 2 = 1 := by omega
  have hN2 : D.natAbs % 2 = 1 := Nat.odd_iff.mp hNodd
  have hmod8 : (D % 8 = 1 ∨ D % 8 = 7) ↔
      (D.natAbs % 8 = 1 ∨ D.natAbs % 8 = 7) := by omega
  unfold kroneckerAtTwo
  by_cases h8 : D % 8 = 1 ∨ D % 8 = 7
  · have h8N := hmod8.mp h8
    simp [h8, h8N, hD2, hN2]
  · have h8N1 : ¬ D.natAbs % 8 = 1 := fun h => h8 (hmod8.mpr (Or.inl h))
    have h8N7 : ¬ D.natAbs % 8 = 7 := fun h => h8 (hmod8.mpr (Or.inr h))
    simp [h8, hD2, hN2, h8N1, h8N7]

private theorem jacobi_flip_of_one_mod_four (D : ℤ) (hD4 : D % 4 = 1) (t : ℕ)
    (ht : Odd t) :
    jacobiSym D t = jacobiSym (t : ℤ) D.natAbs := by
  have hNodd : Odd D.natAbs := by rw [Nat.odd_iff]; omega
  rcases le_total D 0 with hDneg | hDpos
  · have hDN : D = -((D.natAbs : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs, abs_of_nonpos hDneg, neg_neg]
    have hN4 : D.natAbs % 4 = 3 := by omega
    conv_lhs => rw [hDN]
    rw [jacobiSym.neg _ ht]
    have hrec := jacobiSym.quadratic_reciprocity hNodd ht
    have hpow : (-1 : ℤ) ^ (D.natAbs / 2 * (t / 2)) = ZMod.χ₄ ((t : ℕ) : ZMod 4) := by
      have hN2odd : Odd (D.natAbs / 2) := by rw [Nat.odd_iff]; omega
      rw [pow_mul, hN2odd.neg_one_pow, ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp ht)]
    rw [hrec, hpow, ← mul_assoc, ← sq, chi4_sq_of_odd t ht, one_mul]
  · have hDN : D = ((D.natAbs : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs, abs_of_nonneg hDpos]
    have hN4 : D.natAbs % 4 = 1 := by omega
    conv_lhs => rw [hDN]
    exact jacobiSym.quadratic_reciprocity_one_mod_four hN4 ht

private theorem caseA_identity (D : ℤ) (hD4 : D % 4 = 1) (n : ℕ) :
    kroneckerSym D n = jacobiSym (n : ℤ) D.natAbs := by
  have hDne : D ≠ -1 := by omega
  have hD0 : D ≠ 0 := by intro h; rw [h] at hD4; simp at hD4
  have hN0 : D.natAbs ≠ 0 := by omega
  by_cases hn : n = 0
  · subst hn
    rw [Nat.cast_zero]
    by_cases hN1 : D.natAbs = 1
    · have hL : kroneckerSym D 0 = 1 := by simp [kroneckerSym, hN1]
      rw [hL, hN1]
      exact (jacobiSym.one_right _).symm
    · have hL : kroneckerSym D 0 = 0 := by simp [kroneckerSym, hN1]
      rw [hL]
      exact (jacobiSym.zero_left (by omega)).symm
  · obtain ⟨e, t, ht2, hnt⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn 2 (by decide)
    have htodd : Odd t :=
      Nat.not_even_iff_odd.mp (fun hev => ht2 (even_iff_two_dvd.mp hev))
    have hcast : ((2 ^ e * t : ℕ) : ℤ) = (2 : ℤ) ^ e * (t : ℤ) := by
      push_cast
      ring
    rw [hnt, kroneckerSym_mul D hDne (2 ^ e) t,
      kroneckerSym_pow_two D hDne, kroneckerSym_eq_jacobiSym_of_odd D t htodd,
      jacobi_flip_of_one_mod_four D hD4 t htodd, atTwo_eq_jacobi D hD4,
      hcast, jacobiSym.mul_left, jacobiSym.pow_left]

private theorem jacobi_of_three_mod_four (m : ℤ) (hm4 : m % 4 = 3) (n : ℕ) (hn : Odd n) :
    jacobiSym m n = ZMod.χ₄ ((n : ℕ) : ZMod 4) * jacobiSym (n : ℤ) m.natAbs := by
  have hModd : Odd m.natAbs := by
    have hmo : Odd m := Int.odd_iff.mpr (by omega)
    exact Odd.natAbs hmo
  rcases le_total m 0 with hmneg | hmpos
  · have hmM : m = -((m.natAbs : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs, abs_of_nonpos hmneg, neg_neg]
    have hM4 : m.natAbs % 4 = 1 := by omega
    conv_lhs => rw [hmM]
    rw [jacobiSym.neg _ hn,
      jacobiSym.quadratic_reciprocity_one_mod_four hM4 hn]
  · have hmM : m = ((m.natAbs : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs, abs_of_nonneg hmpos]
    have hM4 : m.natAbs % 4 = 3 := by omega
    conv_lhs => rw [hmM]
    have hrec := jacobiSym.quadratic_reciprocity hModd hn
    have hpow : (-1 : ℤ) ^ (m.natAbs / 2 * (n / 2)) = ZMod.χ₄ ((n : ℕ) : ZMod 4) := by
      have hM2odd : Odd (m.natAbs / 2) := by rw [Nat.odd_iff]; omega
      rw [pow_mul, hM2odd.neg_one_pow, ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp hn)]
    rw [hrec, hpow]

private theorem caseB1_identity (D m : ℤ) (hDm : D = 4 * m) (hm4 : m % 4 = 3) (n : ℕ) :
    kroneckerSym D n =
      ZMod.χ₄ ((n : ℕ) : ZMod 4) * jacobiSym (n : ℤ) m.natAbs := by
  have hDne : D ≠ -1 := by omega
  have hD2 : D % 2 = 0 := by omega
  have hc0 : kroneckerAtTwo D = 0 := by simp [kroneckerAtTwo, hD2]
  have hm0 : m ≠ 0 := by intro h; rw [h] at hm4; simp at hm4
  have hM0 : m.natAbs ≠ 0 := by omega
  have h4 : (4 : ℤ).natAbs = 4 := rfl
  have hN : D.natAbs = 4 * m.natAbs := by rw [hDm, Int.natAbs_mul, h4]
  have hN1 : D.natAbs ≠ 1 := by omega
  by_cases hn0 : n = 0
  · subst hn0
    have hL : kroneckerSym D 0 = 0 := by simp [kroneckerSym, hN1]
    have hchi0 : ZMod.χ₄ (((0 : ℕ)) : ZMod 4) = 0 := by decide
    rw [hL, hchi0, zero_mul]
  · rcases Nat.even_or_odd n with heven | hodd
    · obtain ⟨e, t, ht2, hnt⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 2 (by decide)
      have htodd : Odd t :=
        Nat.not_even_iff_odd.mp (fun hev => ht2 (even_iff_two_dvd.mp hev))
      have he : e ≠ 0 := by
        intro h
        subst h
        simp only [pow_zero, one_mul] at hnt
        have hevt : Even t := hnt ▸ heven
        exact (Nat.not_even_iff_odd.mpr htodd) hevt
      have hL : kroneckerSym D n = 0 := by
        rw [hnt, kroneckerSym_mul D hDne (2 ^ e) t,
          kroneckerSym_pow_two D hDne, hc0, zero_pow he, zero_mul]
      have hR : ZMod.χ₄ ((n : ℕ) : ZMod 4) * jacobiSym (n : ℤ) m.natAbs = 0 := by
        rw [chi4_eq_zero_of_even n heven, zero_mul]
      rw [hL, hR]
    · have hJ : kroneckerSym D n = jacobiSym D n :=
        kroneckerSym_eq_jacobiSym_of_odd D n hodd
      have hD4 : jacobiSym D n = jacobiSym (4 : ℤ) n * jacobiSym m n := by
        conv_lhs => rw [hDm]
        rw [jacobiSym.mul_left]
      have hat4 : jacobiSym (4 : ℤ) n = 1 := jacobiSym.at_four hodd
      rw [hJ, hD4, hat4, one_mul, jacobi_of_three_mod_four m hm4 n hodd]

private theorem chi8_eq_zero_of_even (n : ℕ) (he : Even n) :
    ZMod.χ₈ ((n : ℕ) : ZMod 8) = 0 := by
  rw [ZMod.χ₈_nat_eq_if_mod_eight]
  have h2 : n % 2 = 0 := Nat.even_iff.mp he
  simp [h2]

private theorem chi8'_eq_zero_of_even (n : ℕ) (he : Even n) :
    ZMod.χ₈' ((n : ℕ) : ZMod 8) = 0 := by
  rw [ZMod.χ₈'_nat_eq_if_mod_eight]
  have h2 : n % 2 = 0 := Nat.even_iff.mp he
  simp [h2]

private theorem chi8_cube_of_odd (n : ℕ) (hn : Odd n) :
    (ZMod.χ₈ ((n : ℕ) : ZMod 8)) ^ 3 = ZMod.χ₈ ((n : ℕ) : ZMod 8) := by
  have hn2 : n % 2 = 1 := Nat.odd_iff.mp hn
  have hpm : ZMod.χ₈ ((n : ℕ) : ZMod 8) = 1 ∨ ZMod.χ₈ ((n : ℕ) : ZMod 8) = -1 := by
    rw [ZMod.χ₈_nat_eq_if_mod_eight]
    simp only [hn2]
    by_cases h8 : n % 8 = 1 ∨ n % 8 = 7 <;> simp [h8]
  rcases hpm with h | h <;> rw [h] <;> norm_num

private theorem jay8_eq (n : ℕ) (hn : Odd n) :
    jacobiSym (8 : ℤ) n = ZMod.χ₈ ((n : ℕ) : ZMod 8) := by
  have h8 : (8 : ℤ) = (2 : ℤ) ^ 3 := by norm_num
  rw [h8, jacobiSym.pow_left, jacobiSym.at_two hn, chi8_cube_of_odd n hn]

private theorem bridge_chi8' (n : ℕ) :
    ZMod.χ₈' ((n : ℕ) : ZMod 8)
      = ZMod.χ₄ ((n : ℕ) : ZMod 4) * ZMod.χ₈ ((n : ℕ) : ZMod 8) := by
  have h := ZMod.χ₈'_int_eq_χ₄_mul_χ₈ ((n : ℕ) : ℤ)
  simp only [Int.cast_natCast] at h
  exact h

private theorem jacobi_k_one (k : ℤ) (hk4 : k % 4 = 1) (n : ℕ) (hn : Odd n) :
    jacobiSym k n = jacobiSym (n : ℤ) k.natAbs := by
  have hKodd : Odd k.natAbs := by
    have hko : Odd k := Int.odd_iff.mpr (by omega)
    exact Odd.natAbs hko
  rcases le_total k 0 with hkneg | hkpos
  · have hkK : k = -((k.natAbs : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs, abs_of_nonpos hkneg, neg_neg]
    have hK4 : k.natAbs % 4 = 3 := by omega
    conv_lhs => rw [hkK]
    rw [jacobiSym.neg _ hn]
    have hrec := jacobiSym.quadratic_reciprocity hKodd hn
    have hpow : (-1 : ℤ) ^ (k.natAbs / 2 * (n / 2)) = ZMod.χ₄ ((n : ℕ) : ZMod 4) := by
      have hK2odd : Odd (k.natAbs / 2) := by rw [Nat.odd_iff]; omega
      rw [pow_mul, hK2odd.neg_one_pow, ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp hn)]
    rw [hrec, hpow, ← mul_assoc, ← sq, chi4_sq_of_odd n hn, one_mul]
  · have hkK : k = ((k.natAbs : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs, abs_of_nonneg hkpos]
    have hK4 : k.natAbs % 4 = 1 := by omega
    conv_lhs => rw [hkK]
    exact jacobiSym.quadratic_reciprocity_one_mod_four hK4 hn

private theorem caseB2a_identity (D k : ℤ) (hDk : D = 8 * k) (hk4 : k % 4 = 1) (n : ℕ) :
    kroneckerSym D n =
      ZMod.χ₈ ((n : ℕ) : ZMod 8) * jacobiSym (n : ℤ) k.natAbs := by
  have hDne : D ≠ -1 := by omega
  have hD2 : D % 2 = 0 := by omega
  have hc0 : kroneckerAtTwo D = 0 := by simp [kroneckerAtTwo, hD2]
  have hk0 : k ≠ 0 := by
    intro h
    rw [h] at hk4
    simp at hk4
  have hK0 : k.natAbs ≠ 0 := by omega
  have h4 : (8 : ℤ).natAbs = 8 := rfl
  have hN : D.natAbs = 8 * k.natAbs := by rw [hDk, Int.natAbs_mul, h4]
  have hN1 : D.natAbs ≠ 1 := by omega
  by_cases hn0 : n = 0
  · subst hn0
    have hL : kroneckerSym D 0 = 0 := by simp [kroneckerSym, hN1]
    have hchi0 : ZMod.χ₈ (((0 : ℕ)) : ZMod 8) = 0 := by decide
    rw [hL, hchi0, zero_mul]
  · rcases Nat.even_or_odd n with heven | hodd
    · obtain ⟨e, t, ht2, hnt⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 2 (by decide)
      have htodd : Odd t :=
        Nat.not_even_iff_odd.mp (fun hev => ht2 (even_iff_two_dvd.mp hev))
      have he : e ≠ 0 := by
        intro h
        subst h
        simp only [pow_zero, one_mul] at hnt
        have hevt : Even t := hnt ▸ heven
        exact (Nat.not_even_iff_odd.mpr htodd) hevt
      have hL : kroneckerSym D n = 0 := by
        rw [hnt, kroneckerSym_mul D hDne (2 ^ e) t,
          kroneckerSym_pow_two D hDne, hc0, zero_pow he, zero_mul]
      have hR : ZMod.χ₈ ((n : ℕ) : ZMod 8) * jacobiSym (n : ℤ) k.natAbs = 0 := by
        rw [chi8_eq_zero_of_even n heven, zero_mul]
      rw [hL, hR]
    · have hJ : kroneckerSym D n = jacobiSym D n :=
        kroneckerSym_eq_jacobiSym_of_odd D n hodd
      have hD8 : jacobiSym D n = jacobiSym (8 : ℤ) n * jacobiSym k n := by
        conv_lhs => rw [hDk]
        rw [jacobiSym.mul_left]
      rw [hJ, hD8, jay8_eq n hodd, jacobi_k_one k hk4 n hodd]

private theorem caseB2b_identity (D k : ℤ) (hDk : D = 8 * k) (hk4 : k % 4 = 3) (n : ℕ) :
    kroneckerSym D n =
      ZMod.χ₈' ((n : ℕ) : ZMod 8) * jacobiSym (n : ℤ) k.natAbs := by
  have hDne : D ≠ -1 := by omega
  have hD2 : D % 2 = 0 := by omega
  have hc0 : kroneckerAtTwo D = 0 := by simp [kroneckerAtTwo, hD2]
  have hk0 : k ≠ 0 := by
    intro h
    rw [h] at hk4
    simp at hk4
  have hK0 : k.natAbs ≠ 0 := by omega
  have h4 : (8 : ℤ).natAbs = 8 := rfl
  have hN : D.natAbs = 8 * k.natAbs := by rw [hDk, Int.natAbs_mul, h4]
  have hN1 : D.natAbs ≠ 1 := by omega
  by_cases hn0 : n = 0
  · subst hn0
    have hL : kroneckerSym D 0 = 0 := by simp [kroneckerSym, hN1]
    have hchi0 : ZMod.χ₈' (((0 : ℕ)) : ZMod 8) = 0 := by decide
    rw [hL, hchi0, zero_mul]
  · rcases Nat.even_or_odd n with heven | hodd
    · obtain ⟨e, t, ht2, hnt⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 2 (by decide)
      have htodd : Odd t :=
        Nat.not_even_iff_odd.mp (fun hev => ht2 (even_iff_two_dvd.mp hev))
      have he : e ≠ 0 := by
        intro h
        subst h
        simp only [pow_zero, one_mul] at hnt
        have hevt : Even t := hnt ▸ heven
        exact (Nat.not_even_iff_odd.mpr htodd) hevt
      have hL : kroneckerSym D n = 0 := by
        rw [hnt, kroneckerSym_mul D hDne (2 ^ e) t,
          kroneckerSym_pow_two D hDne, hc0, zero_pow he, zero_mul]
      have hR : ZMod.χ₈' ((n : ℕ) : ZMod 8) * jacobiSym (n : ℤ) k.natAbs = 0 := by
        rw [chi8'_eq_zero_of_even n heven, zero_mul]
      rw [hL, hR]
    · have hJ : kroneckerSym D n = jacobiSym D n :=
        kroneckerSym_eq_jacobiSym_of_odd D n hodd
      have hD8 : jacobiSym D n = jacobiSym (8 : ℤ) n * jacobiSym k n := by
        conv_lhs => rw [hDk]
        rw [jacobiSym.mul_left]
      rw [hJ, hD8, jay8_eq n hodd, jacobi_of_three_mod_four k hk4 n hodd,
        bridge_chi8']
      ring

private theorem chi4_zero_iff (n : ℕ) :
    ZMod.χ₄ ((n : ℕ) : ZMod 4) = 0 ↔ ¬ Nat.Coprime n 4 := by
  rw [ZMod.χ₄_nat_eq_if_mod_four]
  by_cases h2 : n % 2 = 0
  · rw [ite_eq_left h2]
    have hev : Even n := Nat.even_iff.mpr h2
    have hnc : ¬ Nat.Coprime n 4 := by
      rw [coprime_four_iff_odd n]
      exact fun ho => (Nat.not_even_iff_odd.mpr ho) hev
    exact iff_of_true rfl hnc
  · have hodd : Odd n := by rw [Nat.odd_iff]; omega
    have hcop : Nat.Coprime n 4 := Iff.mpr (coprime_four_iff_odd n) hodd
    rw [ite_eq_right h2]
    by_cases h4 : n % 4 = 1
    · rw [ite_eq_left h4]
      exact iff_of_false one_ne_zero (not_not.mpr hcop)
    · rw [ite_eq_right h4]
      exact iff_of_false (by decide) (not_not.mpr hcop)

private theorem chi8_zero_iff (n : ℕ) :
    ZMod.χ₈ ((n : ℕ) : ZMod 8) = 0 ↔ ¬ Nat.Coprime n 8 := by
  rw [ZMod.χ₈_nat_eq_if_mod_eight]
  by_cases h2 : n % 2 = 0
  · rw [ite_eq_left h2]
    have hev : Even n := Nat.even_iff.mpr h2
    have hnc : ¬ Nat.Coprime n 8 := by
      rw [coprime_eight_iff_odd n]
      exact fun ho => (Nat.not_even_iff_odd.mpr ho) hev
    exact iff_of_true rfl hnc
  · have hodd : Odd n := by rw [Nat.odd_iff]; omega
    have hcop : Nat.Coprime n 8 := Iff.mpr (coprime_eight_iff_odd n) hodd
    rw [ite_eq_right h2]
    by_cases h8 : n % 8 = 1 ∨ n % 8 = 7
    · rw [ite_eq_left h8]
      exact iff_of_false one_ne_zero (not_not.mpr hcop)
    · rw [ite_eq_right h8]
      exact iff_of_false (by decide) (not_not.mpr hcop)

private theorem chi8'_zero_iff (n : ℕ) :
    ZMod.χ₈' ((n : ℕ) : ZMod 8) = 0 ↔ ¬ Nat.Coprime n 8 := by
  rw [ZMod.χ₈'_nat_eq_if_mod_eight]
  by_cases h2 : n % 2 = 0
  · rw [ite_eq_left h2]
    have hev : Even n := Nat.even_iff.mpr h2
    have hnc : ¬ Nat.Coprime n 8 := by
      rw [coprime_eight_iff_odd n]
      exact fun ho => (Nat.not_even_iff_odd.mpr ho) hev
    exact iff_of_true rfl hnc
  · have hodd : Odd n := by rw [Nat.odd_iff]; omega
    have hcop : Nat.Coprime n 8 := Iff.mpr (coprime_eight_iff_odd n) hodd
    rw [ite_eq_right h2]
    by_cases h8 : n % 8 = 1 ∨ n % 8 = 3
    · rw [ite_eq_left h8]
      exact iff_of_false one_ne_zero (not_not.mpr hcop)
    · rw [ite_eq_right h8]
      exact iff_of_false (by decide) (not_not.mpr hcop)

private theorem per_zero_of_factored (N tw M : ℕ) (hN : N ≠ 0) (htwM : N = tw * M)
    (E F : ℕ → ℤ)
    (hF : ∀ n, F n = E n * jacobiSym (n : ℤ) M)
    (hEper : ∀ a b : ℕ, (a : ZMod tw) = (b : ZMod tw) → E a = E b)
    (hEzero : ∀ n : ℕ, E n = 0 ↔ ¬ Nat.Coprime n tw)
    (hM0 : M ≠ 0) :
    (∀ a b : ℕ, (a : ZMod N) = (b : ZMod N) → F a = F b) ∧
    (∀ a : ZMod N, ¬IsUnit a → F a.val = 0) := by
  have : NeZero N := ⟨hN⟩
  have htwDvd : tw ∣ N := ⟨M, htwM⟩
  have hMDvd : M ∣ N := ⟨tw, by rw [htwM, mul_comm]⟩
  constructor
  · intro a b hab
    have hmod : a ≡ b [MOD N] := (ZMod.natCast_eq_natCast_iff a b N).mp hab
    have hmodtw : a ≡ b [MOD tw] := Nat.ModEq.of_dvd htwDvd hmod
    have hmodM : a ≡ b [MOD M] := Nat.ModEq.of_dvd hMDvd hmod
    have hE : E a = E b := hEper a b ((ZMod.natCast_eq_natCast_iff a b tw).mpr hmodtw)
    have hJ : jacobiSym (a : ℤ) M = jacobiSym (b : ℤ) M := by
      have hmodM' : a % M = b % M := hmodM
      have hcc := congrArg (Nat.cast : ℕ → ℤ) hmodM'
      rw [Int.natCast_mod, Int.natCast_mod] at hcc
      exact jacobiSym.mod_left' hcc
    rw [hF, hF, hE, hJ]
  · intro a ha
    rw [hF]
    set v := a.val with hv
    have hNC : ¬ Nat.Coprime v N := by
      intro hc
      apply ha
      have hcast : ((v : ℕ) : ZMod N) = a := by
        rw [hv]; exact ZMod.natCast_zmod_val a
      rw [← hcast]
      exact (ZMod.isUnit_iff_coprime _ _).mpr hc
    have htwM' : Nat.Coprime v N ↔ Nat.Coprime v tw ∧ Nat.Coprime v M := by
      rw [htwM]; exact Nat.coprime_mul_iff_right
    rw [htwM'] at hNC
    by_cases htw : Nat.Coprime v tw
    · have hM : ¬ Nat.Coprime v M := fun h => hNC ⟨htw, h⟩
      have hgcd : Int.gcd ((v : ℕ) : ℤ) ((M : ℕ) : ℤ) ≠ 1 := by
        rw [Int.gcd_natCast_natCast]
        exact fun hcon => hM (Nat.coprime_iff_gcd_eq_one.mpr hcon)
      have hJ0 : jacobiSym ((v : ℕ) : ℤ) M = 0 :=
        jacobiSym.eq_zero_iff.mpr ⟨hM0, hgcd⟩
      rw [hJ0, mul_zero]
    · have hE0 : E v = 0 := (hEzero _).mpr htw
      rw [hE0, zero_mul]

private noncomputable def mkChar (N : ℕ) (hN : N ≠ 0) (F : ℕ → ℤ)
    (h1 : F 1 = 1)
    (hmul : ∀ m n : ℕ, F (m * n) = F m * F n)
    (hper : ∀ a b : ℕ, (a : ZMod N) = (b : ZMod N) → F a = F b)
    (hzero : ∀ a : ZMod N, ¬IsUnit a → F a.val = 0) :
    MulChar (ZMod N) ℤ where
  toFun a := F a.val
  map_one' := by
    have : NeZero N := ⟨hN⟩
    change F (1 : ZMod N).val = 1
    have h : F (1 : ZMod N).val = F 1 := hper _ _ (by simp)
    rw [h, h1]
  map_mul' := by
    have : NeZero N := ⟨hN⟩
    intro a b
    change F (a * b).val = F a.val * F b.val
    have hcast : ((a.val * b.val : ℕ) : ZMod N) = a * b := by
      push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    have hper' : F (a * b).val = F (a.val * b.val) :=
      hper _ _ (by rw [ZMod.natCast_zmod_val, hcast])
    rw [hper', hmul]
  map_nonunit' := by
    intro a ha
    exact hzero a ha

private theorem mkChar_apply (N : ℕ) (hN : N ≠ 0) (F : ℕ → ℤ)
    (h1 : F 1 = 1)
    (hmul : ∀ m n : ℕ, F (m * n) = F m * F n)
    (hper : ∀ a b : ℕ, (a : ZMod N) = (b : ZMod N) → F a = F b)
    (hzero : ∀ a : ZMod N, ¬IsUnit a → F a.val = 0)
    (a : ZMod N) :
    mkChar N hN F h1 hmul hper hzero a = F a.val := rfl

private theorem existsUnique_of_kroneckerProps (N : ℕ) (hN : N ≠ 0) (F : ℕ → ℤ)
    (h1 : F 1 = 1)
    (hmul : ∀ m n : ℕ, F (m * n) = F m * F n)
    (hper : ∀ a b : ℕ, (a : ZMod N) = (b : ZMod N) → F a = F b)
    (hzero : ∀ a : ZMod N, ¬IsUnit a → F a.val = 0) :
    ∃! χ : DirichletCharacter ℤ N, ∀ n : ℕ, χ (n : ZMod N) = F n := by
  have : NeZero N := ⟨hN⟩
  refine ⟨mkChar N hN F h1 hmul hper hzero, ?_, ?_⟩
  · intro n
    rw [mkChar_apply]
    exact hper _ _ (by rw [ZMod.natCast_zmod_val])
  · intro χ₂ h₂
    apply DFunLike.ext
    intro a
    have e1 : χ₂ ((a.val : ℕ) : ZMod N) = F a.val := h₂ a.val
    have e2 : mkChar N hN F h1 hmul hper hzero ((a.val : ℕ) : ZMod N)
        = F (((a.val : ℕ) : ZMod N)).val :=
      mkChar_apply N hN F h1 hmul hper hzero _
    have e3 : F (((a.val : ℕ) : ZMod N)).val = F a.val :=
      hper _ _ (by rw [ZMod.natCast_zmod_val])
    have ea : ((a.val : ℕ) : ZMod N) = a := ZMod.natCast_zmod_val a
    rw [← ea, e1, e2, e3]

private theorem caseA_final (D : ℤ) (hD4 : D % 4 = 1) :
    ∃! χ : DirichletCharacter ℤ D.natAbs,
      ∀ n : ℕ, χ (n : ZMod D.natAbs) = kroneckerSym D n := by
  have hDne : D ≠ -1 := by omega
  have hD0 : D ≠ 0 := by intro h; rw [h] at hD4; simp at hD4
  have hN0 : D.natAbs ≠ 0 := by omega
  have h1 : kroneckerSym D 1 = 1 := kroneckerSym_one D
  have hmul : ∀ m n : ℕ,
      kroneckerSym D (m * n) = kroneckerSym D m * kroneckerSym D n :=
    kroneckerSym_mul D hDne
  have hF : ∀ n : ℕ,
      kroneckerSym D n = (fun _ => (1 : ℤ)) n * jacobiSym (n : ℤ) D.natAbs := by
    intro n
    change kroneckerSym D n = 1 * _
    rw [one_mul]
    exact caseA_identity D hD4 n
  have hEper : ∀ a b : ℕ, (a : ZMod 1) = (b : ZMod 1) →
      (fun _ => (1 : ℤ)) a = (fun _ => (1 : ℤ)) b :=
    fun _ _ _ => rfl
  have hEzero : ∀ n : ℕ, (fun _ => (1 : ℤ)) n = 0 ↔ ¬ Nat.Coprime n 1 := by
    intro n
    change (1 : ℤ) = 0 ↔ _
    exact iff_of_false one_ne_zero (not_not.mpr (Nat.coprime_one_right n))
  have htwM : D.natAbs = 1 * D.natAbs := (one_mul _).symm
  obtain ⟨hper, hzero⟩ := per_zero_of_factored D.natAbs 1 D.natAbs hN0 htwM
    (fun _ => (1 : ℤ)) (kroneckerSym D) hF hEper hEzero hN0
  exact existsUnique_of_kroneckerProps D.natAbs hN0 (kroneckerSym D) h1 hmul hper hzero

private theorem caseB1_final (D m : ℤ) (hDm : D = 4 * m) (hm4 : m % 4 = 3) :
    ∃! χ : DirichletCharacter ℤ D.natAbs,
      ∀ n : ℕ, χ (n : ZMod D.natAbs) = kroneckerSym D n := by
  have hDne : D ≠ -1 := by omega
  have hm0 : m ≠ 0 := by intro h; rw [h] at hm4; simp at hm4
  have hD0 : D ≠ 0 := by rw [hDm]; exact mul_ne_zero (by decide) hm0
  have hN0 : D.natAbs ≠ 0 := by omega
  have hM0 : m.natAbs ≠ 0 := by omega
  have h4 : (4 : ℤ).natAbs = 4 := rfl
  have hN : D.natAbs = 4 * m.natAbs := by rw [hDm, Int.natAbs_mul, h4]
  have h1 : kroneckerSym D 1 = 1 := kroneckerSym_one D
  have hmul : ∀ m' n : ℕ,
      kroneckerSym D (m' * n) = kroneckerSym D m' * kroneckerSym D n :=
    kroneckerSym_mul D hDne
  have hF : ∀ n : ℕ, kroneckerSym D n =
      (fun n => ZMod.χ₄ ((n : ℕ) : ZMod 4)) n * jacobiSym (n : ℤ) m.natAbs :=
    caseB1_identity D m hDm hm4
  have hEper : ∀ a b : ℕ, (a : ZMod 4) = (b : ZMod 4) →
      (fun n => ZMod.χ₄ ((n : ℕ) : ZMod 4)) a
        = (fun n => ZMod.χ₄ ((n : ℕ) : ZMod 4)) b := by
    intro a b h
    change ZMod.χ₄ _ = ZMod.χ₄ _
    rw [h]
  have hEzero : ∀ n : ℕ, (fun n => ZMod.χ₄ ((n : ℕ) : ZMod 4)) n = 0 ↔ ¬ Nat.Coprime n 4 := by
    intro n
    change ZMod.χ₄ _ = 0 ↔ _
    exact chi4_zero_iff n
  obtain ⟨hper, hzero⟩ := per_zero_of_factored D.natAbs 4 m.natAbs hN0 hN
    (fun n => ZMod.χ₄ ((n : ℕ) : ZMod 4)) (kroneckerSym D) hF hEper hEzero hM0
  exact existsUnique_of_kroneckerProps D.natAbs hN0 (kroneckerSym D) h1 hmul hper hzero

private theorem caseB2a_final (D k : ℤ) (hDk : D = 8 * k) (hk4 : k % 4 = 1) :
    ∃! χ : DirichletCharacter ℤ D.natAbs,
      ∀ n : ℕ, χ (n : ZMod D.natAbs) = kroneckerSym D n := by
  have hDne : D ≠ -1 := by omega
  have hk0 : k ≠ 0 := by
    intro h
    rw [h] at hk4
    simp at hk4
  have hD0 : D ≠ 0 := by rw [hDk]; exact mul_ne_zero (by decide) hk0
  have hN0 : D.natAbs ≠ 0 := by omega
  have hK0 : k.natAbs ≠ 0 := by omega
  have h4 : (8 : ℤ).natAbs = 8 := rfl
  have hN : D.natAbs = 8 * k.natAbs := by rw [hDk, Int.natAbs_mul, h4]
  have h1 : kroneckerSym D 1 = 1 := kroneckerSym_one D
  have hmul : ∀ m' n : ℕ,
      kroneckerSym D (m' * n) = kroneckerSym D m' * kroneckerSym D n :=
    kroneckerSym_mul D hDne
  have hF : ∀ n : ℕ, kroneckerSym D n =
      (fun n => ZMod.χ₈ ((n : ℕ) : ZMod 8)) n * jacobiSym (n : ℤ) k.natAbs :=
    caseB2a_identity D k hDk hk4
  have hEper : ∀ a b : ℕ, (a : ZMod 8) = (b : ZMod 8) →
      (fun n => ZMod.χ₈ ((n : ℕ) : ZMod 8)) a
        = (fun n => ZMod.χ₈ ((n : ℕ) : ZMod 8)) b := by
    intro a b h
    change ZMod.χ₈ _ = ZMod.χ₈ _
    rw [h]
  have hEzero : ∀ n : ℕ, (fun n => ZMod.χ₈ ((n : ℕ) : ZMod 8)) n = 0 ↔ ¬ Nat.Coprime n 8 := by
    intro n
    change ZMod.χ₈ _ = 0 ↔ _
    exact chi8_zero_iff n
  obtain ⟨hper, hzero⟩ := per_zero_of_factored D.natAbs 8 k.natAbs hN0 hN
    (fun n => ZMod.χ₈ ((n : ℕ) : ZMod 8)) (kroneckerSym D) hF hEper hEzero hK0
  exact existsUnique_of_kroneckerProps D.natAbs hN0 (kroneckerSym D) h1 hmul hper hzero

private theorem caseB2b_final (D k : ℤ) (hDk : D = 8 * k) (hk4 : k % 4 = 3) :
    ∃! χ : DirichletCharacter ℤ D.natAbs,
      ∀ n : ℕ, χ (n : ZMod D.natAbs) = kroneckerSym D n := by
  have hDne : D ≠ -1 := by omega
  have hk0 : k ≠ 0 := by
    intro h
    rw [h] at hk4
    simp at hk4
  have hD0 : D ≠ 0 := by rw [hDk]; exact mul_ne_zero (by decide) hk0
  have hN0 : D.natAbs ≠ 0 := by omega
  have hK0 : k.natAbs ≠ 0 := by omega
  have h4 : (8 : ℤ).natAbs = 8 := rfl
  have hN : D.natAbs = 8 * k.natAbs := by rw [hDk, Int.natAbs_mul, h4]
  have h1 : kroneckerSym D 1 = 1 := kroneckerSym_one D
  have hmul : ∀ m' n : ℕ,
      kroneckerSym D (m' * n) = kroneckerSym D m' * kroneckerSym D n :=
    kroneckerSym_mul D hDne
  have hF : ∀ n : ℕ, kroneckerSym D n =
      (fun n => ZMod.χ₈' ((n : ℕ) : ZMod 8)) n * jacobiSym (n : ℤ) k.natAbs :=
    caseB2b_identity D k hDk hk4
  have hEper : ∀ a b : ℕ, (a : ZMod 8) = (b : ZMod 8) →
      (fun n => ZMod.χ₈' ((n : ℕ) : ZMod 8)) a
        = (fun n => ZMod.χ₈' ((n : ℕ) : ZMod 8)) b := by
    intro a b h
    change ZMod.χ₈' _ = ZMod.χ₈' _
    rw [h]
  have hEzero : ∀ n : ℕ, (fun n => ZMod.χ₈' ((n : ℕ) : ZMod 8)) n = 0 ↔ ¬ Nat.Coprime n 8 := by
    intro n
    change ZMod.χ₈' _ = 0 ↔ _
    exact chi8'_zero_iff n
  obtain ⟨hper, hzero⟩ := per_zero_of_factored D.natAbs 8 k.natAbs hN0 hN
    (fun n => ZMod.χ₈' ((n : ℕ) : ZMod 8)) (kroneckerSym D) hF hEper hEzero hK0
  exact existsUnique_of_kroneckerProps D.natAbs hN0 (kroneckerSym D) h1 hmul hper hzero

/-- **Quadratic Dirichlet character of a fundamental discriminant.** Let $D$ be a fundamental
discriminant. Then there is a unique integer-valued Dirichlet character $\chi$ modulo $|D|$ such
that $\chi(n \bmod |D|) = \left(\frac{D}{n}\right)$ for every natural number $n$, where
$\left(\frac{D}{n}\right)$ is the Kronecker symbol.

Source: Joshua Males, Andreas Mono, Larry Rolen, and Ian Wagner,
*Central L-values of newforms and local polynomials*,
`arXiv:2306.15519v5`, subsection "L-functions and L-values", physical line 455.
Exact source sentence: "One may also consider L-functions associated to
a Dirichlet character chi_D = (D / dot), namely ...".
Stable ID: `candidate:a:ef6cab2596e5dbf9`.
This is the existence and uniqueness of the integer-valued Dirichlet character
of level `Int.natAbs D` evaluating as the positive-denominator Kronecker symbol
`kroneckerSym D` at every natural `n`, assuming `IsFundamentalDiscriminant D`.
No primitivity or conductor claim belongs to this item.
-/
theorem quadraticDirichletCharacter (D : ℤ)
    (hD : IsFundamentalDiscriminant D) :
    ∃! χ : DirichletCharacter ℤ D.natAbs,
      ∀ n : ℕ, χ (n : ZMod D.natAbs) = kroneckerSym D n := by
  rcases hD with ⟨_, h4⟩ | ⟨m, hDm, _, hm4⟩
  · exact caseA_final D h4
  · rcases hm4 with hm2 | hm3
    · have h2m : 2 ∣ m := by omega
      obtain ⟨k, rfl⟩ := h2m
      have hkodd : Odd k := Int.odd_iff.mpr (by omega)
      have hk43 : k % 4 = 1 ∨ k % 4 = 3 := by
        have h2 : k % 2 = 1 := Int.odd_iff.mp hkodd
        omega
      have hDk : D = 8 * k := by omega
      rcases hk43 with hk1 | hk3
      · exact caseB2a_final D k hDk hk1
      · exact caseB2b_final D k hDk hk3
    · exact caseB1_final D m hDm hm3

end MetaMathlibExt

end
