/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Algebra.Group.Even
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

/-!
# Squares with two blocks of repeated decimal digits

This module classifies squares whose decimal digits form two nonempty constant blocks.

Reference: Omar Kihel and Florian Luca, "Perfect Powers With All Equal Digits But One",
Journal of Integer Sequences 8 (2005), Article 05.5.7, Theorem 3,
https://cs.uwaterloo.ca/journals/JIS/VOL8/Kihel/kihel7.tex.
-/

namespace MetaMathlibExt

private theorem pell_induction {D c a b : ℤ} {B : ℕ} {P : ℤ → ℤ → Prop}
    (hD : 0 < D) (ha : 1 < a) (hb : 0 ≤ b) (hu : a ^ 2 - D * b ^ 2 = 1)
    (h₁ : 0 ≤ D * B ^ 2 + a ^ 2 * c) (h₂ : 0 ≤ (B : ℤ) ^ 2 - b ^ 2 * c)
    (h₃ : 0 < 2 * (a - 1) * B ^ 2 + b ^ 2 * c)
    (base : ∀ j : Fin B, let y : ℤ := j.val
      let x := Int.sqrt (D * y ^ 2 + c)
      x ^ 2 - D * y ^ 2 = c → P x y)
    (step : ∀ x y, P x y → P (a * x + D * b * y) (b * x + a * y))
    (x y : ℤ) (hx : 0 ≤ x) (hy : 0 ≤ y) (he : x ^ 2 - D * y ^ 2 = c) : P x y := by
  by_cases h : y < B
  · have hbase := base ⟨y.toNat, by omega⟩
    have hsq : D * y ^ 2 + c = x * x := by linarith [sq x]
    simp only [Int.toNat_of_nonneg hy, hsq, Int.sqrt_eq, Int.natCast_natAbs,
      abs_of_nonneg hx] at hbase
    exact hbase he
  have hB : (B : ℤ) ^ 2 ≤ y ^ 2 := by gcongr; omega
  have hx' : D * b * y ≤ a * x := by
    apply le_of_sq_le_sq _ (mul_nonneg (by omega) hx)
    have hid : (a * x) ^ 2 - (D * b * y) ^ 2 = D * y ^ 2 + a ^ 2 * c := by
      linear_combination a ^ 2 * he + D * y ^ 2 * hu
    linarith [mul_le_mul_of_nonneg_left hB hD.le]
  have hy' : b * x ≤ a * y := by
    apply le_of_sq_le_sq _ (mul_nonneg (by omega) hy)
    have hid : (a * y) ^ 2 - (b * x) ^ 2 = y ^ 2 - b ^ 2 * c := by
      linear_combination y ^ 2 * hu - b ^ 2 * he
    linarith
  have hlt : (a - 1) * y < b * x := by
    apply lt_of_not_ge
    intro hge
    have hs := pow_le_pow_left₀ (mul_nonneg hb hx) hge 2
    have hid : (b * x) ^ 2 - ((a - 1) * y) ^ 2 = 2 * (a - 1) * y ^ 2 + b ^ 2 * c := by
      linear_combination b ^ 2 * he - y ^ 2 * hu
    linarith [mul_le_mul_of_nonneg_left hB (by omega : 0 ≤ 2 * (a - 1))]
  let u := a * x - D * b * y
  let v := a * y - b * x
  have hv : 0 ≤ v := sub_nonneg.mpr hy'
  have hvlt : v < y := by dsimp [v]; linarith
  have he' : u ^ 2 - D * v ^ 2 = c := by
    calc
      _ = (a ^ 2 - D * b ^ 2) * (x ^ 2 - D * y ^ 2) := by dsimp [u, v]; ring
      _ = c := by rw [hu, he, one_mul]
  have ih := pell_induction hD ha hb hu h₁ h₂ h₃ base step u v (sub_nonneg.mpr hx') hv he'
  have ex : a * u + D * b * v = x := by dsimp [u, v]; linear_combination x * hu
  have ey : b * u + a * v = y := by dsimp [u, v]; linear_combination y * hu
  simpa only [ex, ey] using step u v ih
termination_by y.toNat
decreasing_by omega

private structure PellCase where
  D : ℤ
  c : ℤ
  a : ℤ
  b : ℤ
  bound : ℕ
  modulus : ℤ
  seeds : List (ℤ × ℤ)
  period : ℕ
  scale : ℤ
  powerPeriod : ℕ

private def PellCase.next (s : PellCase) (p : ℤ × ℤ) : ℤ × ℤ :=
  ((s.a * p.1 + s.D * s.b * p.2) % s.modulus, (s.b * p.1 + s.a * p.2) % s.modulus)

private def PellCase.residues (s : PellCase) : List (ℤ × ℤ) :=
  s.seeds.flatMap fun (x, y) ↦ List.iterate s.next (x % s.modulus, y % s.modulus) s.period

private def PellCase.powers (s : PellCase) : List ℤ :=
  List.iterate (fun z ↦ z * 10 % s.modulus) (s.scale * 10 ^ 4 % s.modulus) s.powerPeriod

private abbrev PellCase.Valid (s : PellCase) : Prop :=
  3 ∣ s.modulus ∧ 0 < s.D ∧ 1 < s.a ∧ 0 ≤ s.b ∧ s.a ^ 2 - s.D * s.b ^ 2 = 1 ∧
  0 ≤ s.D * s.bound ^ 2 + s.a ^ 2 * s.c ∧ 0 ≤ (s.bound : ℤ) ^ 2 - s.b ^ 2 * s.c ∧
  0 < 2 * (s.a - 1) * s.bound ^ 2 + s.b ^ 2 * s.c ∧
  (∀ j : Fin s.bound, let y : ℤ := j.val
    let x := Int.sqrt (s.D * y ^ 2 + s.c)
    x ^ 2 - s.D * y ^ 2 = s.c → (x % s.modulus, y % s.modulus) ∈ s.residues) ∧
  (∀ p ∈ s.residues, s.next p ∈ s.residues) ∧
  s.scale * 10 ^ 4 % s.modulus ∈ s.powers ∧
  (∀ z ∈ s.powers, z * 10 % s.modulus ∈ s.powers) ∧
  ∀ p ∈ s.residues, p.1 % 3 = 0 → p.2 ∉ s.powers

private theorem PellCase.exclude (s : PellCase) (hs : s.Valid) {x y : ℤ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (he : x ^ 2 - s.D * y ^ 2 = s.c) (hx₃ : x % 3 = 0)
    {r : ℕ} (hr : 4 ≤ r) :
    y % s.modulus ≠ s.scale * 10 ^ r % s.modulus := by
  obtain ⟨hm, hD, ha, hb, hu, h₁, h₂, h₃, base, step, start, next, disj⟩ := hs
  have hxy : (x % s.modulus, y % s.modulus) ∈ s.residues := by
    apply pell_induction hD ha hb hu h₁ h₂ h₃ base _ x y hx hy he
    intro u v huv
    have h := step _ huv
    have hu' := Int.mod_modEq u s.modulus
    have hv' := Int.mod_modEq v s.modulus
    have ex := (hu'.mul_left s.a).add (hv'.mul_left (s.D * s.b))
    have ey := (hu'.mul_left s.b).add (hv'.mul_left s.a)
    simpa only [PellCase.next, ex.eq, ey.eq] using h
  intro h
  apply disj _ hxy
  · simpa only [Int.emod_emod_of_dvd _ hm] using hx₃
  rw [h]
  clear h
  induction r, hr using Nat.le_induction with
  | base => exact start
  | succ n hn ih =>
    rw [pow_succ, ← mul_assoc]
    exact ((Int.mod_modEq _ _).mul_right 10).eq ▸ next _ ih


private def twoFourOdd : PellCase :=
  ⟨5, 16, 9, 4, 16, 96, [(4, 0), (6, 2), (14, 6)], 4, 2, 1⟩

private def twoFiveEven : PellCase :=
  ⟨2, 25, 3, 2, 10, 24, [(5, 0)], 4, 1, 1⟩

private def twoFiveOdd : PellCase :=
  ⟨5, 25, 9, 4, 20, 24, [(5, 0)], 4, 2, 1⟩

private def fourOneOdd : PellCase :=
  ⟨10, -31, 19, 6, 34, 168, [(3, 2), (63, 20)], 8, 2, 6⟩

private def fourNineOdd : PellCase :=
  ⟨10, 41, 19, 6, 39, 888, [(9, 2), (51, 16)], 12, 2, 3⟩

private def fiveSixEven : PellCase :=
  ⟨5, 4, 9, 4, 8, 48, [(2, 0), (3, 1), (7, 3)], 4, 1, 1⟩

private def eightOneEven : PellCase :=
  ⟨2, -71, 3, 2, 18, 24, [(1, 6), (21, 16)], 4, 2, 1⟩

private def eightOneOdd : PellCase :=
  ⟨5, -71, 9, 4, 34, 24, [(3, 4), (53, 24)], 4, 4, 1⟩

private def eightNineEven : PellCase :=
  ⟨2, 1, 3, 2, 2, 24, [(1, 0)], 4, 2, 1⟩

private def eightNineOdd : PellCase :=
  ⟨5, 1, 9, 4, 4, 24, [(1, 0)], 4, 4, 1⟩

private def twoFourEvenTwo : PellCase :=
  ⟨2, 196, 3, 2, 28, 264, [(14, 0), (18, 8), (22, 12)], 12, 1, 2⟩

private def threeFourEvenThree : PellCase :=
  ⟨3, 996, 2, 1, 32, 1776, [(36, 10), (42, 16)], 36, 1, 3⟩

private def threeFourOddThree : PellCase :=
  ⟨30, 996, 11, 2, 64, 33, [(54, 8), (114, 20)], 4, 1, 2⟩

private theorem pell_cases_valid :
    twoFourOdd.Valid ∧ twoFiveEven.Valid ∧ twoFiveOdd.Valid ∧ fourOneOdd.Valid ∧
    fourNineOdd.Valid ∧ fiveSixEven.Valid ∧ eightOneEven.Valid ∧ eightOneOdd.Valid ∧
    eightNineEven.Valid ∧ eightNineOdd.Valid ∧ twoFourEvenTwo.Valid ∧
    threeFourEvenThree.Valid ∧ threeFourOddThree.Valid := by
  repeat' apply And.intro
  all_goals decide +kernel

private theorem repdigit_identity (a r : ℕ) :
    9 * Nat.ofDigits 10 (List.replicate r a) + a = a * 10 ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [List.replicate_succ, Nat.ofDigits_cons, pow_succ]
    linarith only [ih]

private theorem block_identity (n a b r s : ℕ)
    (h : Nat.digits 10 n = List.replicate s b ++ List.replicate r a) :
    9 * n + a * 10 ^ s + b = a * 10 ^ (r + s) + b * 10 ^ s := by
  have hn := Nat.ofDigits_digits 10 n
  rw [h, Nat.ofDigits_append, List.length_replicate] at hn
  have ha := repdigit_identity a r
  have hb := repdigit_identity b s
  rw [pow_add]
  have ha' := congrArg (fun z : ℕ => z * 10 ^ s) ha
  nlinarith only [hn, ha', hb]

private theorem ten_dvd_root (x : ℕ) (h : 10 ∣ x * x) : 10 ∣ x := by
  have hx : (x % 10) ^ 2 % 10 = 0 := by
    simpa only [pow_two, Nat.mul_mod, Nat.mod_mod] using Nat.mod_eq_zero_of_dvd h
  have check : ∀ z : Fin 10, z.val ^ 2 % 10 = 0 → z.val = 0 := by decide
  exact Nat.dvd_of_mod_eq_zero (check ⟨x % 10, by omega⟩ hx)

private theorem square_cancel_hundred (v : ℕ) (h : IsSquare (100 * v)) : IsSquare v := by
  obtain ⟨x, hx⟩ := h
  have hd : 10 ∣ x := ten_dvd_root x (by rw [← hx]; exact ⟨10 * v, by ring⟩)
  obtain ⟨y, rfl⟩ := hd
  exact ⟨y, by nlinarith only [hx]⟩

private theorem square_ten_pow (v s : ℕ) (hv : v % 10 ≠ 0)
    (hs : IsSquare (10 ^ s * v)) : ∃ i, s = 2 * i ∧ IsSquare v := by
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    rcases s with _ | _ | s
    · exact ⟨0, rfl, by simpa using hs⟩
    · obtain ⟨x, hx⟩ := hs
      have hd : 10 ∣ x := ten_dvd_root x (by rw [← hx]; simp)
      obtain ⟨y, rfl⟩ := hd
      have : v = 10 * (y * y) := by norm_num at hx; nlinarith only [hx]
      exact (hv (by rw [this]; simp)).elim
    · have hsq : IsSquare (100 * (10 ^ s * v)) := by
        convert hs using 1
        simp [pow_add]
        ring
      obtain ⟨i, hi, hv⟩ := ih s (by omega) (square_cancel_hundred _ hsq)
      exact ⟨i + 1, by omega, hv⟩

private theorem repdigit_square (a r : ℕ) (ha : 1 ≤ a) (ha₉ : a ≤ 9) (hr : 1 ≤ r)
    (hs : IsSquare (Nat.ofDigits 10 (List.replicate r a))) :
    r = 1 ∧ (a = 1 ∨ a = 4 ∨ a = 9) := by
  obtain ⟨x, hx⟩ := hs
  have he := repdigit_identity a r
  rw [hx] at he
  by_cases hr₁ : r = 1
  · subst r
    simp only [List.replicate_one, Nat.ofDigits_singleton] at hx
    have hx₃ : x ≤ 3 := by nlinarith
    interval_cases x <;> omega
  have hr₂ : 2 ≤ r := by omega
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hr₂
  have h100 : a * 10 ^ r % 100 = 0 := by rw [ht, pow_add]; simp [Nat.mul_mod]
  have hmod : (9 * (x % 100) ^ 2 + a) % 100 = 0 := by
    rw [← he] at h100
    simpa only [pow_two, Nat.add_mod, Nat.mul_mod, Nat.mod_mod] using h100
  have check : ∀ a : Fin 10, ∀ x : Fin 100, 0 < a.val →
      (9 * x.val ^ 2 + a.val) % 100 = 0 → a.val = 4 := by decide +kernel
  have ha₄ : a = 4 := check ⟨a, by omega⟩ ⟨x % 100, by omega⟩ ha hmod
  subst a
  have h16 : 4 * 10 ^ r % 16 = 0 := by
    rw [ht, pow_add, ← mul_assoc]
    simp [Nat.mul_mod]
  have hmod16 : (9 * (x % 16) ^ 2 + 4) % 16 = 0 := by
    rw [← he] at h16
    simpa only [pow_two, Nat.add_mod, Nat.mul_mod, Nat.mod_mod] using h16
  have check16 : ∀ x : Fin 16, (9 * x.val ^ 2 + 4) % 16 ≠ 0 := by decide
  exact (check16 ⟨x % 16, by omega⟩ hmod16).elim

private theorem zero_block (n a r s : ℕ) (ha : 1 ≤ a) (ha₉ : a ≤ 9) (hr : 1 ≤ r)
    (hn : IsSquare n)
    (h : Nat.digits 10 n = List.replicate s 0 ++ List.replicate r a) :
    (∃ i, n = 10 ^ (2 * i)) ∨ (∃ i, n = 4 * 10 ^ (2 * i)) ∨
      (∃ i, n = 9 * 10 ^ (2 * i)) := by
  have hnval := Nat.ofDigits_digits 10 n
  rw [h, Nat.ofDigits_append, Nat.ofDigits_replicate_zero, List.length_replicate,
    zero_add] at hnval
  have hv : Nat.ofDigits 10 (List.replicate r a) % 10 ≠ 0 := by
    have hr' : r = (r - 1) + 1 := by omega
    rw [hr', List.replicate_succ, Nat.ofDigits_cons]
    simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt (by omega : a < 10)] using
      (by omega : a ≠ 0)
  obtain ⟨i, hi, hs⟩ := square_ten_pow _ s hv (by simpa only [hnval] using hn)
  obtain ⟨rfl, ha | ha | ha⟩ := repdigit_square a r ha ha₉ hr hs
  · subst a
    exact Or.inl ⟨i, by simpa [hi] using hnval.symm⟩
  · subst a
    exact Or.inr (Or.inl ⟨i, by simpa [hi, mul_comm] using hnval.symm⟩)
  · subst a
    exact Or.inr (Or.inr ⟨i, by simpa [hi, mul_comm] using hnval.symm⟩)

private def squareResidues (m : ℕ) : List ℤ :=
  (List.range m).map fun x : ℕ => (x : ℤ) ^ 2 % m

private theorem square_mod_mem (x : ℤ) (m : ℕ) (hm : 0 < m) :
    x ^ 2 % m ∈ squareResidues m := by
  have hm' : 0 < (m : ℤ) := by exact_mod_cast hm
  have hnonneg := Int.emod_nonneg x (by omega : (m : ℤ) ≠ 0)
  have hlt := Int.emod_lt_of_pos x hm'
  apply List.mem_map.mpr
  refine ⟨(x % m).toNat, List.mem_range.mpr (by omega), ?_⟩
  rw [Int.toNat_of_nonneg (by omega)]
  exact ((Int.mod_modEq x m).pow 2).eq

private theorem ten_pow_mod (m : ℤ) (t k : ℕ) (h : (10 : ℤ) ^ t ≡ 0 [ZMOD m])
    (hk : t ≤ k) : (10 : ℤ) ^ k ≡ 0 [ZMOD m] := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [pow_add]
  simpa using h.mul_right ((10 : ℤ) ^ j)

private theorem trailing_bound (a b s k p : ℕ) (hb : 1 ≤ b) (hb₉ : b ≤ 9) (hsk : s ≤ k)
    (he : (3 * (p : ℤ)) ^ 2 = a * 10 ^ k + ((b : ℤ) - a) * 10 ^ s - b) : s ≤ 3 := by
  by_contra! hs
  have hs100 := ten_pow_mod 100 4 s (by decide) (by omega)
  have hk100 := ten_pow_mod 100 4 k (by decide) (by omega)
  have h100 : (3 * (p : ℤ)) ^ 2 ≡ -(b : ℤ) [ZMOD 100] := by
    rw [he]
    simpa using ((hk100.mul_left (a : ℤ)).add
      (hs100.mul_left ((b : ℤ) - a))).sub_right (b : ℤ)
  have hm100 := square_mod_mem (3 * (p : ℤ)) 100 (by decide)
  norm_num only at hm100
  rw [h100.eq] at hm100
  have check : ∀ b : Fin 10, 0 < b.val →
      -(b.val : ℤ) % 100 ∈ squareResidues 100 → b.val = 4 := by decide +kernel
  have hb₄ : b = 4 := check ⟨b, by omega⟩ hb hm100
  subst b
  have hs16 := ten_pow_mod 16 4 s (by decide) (by omega)
  have hk16 := ten_pow_mod 16 4 k (by decide) (by omega)
  have h16 : (3 * (p : ℤ)) ^ 2 ≡ -4 [ZMOD 16] := by
    rw [he]
    simpa using ((hk16.mul_left (a : ℤ)).add
      (hs16.mul_left (4 - (a : ℤ)))).sub_right 4
  have hm16 := square_mod_mem (3 * (p : ℤ)) 16 (by decide)
  norm_num only at hm16
  rw [h16.eq] at hm16
  exact (by decide : ¬((-4 : ℤ) % 16 ∈ squareResidues 16)) hm16

private def digitCases : List (ℕ × ℕ × ℕ × ℕ) :=
  [(2, 4, 1, 1), (2, 5, 1, 0), (2, 5, 1, 1), (4, 1, 1, 1),
   (4, 9, 1, 0), (4, 9, 1, 1), (5, 6, 1, 0), (8, 1, 1, 0),
   (8, 1, 1, 1), (8, 9, 1, 0), (8, 9, 1, 1), (2, 4, 2, 0),
   (3, 4, 3, 0), (3, 4, 3, 1)]

private theorem digit_cases_check : ∀ a b : Fin 10, ∀ s : Fin 4, ∀ e : Fin 2,
    let c : ℤ := ((b.val : ℤ) - a.val) * 10 ^ s.val - b.val
    0 < a.val → 0 < b.val → 0 < s.val →
    c % 128 ∈ squareResidues 128 → c % 25 ∈ squareResidues 25 →
    ((a.val : ℤ) * 10 ^ e.val + c) % 11 ∈ squareResidues 11 →
    (a.val ≠ 7 ∨ c % 7 ∈ squareResidues 7) →
    (a.val, b.val, s.val, e.val) ∈ digitCases := by
  decide +kernel

private theorem digit_candidates (a b s k p t e : ℕ) (ha : 1 ≤ a) (ha₉ : a ≤ 9)
    (hb : 1 ≤ b) (hb₉ : b ≤ 9) (hs : 1 ≤ s) (hs₃ : s ≤ 3) (hk : 8 ≤ k)
    (he₂ : e < 2) (hkt : k = 2 * t + e)
    (he : (3 * (p : ℤ)) ^ 2 = a * 10 ^ k + ((b : ℤ) - a) * 10 ^ s - b) :
    (a, b, s, e) ∈ digitCases := by
  let c : ℤ := ((b : ℤ) - a) * 10 ^ s - b
  have he' : (3 * (p : ℤ)) ^ 2 = a * 10 ^ k + c := by dsimp [c]; linarith only [he]
  have h128 : (3 * (p : ℤ)) ^ 2 ≡ c [ZMOD 128] := by
    rw [he']
    simpa using ((ten_pow_mod 128 8 k (by decide) hk).mul_left (a : ℤ)).add_right c
  have hm128 := square_mod_mem (3 * (p : ℤ)) 128 (by decide)
  norm_num only at hm128
  rw [h128.eq] at hm128
  have h25 : (3 * (p : ℤ)) ^ 2 ≡ c [ZMOD 25] := by
    rw [he']
    simpa using ((ten_pow_mod 25 8 k (by decide) hk).mul_left (a : ℤ)).add_right c
  have hm25 := square_mod_mem (3 * (p : ℤ)) 25 (by decide)
  norm_num only at hm25
  rw [h25.eq] at hm25
  have hp11 : (10 : ℤ) ^ k ≡ 10 ^ e [ZMOD 11] := by
    rw [hkt, pow_add, pow_mul]
    simpa using ((by decide : (10 : ℤ) ^ 2 ≡ 1 [ZMOD 11]).pow t).mul_right ((10 : ℤ) ^ e)
  have h11 : (3 * (p : ℤ)) ^ 2 ≡ a * 10 ^ e + c [ZMOD 11] := by
    rw [he']
    exact (hp11.mul_left (a : ℤ)).add_right c
  have hm11 := square_mod_mem (3 * (p : ℤ)) 11 (by decide)
  norm_num only at hm11
  rw [h11.eq] at hm11
  have h7 : a ≠ 7 ∨ c % 7 ∈ squareResidues 7 := by
    by_cases ha7 : a = 7
    · right
      have h7 : (3 * (p : ℤ)) ^ 2 ≡ c [ZMOD 7] := by
        rw [he', ha7]
        simp [Int.ModEq, Int.add_emod]
      have hm7 := square_mod_mem (3 * (p : ℤ)) 7 (by decide)
      norm_num only at hm7
      simpa only [h7.eq] using hm7
    · exact Or.inl ha7
  exact digit_cases_check ⟨a, by omega⟩ ⟨b, by omega⟩ ⟨s, by omega⟩ ⟨e, he₂⟩
    ha hb hs hm128 hm25 hm11 h7

private theorem nonzero_length_bound (a b s k p : ℕ) (ha : 1 ≤ a) (ha₉ : a ≤ 9)
    (hb : 1 ≤ b) (hb₉ : b ≤ 9) (hs : 1 ≤ s) (hsk : s ≤ k)
    (he : (3 * (p : ℤ)) ^ 2 = a * 10 ^ k + ((b : ℤ) - a) * 10 ^ s - b) : k < 8 := by
  by_contra! hk
  have hs₃ := trailing_bound a b s k p hb hb₉ hsk he
  obtain ⟨t, e, he₂, hkt⟩ : ∃ t e : ℕ, e < 2 ∧ k = 2 * t + e :=
    ⟨k / 2, k % 2, by omega, by omega⟩
  have ht : 4 ≤ t := by omega
  have hc := digit_candidates a b s k p t e ha ha₉ hb hb₉ hs hs₃ hk he₂ hkt he
  have hcases : (a = 2 ∧ b = 4 ∧ s = 1 ∧ e = 1) ∨
      (a = 2 ∧ b = 5 ∧ s = 1 ∧ e = 0) ∨
      (a = 2 ∧ b = 5 ∧ s = 1 ∧ e = 1) ∨
      (a = 4 ∧ b = 1 ∧ s = 1 ∧ e = 1) ∨
      (a = 4 ∧ b = 9 ∧ s = 1 ∧ e = 0) ∨
      (a = 4 ∧ b = 9 ∧ s = 1 ∧ e = 1) ∨
      (a = 5 ∧ b = 6 ∧ s = 1 ∧ e = 0) ∨
      (a = 8 ∧ b = 1 ∧ s = 1 ∧ e = 0) ∨
      (a = 8 ∧ b = 1 ∧ s = 1 ∧ e = 1) ∨
      (a = 8 ∧ b = 9 ∧ s = 1 ∧ e = 0) ∨
      (a = 8 ∧ b = 9 ∧ s = 1 ∧ e = 1) ∨
      (a = 2 ∧ b = 4 ∧ s = 2 ∧ e = 0) ∨
      (a = 3 ∧ b = 4 ∧ s = 3 ∧ e = 0) ∨
      (a = 3 ∧ b = 4 ∧ s = 3 ∧ e = 1) := by
    simpa [digitCases] using hc
  obtain ⟨h_twoFourOdd, h_twoFiveEven, h_twoFiveOdd, h_fourOneOdd, h_fourNineOdd, h_fiveSixEven,
    h_eightOneEven, h_eightOneOdd, h_eightNineEven, h_eightNineOdd, h_twoFourEvenTwo,
    h_threeFourEvenThree, h_threeFourOddThree⟩ := pell_cases_valid
  rw [hkt, pow_add, pow_mul'] at he
  rcases hcases with ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩
  · norm_num at he
    apply twoFourOdd.exclude h_twoFourOdd (x := 3 * p) (y := 2 * 10 ^ t)
      (by positivity) (by positivity) ?_ (by simp) ht rfl
    change (3 * (p : ℤ)) ^ 2 - 5 * (2 * 10 ^ t) ^ 2 = 16
    nlinarith only [he]
  · norm_num at he
    apply twoFiveEven.exclude h_twoFiveEven (x := 3 * p) (y := 1 * 10 ^ t)
      (by positivity) (by positivity) ?_ (by simp) ht rfl
    change (3 * (p : ℤ)) ^ 2 - 2 * (1 * 10 ^ t) ^ 2 = 25
    nlinarith only [he]
  · norm_num at he
    apply twoFiveOdd.exclude h_twoFiveOdd (x := 3 * p) (y := 2 * 10 ^ t)
      (by positivity) (by positivity) ?_ (by simp) ht rfl
    change (3 * (p : ℤ)) ^ 2 - 5 * (2 * 10 ^ t) ^ 2 = 25
    nlinarith only [he]
  · norm_num at he
    apply fourOneOdd.exclude h_fourOneOdd (x := 3 * p) (y := 2 * 10 ^ t)
      (by positivity) (by positivity) ?_ (by simp) ht rfl
    change (3 * (p : ℤ)) ^ 2 - 10 * (2 * 10 ^ t) ^ 2 = -31
    nlinarith only [he]
  · norm_num at he
    have hten : (10000 : ℤ) ≤ 10 ^ t := by
      simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 10) ht)
    have hxy : 2 * (10 : ℤ) ^ t + 1 ≤ 3 * p := by
      have : 2 * (10 : ℤ) ^ t < 3 * p := by nlinarith only [he, hten]
      omega
    have hprod := mul_nonneg (by omega : 0 ≤ 3 * (p : ℤ) - 2 * 10 ^ t - 1)
      (by positivity : 0 ≤ 3 * (p : ℤ) + 2 * 10 ^ t + 1)
    nlinarith only [he, hten, hprod]
  · norm_num at he
    apply fourNineOdd.exclude h_fourNineOdd (x := 3 * p) (y := 2 * 10 ^ t)
      (by positivity) (by positivity) ?_ (by simp) ht rfl
    change (3 * (p : ℤ)) ^ 2 - 10 * (2 * 10 ^ t) ^ 2 = 41
    nlinarith only [he]
  · norm_num at he
    apply fiveSixEven.exclude h_fiveSixEven (x := 3 * p) (y := 1 * 10 ^ t)
      (by positivity) (by positivity) ?_ (by simp) ht rfl
    change (3 * (p : ℤ)) ^ 2 - 5 * (1 * 10 ^ t) ^ 2 = 4
    nlinarith only [he]
  · norm_num at he
    apply eightOneEven.exclude h_eightOneEven (x := 3 * p) (y := 2 * 10 ^ t)
      (by positivity) (by positivity) ?_ (by simp) ht rfl
    change (3 * (p : ℤ)) ^ 2 - 2 * (2 * 10 ^ t) ^ 2 = -71
    nlinarith only [he]
  · norm_num at he
    apply eightOneOdd.exclude h_eightOneOdd (x := 3 * p) (y := 4 * 10 ^ t)
      (by positivity) (by positivity) ?_ (by simp) ht rfl
    change (3 * (p : ℤ)) ^ 2 - 5 * (4 * 10 ^ t) ^ 2 = -71
    nlinarith only [he]
  · norm_num at he
    apply eightNineEven.exclude h_eightNineEven (x := 3 * p) (y := 2 * 10 ^ t)
      (by positivity) (by positivity) ?_ (by simp) ht rfl
    change (3 * (p : ℤ)) ^ 2 - 2 * (2 * 10 ^ t) ^ 2 = 1
    nlinarith only [he]
  · norm_num at he
    apply eightNineOdd.exclude h_eightNineOdd (x := 3 * p) (y := 4 * 10 ^ t)
      (by positivity) (by positivity) ?_ (by simp) ht rfl
    change (3 * (p : ℤ)) ^ 2 - 5 * (4 * 10 ^ t) ^ 2 = 1
    nlinarith only [he]
  · norm_num at he
    apply twoFourEvenTwo.exclude h_twoFourEvenTwo (x := 3 * p) (y := 1 * 10 ^ t)
      (by positivity) (by positivity) ?_ (by simp) ht rfl
    change (3 * (p : ℤ)) ^ 2 - 2 * (1 * 10 ^ t) ^ 2 = 196
    nlinarith only [he]
  · norm_num at he
    apply threeFourEvenThree.exclude h_threeFourEvenThree (x := 3 * p) (y := 1 * 10 ^ t)
      (by positivity) (by positivity) ?_ (by simp) ht rfl
    change (3 * (p : ℤ)) ^ 2 - 3 * (1 * 10 ^ t) ^ 2 = 996
    nlinarith only [he]
  · norm_num at he
    apply threeFourOddThree.exclude h_threeFourOddThree (x := 3 * p) (y := 1 * 10 ^ t)
      (by positivity) (by positivity) ?_ (by simp) ht rfl
    change (3 * (p : ℤ)) ^ 2 - 30 * (1 * 10 ^ t) ^ 2 = 996
    nlinarith only [he]

private theorem short_cases : ∀ a b : Fin 10, ∀ r s : Fin 8,
    0 < a.val → 0 < b.val → 0 < r.val → 0 < s.val → r.val + s.val < 8 →
    let n := (a.val * 10 ^ (r.val + s.val) + b.val * 10 ^ s.val - a.val * 10 ^ s.val -
      b.val) / 9
    n.sqrt ^ 2 = n →
    n = 16 ∨ n = 25 ∨ n = 36 ∨ n = 49 ∨ n = 64 ∨ n = 81 ∨ n = 144 ∨
    n = 225 ∨ n = 441 ∨ n = 1444 ∨ n = 7744 := by
  decide +kernel

/--
**Squares with two blocks of repeated digits.** Let $n$ be a perfect square whose decimal
representation, read from the most significant digit, consists of $r \ge 1$ copies of a digit
$a$ with $1 \le a \le 9$ followed by $s \ge 1$ copies of a digit $b$ with $0 \le b \le 9$. Then
$n$ is one of $16$, $25$, $36$, $49$, $64$, $81$, $144$, $225$, $441$, $1444$ and $7744$, or
there is a natural number $i$ such that $n = 10^{2i}$, $n = 4 \cdot 10^{2i}$ or
$n = 9 \cdot 10^{2i}$.

Source: Omar Kihel and Florian Luca, "Perfect Powers With All Equal Digits
But One," Journal of Integer Sequences 8 (2005), Article 05.5.7, Theorem
(label thm:3), lines 273–279,
https://cs.uwaterloo.ca/journals/JIS/VOL8/Kihel/kihel7.tex
-/
public theorem squares_aaabb_classification
    (n : ℕ) (hn : IsSquare n)
    (h : ∃ a b r s : ℕ, 1 ≤ a ∧ a ≤ 9 ∧ b ≤ 9 ∧ 1 ≤ r ∧ 1 ≤ s ∧
      Nat.digits 10 n = List.replicate s b ++ List.replicate r a) :
    n = 16 ∨ n = 25 ∨ n = 36 ∨ n = 49 ∨ n = 64 ∨ n = 81 ∨ n = 144 ∨
    n = 225 ∨ n = 441 ∨ n = 1444 ∨ n = 7744 ∨
    (∃ i, n = 10 ^ (2 * i)) ∨ (∃ i, n = 4 * 10 ^ (2 * i)) ∨
    (∃ i, n = 9 * 10 ^ (2 * i))
 := by
  obtain ⟨a, b, r, s, ha, ha₉, hb₉, hr, hs, hdigits⟩ := h
  by_cases hb : b = 0
  · subst b
    iterate 11 right
    exact zero_block n a r s ha ha₉ hr hn hdigits
  have hb₁ : 1 ≤ b := by omega
  obtain ⟨p, hp⟩ := hn
  have hvalue := block_identity n a b r s hdigits
  have hvalue' : 9 * (n : ℤ) + a * 10 ^ s + b = a * 10 ^ (r + s) + b * 10 ^ s := by
    exact_mod_cast hvalue
  have hp' : (n : ℤ) = (p : ℤ) * p := by exact_mod_cast hp
  have he : (3 * (p : ℤ)) ^ 2 = a * 10 ^ (r + s) + ((b : ℤ) - a) * 10 ^ s - b := by
    nlinarith only [hvalue', hp']
  have hk := nonzero_length_bound a b s (r + s) p ha ha₉ hb₁ hb₉ hs (by omega) he
  have hformula : (a * 10 ^ (r + s) + b * 10 ^ s - a * 10 ^ s - b) / 9 = n := by omega
  have hsmall := short_cases ⟨a, by omega⟩ ⟨b, by omega⟩ ⟨r, by omega⟩ ⟨s, by omega⟩
    ha hb₁ hr hs hk
  dsimp only at hsmall
  rw [hformula] at hsmall
  have hsquare : n.sqrt ^ 2 = n := by rw [hp, ← pow_two, Nat.sqrt_eq']
  rcases hsmall hsquare with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp

end MetaMathlibExt
