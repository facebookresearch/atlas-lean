/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Set.Insert
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Triangular numbers with a single repeated digit

The positive triangular numbers with a constant decimal digit are 1, 3, 6, 55, 66, and 666.

Statement from Christian Hercher and Karl Fegert, "Triangular Numbers
With a Single Repeated Digit", *Journal of Integer Sequences* 28
(2025), Article 25.2.1
(<https://cs.uwaterloo.ca/journals/JIS/VOL28/Hercher/hercher33.html>).

Triangular numbers are indexed from `1`, as in the source's list. The
digit condition says that every entry of `Nat.digits 10 m` is one digit
`d` that actually occurs in the list.
-/

set_option autoImplicit false

namespace MathlibExt.NumberTheory.Digits.TriangularRepdigitsWanted

-- Multiplication by a - b√D descends in the second coordinate whenever y ≥ B.
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
    linarith [mul_le_mul_of_nonneg_left hB (show 0 ≤ 2 * (a - 1) by omega)]
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

-- Data for x² - D y² = c. The unit (a,b) generates the residue cycles from the seeds.
-- The chosen coordinate must equal scale · 10^r for a repdigit of length 2r or 2r+1.
private structure PellCase where
  D : ℤ
  c : ℤ
  a : ℤ
  b : ℤ
  bound : ℕ
  modulus : ℤ
  seeds : List (ℤ × ℤ)
  period : ℕ
  coord : ℤ × ℤ → ℤ
  scale : ℤ
  powerPeriod : ℕ

private def PellCase.next (s : PellCase) (p : ℤ × ℤ) : ℤ × ℤ :=
  ((s.a * p.1 + s.D * s.b * p.2) % s.modulus, (s.b * p.1 + s.a * p.2) % s.modulus)

private def PellCase.residues (s : PellCase) : List (ℤ × ℤ) :=
  s.seeds.flatMap fun (x, y) ↦ List.iterate s.next (x % s.modulus, y % s.modulus) s.period

private def PellCase.powers (s : PellCase) : List ℤ :=
  List.iterate (fun z ↦ z * 10 % s.modulus) (s.scale * 10 ^ 4 % s.modulus) s.powerPeriod

-- These finite checks certify the descent threshold, the base cases, closure of
-- both residue lists, and their disjointness in the specified coordinate.
private abbrev PellCase.Valid (s : PellCase) : Prop :=
  0 < s.D ∧ 1 < s.a ∧ 0 ≤ s.b ∧ s.a ^ 2 - s.D * s.b ^ 2 = 1 ∧
  0 ≤ s.D * s.bound ^ 2 + s.a ^ 2 * s.c ∧ 0 ≤ (s.bound : ℤ) ^ 2 - s.b ^ 2 * s.c ∧
  0 < 2 * (s.a - 1) * s.bound ^ 2 + s.b ^ 2 * s.c ∧
  (∀ j : Fin s.bound, let y : ℤ := j.val
    let x := Int.sqrt (s.D * y ^ 2 + s.c)
    x ^ 2 - s.D * y ^ 2 = s.c → (x % s.modulus, y % s.modulus) ∈ s.residues) ∧
  (∀ p ∈ s.residues, s.next p ∈ s.residues) ∧
  s.scale * 10 ^ 4 % s.modulus ∈ s.powers ∧
  (∀ z ∈ s.powers, z * 10 % s.modulus ∈ s.powers) ∧
  ∀ p ∈ s.residues, s.coord p ∉ s.powers

private theorem PellCase.exclude (s : PellCase) (hs : s.Valid) {x y : ℤ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (he : x ^ 2 - s.D * y ^ 2 = s.c) {r : ℕ} (hr : 4 ≤ r) :
    s.coord (x % s.modulus, y % s.modulus) ≠ s.scale * 10 ^ r % s.modulus := by
  obtain ⟨hD, ha, hb, hu, h₁, h₂, h₃, base, step, start, next, disj⟩ := hs
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
  rw [h]
  clear h
  induction r, hr using Nat.le_induction with
  | base => exact start
  | succ n hn ih =>
    rw [pow_succ, ← mul_assoc]
    exact ((Int.mod_modEq _ _).mul_right 10).eq ▸ next _ ih

-- Each modulus combines the two moduli in the corresponding Pell calculation of the paper.
private def oneEven : PellCase := ⟨2, 1, 3, 2, 3, 35, [(1, 0)], 6, Prod.snd, 2, 6⟩
private def oneOdd : PellCase := ⟨20, 1, 9, 2, 3, 55, [(1, 0)], 10, Prod.snd, 2, 2⟩
private def fiveEven : PellCase := ⟨10, -31, 19, 6, 34, 56, [(3, 2), (63, 20)], 8, Prod.snd, 2, 6⟩
private def sixEven : PellCase := ⟨3, 13, 2, 1, 4, 12050, [(4, 1), (5, 2)], 30, Prod.fst, 4, 30⟩
private def sixOdd : PellCase := ⟨30, -39, 11, 2, 13, 1984, [(9, 2), (21, 4)], 32, Prod.snd, 4, 15⟩

private theorem cases_valid :
    oneEven.Valid ∧ oneOdd.Valid ∧ fiveEven.Valid ∧ sixEven.Valid ∧ sixOdd.Valid := by
  repeat' apply And.intro
  all_goals decide +kernel

private theorem digit_candidates {d i x : ℕ} (hd : d < 10) (hd₀ : 0 < d) (hi : 2 ≤ i)
    (he : x ^ 2 + 8 * d = 8 * d * 10 ^ i + 9) : d = 1 ∨ d = 5 ∨ d = 6 := by
  have hz : 10 ^ i ≡ 0 [MOD 100] := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
    rw [pow_add]
    simpa using (show 10 ^ 2 ≡ 0 [MOD 100] by decide).mul_right (10 ^ j)
  have hres : (x % 100) ^ 2 + 8 * d ≡ 9 [MOD 100] := by
    calc
      _ ≡ x ^ 2 + 8 * d [MOD 100] := ((Nat.mod_modEq _ _).pow 2).add_right _
      _ = _ := he
      _ ≡ _ [MOD 100] := by simpa using (hz.mul_left (8 * d)).add_right 9
  have check : ∀ d : Fin 10, ∀ x : Fin 100, 0 < d.val →
      x.val ^ 2 + 8 * d.val ≡ 9 [MOD 100] → d.val = 1 ∨ d.val = 5 ∨ d.val = 6 := by
    decide +kernel
  exact check ⟨d, hd⟩ ⟨x % 100, by omega⟩ hd₀ hres

private theorem five_odd_impossible (x : ℤ) (r : ℕ)
    (he : x ^ 2 + 40 = 40 * 10 ^ (2 * r + 1) + 9) : False := by
  have hp : (10 : ℤ) ^ (2 * r + 1) ≡ -1 [ZMOD 11] := by
    rw [pow_succ, pow_mul]
    have h := ((by decide : (10 : ℤ) ^ 2 ≡ 1 [ZMOD 11]).pow r).mul
      (by decide : (10 : ℤ) ≡ -1 [ZMOD 11])
    simpa using h
  have hr : (x % 11) ^ 2 + 40 ≡ -31 [ZMOD 11] := by
    calc
      _ ≡ x ^ 2 + 40 [ZMOD 11] := ((Int.mod_modEq _ _).pow 2).add_right _
      _ = _ := he
      _ ≡ _ [ZMOD 11] := (hp.mul_left 40).add_right 9
  have check : ∀ z : Fin 11, ¬ ((z.val : ℤ) ^ 2 + 40 ≡ -31 [ZMOD 11]) := by decide
  have hx : 0 ≤ x % 11 := by omega
  exact check ⟨(x % 11).toNat, by omega⟩ (by simpa only [Int.toNat_of_nonneg hx] using hr)

private theorem length_lt_eight {d i p : ℕ} (hd : d < 10) (hd₀ : 0 < d)
    (he : (3 * p) ^ 2 + 8 * d = 8 * d * 10 ^ i + 9) : i < 8 := by
  by_contra! h
  obtain ⟨oneEven_valid, oneOdd_valid, fiveEven_valid, sixEven_valid, sixOdd_valid⟩ := cases_valid
  have cases := digit_candidates hd hd₀ (by omega : 2 ≤ i) he
  have he' : (3 * (p : ℤ)) ^ 2 + 8 * d = 8 * d * 10 ^ i + 9 := by exact_mod_cast he
  let r := i / 2
  have hr : 4 ≤ r := by dsimp [r]; omega
  rcases (show i = 2 * r ∨ i = 2 * r + 1 by dsimp [r]; omega) with hi | hi
  · rw [hi, pow_mul'] at he'
    rcases cases with rfl | rfl | rfl
    · apply oneEven.exclude oneEven_valid (x := 3 * p) (y := 2 * 10 ^ r) (by positivity)
        (by positivity) _ hr rfl
      change (3 * (p : ℤ)) ^ 2 - 2 * (2 * 10 ^ r) ^ 2 = 1
      push_cast at he'
      linarith only [he']
    · apply fiveEven.exclude fiveEven_valid (x := 3 * p) (y := 2 * 10 ^ r) (by positivity)
        (by positivity) _ hr rfl
      change (3 * (p : ℤ)) ^ 2 - 10 * (2 * 10 ^ r) ^ 2 = -31
      push_cast at he'
      linarith only [he']
    · apply sixEven.exclude sixEven_valid (x := 4 * 10 ^ r) (y := p) (by positivity)
        (by positivity) _ hr rfl
      change (4 * (10 : ℤ) ^ r) ^ 2 - 3 * p ^ 2 = 13
      push_cast at he'
      linarith only [he']
  · rw [hi] at he'
    rcases cases with rfl | rfl | rfl
    · apply oneOdd.exclude oneOdd_valid (x := 3 * p) (y := 2 * 10 ^ r) (by positivity)
        (by positivity) _ hr rfl
      change (3 * (p : ℤ)) ^ 2 - 20 * (2 * 10 ^ r) ^ 2 = 1
      rw [pow_succ (10 : ℤ), pow_mul'] at he'
      push_cast at he'
      linarith only [he']
    · exact five_odd_impossible (3 * p) r (by norm_num at he' ⊢; exact he')
    · apply sixOdd.exclude sixOdd_valid (x := 3 * p) (y := 4 * 10 ^ r) (by positivity)
        (by positivity) _ hr rfl
      change (3 * (p : ℤ)) ^ 2 - 30 * (4 * 10 ^ r) ^ 2 = -39
      rw [pow_succ (10 : ℤ), pow_mul'] at he'
      push_cast at he'
      linarith only [he']

private theorem repdigit_identity (d i : ℕ) :
    9 * Nat.ofDigits 10 (List.replicate i d) + d = d * 10 ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [List.replicate_succ, Nat.ofDigits_cons, pow_succ]
    linarith only [ih]

private theorem short_cases : ∀ i : Fin 8, ∀ d : Fin 10,
    let m := (d.val * 10 ^ i.val - d.val) / 9
    0 < m → (8 * m + 1).sqrt ^ 2 = 8 * m + 1 →
      m = 1 ∨ m = 3 ∨ m = 6 ∨ m = 55 ∨ m = 66 ∨ m = 666 := by
  decide +kernel

/-- **Triangular repdigits.** The positive triangular numbers $n(n+1)/2$ with $n \ge 1$ whose
decimal representation consists of a single repeated digit are exactly $1$, $3$, $6$, $55$, $66$
and $666$.

Source: Christian Hercher and Karl Fegert, "Triangular Numbers With a
Single Repeated Digit", Theorem 1 (TeX label `Thm:main`). -/
public theorem triangular_numbers_single_repeated_digit :
    {m : ℕ |
      (∃ n : ℕ, 1 ≤ n ∧ 2 * m = n * (n + 1)) ∧
        ∃ d : ℕ, d < 10 ∧ d ∈ Nat.digits 10 m ∧
          ∀ a ∈ Nat.digits 10 m, a = d} =
      {1, 3, 6, 55, 66, 666} := by
  ext m
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨n, hn, htri⟩, d, hd, _, hall⟩
    let i := (Nat.digits 10 m).length
    have hrep := repdigit_identity d i
    rw [← (List.eq_replicate_iff.mpr ⟨rfl, hall⟩ : Nat.digits 10 m = List.replicate i d),
      Nat.ofDigits_digits] at hrep
    have hm : 0 < m := by nlinarith
    have hd₀ : 0 < d := by
      by_contra! hz
      simp [Nat.eq_zero_of_le_zero hz] at hrep
      omega
    have hsq : (2 * n + 1) ^ 2 = 8 * m + 1 := by linarith only [htri]
    have he : (3 * (2 * n + 1)) ^ 2 + 8 * d = 8 * d * 10 ^ i + 9 := by
      linarith only [hsq, hrep]
    have hi := length_lt_eight hd hd₀ he
    have hm' : (d * 10 ^ i - d) / 9 = m := by omega
    have hsmall := short_cases ⟨i, hi⟩ ⟨d, hd⟩
    dsimp only at hsmall
    rw [hm'] at hsmall
    exact hsmall hm (by rw [← hsq, Nat.sqrt_eq'])
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨⟨1, by decide⟩, 1, by decide +kernel⟩
    · exact ⟨⟨2, by decide⟩, 3, by decide +kernel⟩
    · exact ⟨⟨3, by decide⟩, 6, by decide +kernel⟩
    · exact ⟨⟨10, by decide⟩, 5, by decide +kernel⟩
    · exact ⟨⟨11, by decide⟩, 6, by decide +kernel⟩
    · exact ⟨⟨36, by decide⟩, 6, by decide +kernel⟩

end MathlibExt.NumberTheory.Digits.TriangularRepdigitsWanted
