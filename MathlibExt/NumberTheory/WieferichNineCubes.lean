/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/NumberTheory/WieferichNineCubes.lean` (leanprover/lean-eval),
problem `wieferich_g_three` at commit 38361be884302c7edce1908c4aef8296eb2cb27e.
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison (problem submitter)
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
lean-eval ships no `NOTICE` file.

The definition and theorem statement are adapted from this source via
`WantedExt/NumberTheory/WieferichNineCubesWanted.lean`. The proof is original.
-/

module

public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.QuadraticForms.LegendreThreeSquare

/-!
# Wieferich's theorem `g(3) = 9`

`wieferich_g_three` is Wieferich's theorem (Wieferich 1909, completed by
Kempner 1912): every natural number is a sum of nine cubes, and nine is the
smallest such bound — `23` requires nine cubes (`23 = 2·2³ + 7·1³`, with no
representation using eight or fewer cubes). This is the `k = 3` case of the
Hilbert–Waring problem (`g(3) = 9`).

`IsSumOfCubes k n` fixes the meaning of "sum of `k` cubes": `n` is a sum of
`k` cubes of natural numbers, zeros allowed, that is, of at most `k` positive
cubes. Oliver Knill records the case `g(3) = 9` in §76 of *Some Fundamental
Theorems in Mathematics*.

For large numbers we use Legendre's three-square theorem and the identity
`(m + x)³ + (m - x)³ = 2m³ + 6mx²`. The finite part starts with two bit tables
checked by the kernel. Subtracting a cube three times extends the six-cube table
to the threshold for the large-number argument.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.WieferichNineCubesWanted.NumberTheory

set_option linter.dupNamespace false in
/-- **Sum of $k$ cubes.** A natural number $n$ is a sum of $k$ cubes if there are natural numbers
$x_1, \dots, x_k$ with $n = x_1^3 + \dots + x_k^3$. -/
def IsSumOfCubes (k n : ℕ) : Prop :=
  ∃ x : Fin k → ℕ, ∑ i, (x i) ^ 3 = n

private theorem addCube {k n : ℕ} (hn : IsSumOfCubes k n) (a : ℕ) :
    IsSumOfCubes (k + 1) (a ^ 3 + n) := by
  obtain ⟨x, rfl⟩ := hn
  exact ⟨Fin.cons a x, by simp [Fin.sum_univ_succ]⟩

/- Bit i of the table records a representation of i. Shifting a table left by b³
adds that cube to every representation in the table. -/
private def cubeShifts (bits : ℕ) : ℕ → ℕ
  | 0 => bits
  | b + 1 => cubeShifts bits b ||| (bits <<< (b + 1) ^ 3)

private def cubeBits (bound : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => cubeShifts (cubeBits bound k) bound

private theorem cubeShifts_sound {bits k : ℕ}
    (h : ∀ n, bits.testBit n = true → IsSumOfCubes k n) (b n : ℕ)
    (hb : (cubeShifts bits b).testBit n = true) : IsSumOfCubes (k + 1) n := by
  induction b with
  | zero => simpa using addCube (h n hb) 0
  | succ b ih =>
    rw [cubeShifts, Nat.testBit_lor, Bool.or_eq_true] at hb
    rcases hb with hb | hb
    · exact ih hb
    · rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq] at hb
      simpa [Nat.add_sub_of_le hb.1] using addCube (h _ hb.2) (b + 1)

private theorem cubeBits_sound (b k n : ℕ)
    (h : (cubeBits b k).testBit n = true) : IsSumOfCubes k n := by
  induction k generalizing n with
  | zero =>
    obtain rfl := Nat.testBit_one_eq_true_iff_self_eq_zero.mp h
    exact ⟨Fin.elim0, by simp⟩
  | succ k ih => exact cubeShifts_sound ih b n h

private theorem bits_cover {b k lo len n : ℕ}
    (h : ((cubeBits b k >>> lo) % 2 ^ len) = 2 ^ len - 1)
    (hlo : lo ≤ n) (hhi : n < lo + len) : IsSumOfCubes k n := by
  have hbit := congrArg (fun t : ℕ => t.testBit (n - lo)) h
  have hlt : n - lo < len := by omega
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one, hlt, decide_true,
    Bool.true_and, Nat.testBit_shiftRight, Nat.add_sub_of_le hlo] at hbit
  exact cubeBits_sound b k n hbit

set_option exponentiation.threshold 2000000 in
private theorem six_cube_table :
    ((cubeBits 100 6 >>> 8043) % 2 ^ 991958) = 2 ^ 991958 - 1 := by decide +kernel

private theorem nine_cube_table :
    (cubeBits 21 9 >>> 0) % 2 ^ 8043 = 2 ^ 8043 - 1 := by decide +kernel

/-- Extend an interval by subtracting the largest cube that leaves at least `lo`.
The gaps between consecutive cubes up to `c³` fit inside the original interval. -/
private theorem extend_interval {k lo hi c : ℕ}
    (h : ∀ n, lo ≤ n → n ≤ hi → IsSumOfCubes k n)
    (hgap : lo + 3 * c ^ 2 + 3 * c ≤ hi) (n : ℕ)
    (hlo : lo ≤ n) (hhi : n ≤ lo + c ^ 3) : IsSumOfCubes (k + 1) n := by
  let q := Nat.nthRoot 3 (n - lo)
  have hq : q ^ 3 ≤ n - lo := Nat.pow_nthRoot_le (.inl (by decide))
  have hnext := Nat.lt_pow_nthRoot_add_one (by decide : 3 ≠ 0) (n - lo)
  change n - lo < (q + 1) ^ 3 at hnext
  have hqc : q ≤ c := (Nat.pow_le_pow_iff_left (by decide : 3 ≠ 0)).mp (by omega)
  have hhi' : n - q ^ 3 ≤ hi := by
    have hsq := Nat.pow_le_pow_left hqc 2
    have hdiff : n - lo + lo = n := Nat.sub_add_cancel hlo
    nlinarith [Nat.sub_add_cancel (show q ^ 3 ≤ n by omega)]
  simpa [Nat.add_sub_of_le (show q ^ 3 ≤ n by omega)] using
    addCube (h (n - q ^ 3) (by omega) hhi') q

/-- Six cubes cover the interval from 8043 through one million. Three applications
of the consecutive-cube gap bound extend it past the first dyadic scale. -/
private theorem nine_cubes_small (n : ℕ) (hn : n ≤ 600 * 32768 ^ 3) : IsSumOfCubes 9 n := by
  by_cases h : n < 8043
  · exact bits_cover nine_cube_table (Nat.zero_le _) (by omega)
  have six : ∀ n, 8043 ≤ n → n ≤ 1000000 → IsSumOfCubes 6 n :=
    fun n hn hN => bits_cover six_cube_table hn (by omega)
  have seven := extend_interval (c := 570) six (by decide)
  have eight := extend_interval (c := 7800) seven (by decide)
  exact extend_interval (c := 390000) eight (by decide) n (by omega) (by omega)

private theorem cube_root_mod_two_pow (j u : ℕ) (hu : Odd u) :
    ∃ x < 2 ^ (j + 1), x ^ 3 ≡ u [MOD 2 ^ (j + 1)] := by
  let m := 2 ^ (j + 1)
  have hc : (Nat.card (ZMod m)ˣ).Coprime 3 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    simp only [m, Nat.totient_prime_pow_succ Nat.prime_two, Nat.reduceSub, mul_one]
    exact Nat.Coprime.pow_left _ (by decide)
  let a := ZMod.unitOfCoprime u ((Nat.coprime_two_right.mpr hu).pow_right (j + 1))
  obtain ⟨v, hv⟩ := (powCoprime hc).surjective a
  change v ^ 3 = a at hv
  refine ⟨(v : ZMod m).val, ZMod.val_lt _, (ZMod.natCast_eq_natCast_iff ..).mp ?_⟩
  simpa [a, Nat.cast_pow, ZMod.natCast_zmod_val] using congrArg Units.val hv

/-- Choose a multiple of `d` in the required class modulo three, just below
the cube root of `R`. The spacing between consecutive choices is `3 * d`. -/
private theorem rounded_cube {m d R : ℕ} (hd : 0 < d) (hstep : 512 * d ≤ m)
    (hcop : d.Coprime 3) (hlo : m ^ 3 ≤ R) (hhi : R < (17 * m) ^ 3) :
    ∃ z, d ∣ z ∧ z ^ 3 ≡ R [MOD 3] ∧ z ^ 3 ≤ R ∧ R - z ^ 3 + 6 * m ≤ 6 * m ^ 3 := by
  let s := Nat.nthRoot 3 R
  have hs : s ^ 3 ≤ R := Nat.pow_nthRoot_le (.inl (by decide))
  have hslo : m ≤ s := (Nat.le_nthRoot_iff (by decide)).mpr hlo
  have hshi : s + 1 ≤ 17 * m := (Nat.nthRoot_lt_iff (by decide)).mpr hhi
  have hres : ∀ a b : Fin 3, a ≠ 0 → ∃ r : Fin 3, (a.val * r.val) ^ 3 % 3 = b.val := by
    decide
  have hd3 : d % 3 ≠ 0 := by
    intro hz
    have := hcop.gcd_eq_one
    rw [Nat.gcd_comm, Nat.gcd_rec, hz] at this
    simp at this
  obtain ⟨r, hr⟩ := hres ⟨d % 3, Nat.mod_lt _ (by decide)⟩
    ⟨R % 3, Nat.mod_lt _ (by decide)⟩ (fun h => hd3 (congrArg Fin.val h))
  let offset := d * r.val
  have hoff : offset ≤ s := calc
    d * r.val ≤ d * 3 := Nat.mul_le_mul_left _ r.isLt.le
    _ ≤ s := by omega
  let step := 3 * d
  let q := (s - offset) / step
  let z := offset + step * q
  have hdiv := Nat.mod_add_div (s - offset) step
  have hmod := Nat.mod_lt (s - offset) (show 0 < step by dsimp [step]; omega)
  have hz : z ≤ s := by dsimp [z, q]; omega
  have hnear : s + 1 ≤ z + 3 * d := by dsimp [z, q, step] at *; omega
  have hzc := Nat.pow_le_pow_left hz 3
  refine ⟨z, ⟨r.val + 3 * q, by dsimp [z, offset, step]; ring⟩, ?_, hzc.trans hs, ?_⟩
  · have hoffmod : offset ^ 3 ≡ R [MOD 3] :=
      (((Nat.mod_modEq d 3).mul_right r.val).pow 3).symm.trans hr
    have hzmod : z ≡ offset [MOD 3] := by
      change (offset + 3 * d * q) % 3 = offset % 3
      simp [Nat.add_mod, Nat.mul_assoc]
    exact (hzmod.pow 3).trans hoffmod
  · have hnext : R < (s + 1) ^ 3 := Nat.lt_pow_nthRoot_add_one (by decide) _
    have hdiff : (s + 1) ^ 3 ≤ z ^ 3 + 3 * (s + 1) ^ 2 * (3 * d) := by
      have h₁ := Nat.mul_le_mul_left ((s + 1) ^ 2 + (s + 1) * z + z ^ 2) hnear
      have h₂ := Nat.mul_le_mul_right (3 * d) (Nat.pow_le_pow_left (by omega : z ≤ s + 1) 2)
      have h₃ := Nat.mul_le_mul_right (3 * d) (Nat.mul_le_mul_left (s + 1) (by omega : z ≤ s + 1))
      nlinarith only [h₁, h₂, h₃]
    have hbound := Nat.mul_le_mul_right (9 * d) (Nat.pow_le_pow_left hshi 2)
    have hmargin := Nat.mul_le_mul_right (m ^ 2) (show 2601 * d + 6 ≤ 6 * m by omega)
    have hm : m ≤ m ^ 2 := Nat.le_self_pow (by decide) _
    nlinarith only [hdiff, hnext, hbound, hmargin, hm, Nat.sub_add_cancel (hzc.trans hs)]

/-- The three-square representation of `4b + 1` supplies three pairs of cubes. -/
private theorem six_from_three_squares {m b : ℕ} (hb : 4 * b + 1 ≤ m ^ 2) :
    IsSumOfCubes 6 (6 * m ^ 3 + 6 * m * (4 * b + 1)) := by
  obtain ⟨x, y, z, h⟩ := Nat.exists_three_squares_of_not_four_pow_mul_eight_mul_add_seven
    (4 * b + 1) (by
      rintro ⟨a, t, e⟩
      cases a with
      | zero => simp at e; omega
      | succ a => rw [pow_succ, mul_comm _ 4, mul_assoc] at e; omega)
  have hle (v : ℕ) (hv : v ^ 2 ≤ 4 * b + 1) : v ≤ m :=
    (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp (hv.trans hb)
  have hpair (v : ℕ) (hv : v ≤ m) :
      (m + v) ^ 3 + (m - v) ^ 3 = 2 * m ^ 3 + 6 * m * v ^ 2 := by
    obtain ⟨w, rfl⟩ := Nat.exists_eq_add_of_le hv
    simp only [Nat.add_sub_cancel_left]
    ring
  refine ⟨![m + x, m - x, m + y, m - y, m + z, m - z], ?_⟩
  simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Finset.univ_eq_empty,
    Finset.sum_empty, add_zero]
  nlinarith only [hpair x (hle _ (by omega)), hpair y (hle _ (by omega)),
    hpair z (hle _ (by omega)), congrArg (6 * m * ·) h]

/-- Work at a dyadic scale `m`. After reserving six paired cubes, subtract a parity
correction and solve a cube congruence modulo `8m`. The last cube is chosen near the
cube root of the remainder so the three square roots are all at most `m`. -/
private theorem nine_cubes_at_scale (k n : ℕ) (hk : 15 ≤ k)
    (hlo : 600 * (2 ^ k) ^ 3 ≤ n) (hhi : n < 4800 * (2 ^ k) ^ 3) : IsSumOfCubes 9 n := by
  let m := 2 ^ k
  let d := 2 ^ ((k + 5) / 3)
  have hd : 0 < d := pow_pos (by decide) _
  have hstep : 512 * d ≤ m := by
    change 2 ^ 9 * 2 ^ ((k + 5) / 3) ≤ 2 ^ k
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hdvd : 8 * m ∣ d ^ 3 := by
    change 2 ^ 3 * 2 ^ k ∣ (2 ^ ((k + 5) / 3)) ^ 3
    rw [← pow_add, ← pow_mul]
    exact Nat.pow_dvd_pow _ (by omega)
  change 600 * m ^ 3 ≤ n at hlo
  change n < 4800 * m ^ 3 at hhi
  have hm : m ≤ m ^ 3 := Nat.le_self_pow (by decide) _
  let e := (n + 1) % 2
  have he : e ^ 3 = e := by
    have : e < 2 := Nat.mod_lt _ (by decide)
    rcases (by omega : e = 0 ∨ e = 1) with h | h <;> simp [h]
  let u := n - (e ^ 3 + 6 * m ^ 3 + 6 * m)
  have he2 : e < 2 := Nat.mod_lt _ (by decide)
  have hu : u + (e ^ 3 + 6 * m ^ 3 + 6 * m) = n := by dsimp [u]; omega
  have huodd : Odd u := by
    rw [Nat.odd_iff]
    dsimp [e] at he hu
    omega
  obtain ⟨x, hx, hxmod⟩ := cube_root_mod_two_pow (k + 2) u huodd
  have hpow : 2 ^ (k + 2 + 1) = 8 * m := by dsimp [m]; ring
  rw [hpow] at hx hxmod
  have hxc := Nat.pow_le_pow_left hx.le 3
  let R := u - x ^ 3
  have hRx : R + x ^ 3 = u := by
    apply Nat.sub_add_cancel
    nlinarith only [hlo, hxc, hu, he, he2, hm, hd, hstep]
  have hRlo : m ^ 3 ≤ R := by nlinarith only [hlo, hxc, hu, hRx, he, he2, hm, hd, hstep]
  have hRhi : R < (17 * m) ^ 3 := by
    have hRn : R ≤ n := by omega
    nlinarith only [hhi, hRn, Nat.zero_le (m ^ 3)]
  have hc : d.Coprime 3 := (show Nat.Coprime 2 3 by decide).pow_left _
  obtain ⟨z, hz, hzmod, hzle, hgap⟩ := rounded_cube hd hstep hc hRlo hRhi
  have hRdiv : 8 * m ∣ R := hxmod.dvd'
  have hzdiv : 8 * m ∣ z ^ 3 := hdvd.trans (pow_dvd_pow_of_dvd hz 3)
  have h3 : 3 ∣ R - z ^ 3 := hzmod.dvd'
  have hcop : (8 * m).Coprime 3 := hpow ▸ (show Nat.Coprime 2 3 by decide).pow_left _
  obtain ⟨b, hb⟩ := hcop.mul_dvd_of_dvd_of_dvd (Nat.dvd_sub hRdiv hzdiv) h3
  have hdif := Nat.sub_add_cancel hzle
  have hcancel : 6 * m * (4 * b + 1) ≤ 6 * m * m ^ 2 := by nlinarith only [hgap, hb]
  have hbnd : 4 * b + 1 ≤ m ^ 2 := Nat.le_of_mul_le_mul_left hcancel (by omega)
  have six := six_from_three_squares hbnd
  have hsum := addCube (addCube (addCube six z) x) e
  convert hsum using 1
  nlinarith only [hu, hRx, hdif, hb]

private theorem nine_cubes (n : ℕ) : IsSumOfCubes 9 n := by
  by_cases hn : n ≤ 600 * 32768 ^ 3
  · exact nine_cubes_small n hn
  let s := Nat.nthRoot 3 (n / 600)
  have hs : 2 ^ 15 ≤ s := (Nat.le_nthRoot_iff (by decide)).mpr (by omega)
  let k := Nat.log 2 s
  have hk : 15 ≤ k := Nat.le_log_of_pow_le (by decide) hs
  have hl : 2 ^ k ≤ s := Nat.pow_log_le_self _ (by omega)
  have hh : s < 2 ^ k * 2 := by
    simpa [k, pow_succ] using Nat.lt_pow_succ_log_self (by decide : 1 < 2) s
  apply nine_cubes_at_scale k n hk
  · have h := (Nat.le_nthRoot_iff (by decide)).mp hl
    omega
  · have h := (Nat.nthRoot_lt_iff (by decide)).mp hh
    rw [mul_pow] at h
    omega

private theorem twenty_three_requires_nine : ¬ IsSumOfCubes 8 23 := by
  rintro ⟨x, hx⟩
  have hsmall (i) : x i ≤ 2 := by
    have h := Finset.single_le_sum (f := fun j => x j ^ 3) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
    rw [hx] at h
    by_contra! h'
    have hc : 27 ≤ x i ^ 3 := Nat.pow_le_pow_left h' 3
    omega
  -- Count the summands equal to eight. Two such summands leave room for at most six ones.
  let t (i : Fin 8) := x i ^ 3 / 8
  have upper (i) : x i ^ 3 ≤ 1 + 7 * t i := by
    have := hsmall i
    dsimp [t]
    interval_cases x i <;> decide
  have lower (i) : 8 * t i ≤ x i ^ 3 := by dsimp [t]; omega
  have hu := Finset.sum_le_sum (s := Finset.univ) (fun i _ => upper i)
  have hl := Finset.sum_le_sum (s := Finset.univ) (fun i _ => lower i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one, hx] at hu hl
  omega

set_option linter.dupNamespace false in
/-- **Wieferich's nine cubes theorem.** Every natural number is a sum of $9$ cubes of natural
numbers, and $9$ cannot be replaced by $8$: some natural number is not a sum of $8$ cubes of
natural numbers.

Source: A. Wieferich, *Beweis des Satzes, daß sich eine jede ganze Zahl als Summe von
höchstens neun positiven Kuben darstellen läßt*, Math. Ann. 66 (1909); A. Kempner, *Über das
Waringsche Problem und einige Verallgemeinerungen*, Math. Ann. 72 (1912). Knill, *Some fundamental
theorems in mathematics*, §76. Via leanprover/lean-eval@38361be, problem `wieferich_g_three`. -/
public theorem wieferich_g_three :
    (∀ n : ℕ, IsSumOfCubes 9 n) ∧ ∃ n : ℕ, ¬ IsSumOfCubes 8 n :=
  ⟨nine_cubes, 23, twenty_three_requires_nine⟩

end MathlibExt.NumberTheory.WieferichNineCubesWanted.NumberTheory
