/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PalindromeAPCountOfDvdBase
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Data.List.GetD
import MathlibExt.NumberTheory.DigitSumCongruenceCount
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Palindromes modulo a divisor of the base minus one

For natural numbers `b ≥ 2`, `m ≥ 1`, `q ≥ 1` and `r < q` with `b ≡ 1 [MOD q]`,
we give an exact formula for the number of positive base-`b` palindromes at most `m` in
residue class `r`. Each pair of reflected digits contributes twice its digit, while a center
contributes once. We sum over complete blocks of centers before the cutoff and split the
remaining prefix count at the first digit where a prefix is smaller than the bound's prefix.
The formula uses natural division for `r / 2` when `q` is even; for odd `r` the branches
only use congruences at a center, where no division of `r` is needed.

## References

* Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Phakhinkon Napp Phunphayap and
  Prapanpong Pongsriiam, *Exact Formulas for the Number of Palindromes in Certain Arithmetic
  Progressions*, Journal of Integer Sequences 27 (2024), Article 24.4.8, pp. 1–29,
  Theorem 9 and Lemmas 2 and 4.
* `MathlibExt.NumberTheory.PalindromesArithmeticProgressions` supplies the mirror and cutoff
  enumeration (`mirror_eq`, `count_split_card`, `mirror_modEq`, and `cutoff_base_pow`). The bound on
  the low digits follows the argument in `mirror_strictMono`.
* `MathlibExt.NumberTheory.PalindromeAPCountOfDvdBase` supplies `halfCopy_eq_ofDigits`,
  `digits_drop_div` and `prefix_as_sum` for translating between prefixes and digits.
* `MathlibExt.NumberTheory.DigitSumCongruenceCount` supplies the interval residue sums
  `sum_residueIndicator_range` and `sum_residueIndicator_base`.
-/

namespace MetaMathlibExt

open Finset
open abs_palindromeAPCount_sub_le palindromeAPCount_of_dvd_base

private abbrev residuePrefix (q : ℕ) (r : ℤ) (n : ℕ) : ℚ :=
  ∑ x ∈ range n, residueIndicator q r x

private def doubledPrefix (q r n : ℕ) : ℚ :=
  ∑ x ∈ range n, residueIndicator q r (2 * x : ℕ)

private def centeredPrefix (b q r n : ℕ) : ℚ :=
  ∑ x ∈ range n, residueIndicator q r (2 * (x / b) + x % b : ℕ)

private theorem residueIndicator_congr_left {q : ℕ} {r x y : ℤ} (h : x ≡ y [ZMOD q]) :
    residueIndicator q r x = residueIndicator q r y := by
  simp only [residueIndicator_eq, show (x ≡ r [ZMOD q]) ↔ (y ≡ r [ZMOD q]) from
    ⟨h.symm.trans, h.trans⟩]

private theorem doubledPrefix_odd {q : ℕ} (hq : Odd q) (r n : ℕ) :
    doubledPrefix q r n = residuePrefix q (((q + 1) / 2 * r : ℕ) : ℤ) n := by
  simp only [doubledPrefix, residuePrefix, residueIndicator_eq, Int.natCast_modEq_iff,
    double_iff hq]

private theorem doubledIndicator_even_odd {q r x : ℕ} (hq : Even q) (hr : Odd r) :
    ¬ (2 * x ≡ r [MOD q]) := by
  intro h
  have H := h.of_dvd (even_iff_two_dvd.mp hq)
  simp [Nat.ModEq, Nat.odd_iff.mp hr] at H

private theorem doubledPrefix_even_odd {q r : ℕ} (hq : Even q) (hr : Odd r) (n : ℕ) :
    doubledPrefix q r n = 0 := by
  apply sum_eq_zero
  intro x _
  simp only [residueIndicator_eq, Int.natCast_modEq_iff]
  exact ite_eq_right (doubledIndicator_even_odd hq hr)

private theorem double_iff_half_modulus {q r x : ℕ} (hq : Even q) (hr : Even r) :
    2 * x ≡ r [MOD q] ↔ x ≡ r / 2 [MOD q / 2] := by
  have hq' := Nat.even_iff.mp hq
  have hr' := Nat.even_iff.mp hr
  conv_lhs =>
    rw (occs := .pos [1]) [← show 2 * (q / 2) = q by omega, ← show 2 * (r / 2) = r by omega]
  exact Nat.ModEq.mul_left_cancel_iff' (by decide : 2 ≠ 0)

private theorem doubledPrefix_even_even {q r : ℕ} (hq : Even q) (hr : Even r) (n : ℕ) :
    doubledPrefix q r n = residuePrefix (q / 2) ((r / 2 : ℕ) : ℤ) n := by
  simp only [doubledPrefix, residuePrefix, residueIndicator_eq, Int.natCast_modEq_iff,
    double_iff_half_modulus hq hr]

-- Count complete center blocks first, then count the centers of the last, partial block.
private theorem centeredPrefix_eq {b q : ℕ} (hb : 2 ≤ b) (hq : 0 < q)
    (hbq : b ≡ 1 [MOD q]) (r u c : ℕ) (hc : c ≤ b) :
    centeredPrefix b q r (b * u + c) =
      (b - 1 : ℚ) * u / q + doubledPrefix q r u + residuePrefix q ((r : ℤ) - 2 * u) c := by
  have hblock (v t : ℕ) (ht : t ≤ b) :
      (∑ i ∈ range t, residueIndicator q r
        (2 * ((b * v + i) / b) + (b * v + i) % b : ℕ)) = residuePrefix q ((r : ℤ) - 2 * v) t := by
    apply sum_congr rfl
    intro i hi
    have hlt := (mem_range.mp hi).trans_le ht
    rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hlt, Nat.add_zero,
      Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
    push_cast
    exact residueIndicator_add q r (2 * v) i
  have hfull (v : ℕ) : centeredPrefix b q r (b * v) =
      ((b : ℚ) - 1) * v / q + doubledPrefix q r v := by
    induction v with
    | zero => simp [centeredPrefix, doubledPrefix]
    | succ v ih =>
      rw [Nat.mul_succ, centeredPrefix, sum_range_add, ← centeredPrefix, ih, hblock v b le_rfl,
        show residuePrefix q ((r : ℤ) - 2 * v) b = _ from
          sum_residueIndicator_base (by omega) hq hbq _, ← residueIndicator_add, add_zero]
      simp only [doubledPrefix, sum_range_succ, Nat.cast_succ, Nat.cast_mul]
      norm_num only [Nat.cast_ofNat]
      ring
  rw [centeredPrefix, sum_range_add, ← centeredPrefix, hfull, hblock u c hc]

-- The successive blocks have lengths `w j`, but their congruence shifts are just the digits.
private theorem residuePrefix_blocks {q n : ℕ} (r : ℤ) (w a : ℕ → ℕ)
    (hw : ∀ j < n, w j ≡ a j [MOD q]) :
    residuePrefix q r (∑ j ∈ range n, w j) =
      ∑ j ∈ range n, residuePrefix q (r - ∑ i ∈ range j, (a i : ℤ)) (w j) := by
  induction n with
  | zero => simp [residuePrefix]
  | succ n ih =>
    rw [sum_range_succ, sum_range_succ]
    have hsplit (x y : ℕ) : residuePrefix q r (x + y) =
        residuePrefix q r x + ∑ i ∈ range y, residueIndicator q r ((x + i : ℕ) : ℤ) :=
      sum_range_add (fun i : ℕ => residueIndicator q r i) x y
    rw [hsplit, ih (fun j hj => hw j (by omega))]
    congr 1
    have h : (∑ i ∈ range n, w i) ≡ (∑ i ∈ range n, a i) [MOD q] :=
      Nat.ModEq.sum fun i hi => hw i (by have := mem_range.mp hi; omega)
    have hz := Int.natCast_modEq_iff.mpr h
    push_cast at hz
    apply sum_congr rfl
    intro i _
    rw [Nat.cast_add, Nat.cast_sum]
    rw [residueIndicator_congr_left (hz.add_right i), residueIndicator_add]

private theorem modEq_weightedDigit {b q : ℕ} (hbq : b ≡ 1 [MOD q]) (a j : ℕ) :
    a * b ^ j ≡ a [MOD q] := by
  simpa using (hbq.pow j).mul_left a

private theorem residuePrefix_weightedDigit {b q : ℕ} (hq : 0 < q) (hbq : b ≡ 1 [MOD q])
    (r : ℤ) (a j : ℕ) :
    residuePrefix q r (a * b ^ j) =
      (((a * b ^ j) / q : ℕ) : ℚ) + (if r % q < ((a % q : ℕ) : ℤ) then 1 else 0) := by
  unfold residuePrefix
  rw [sum_residueIndicator_range _ hq, show (a * b ^ j) % q = a % q from
    modEq_weightedDigit hbq a j]

private theorem residuePrefix_weightedDigit_exact {b q : ℕ} (hq : 0 < q)
    (hbq : b ≡ 1 [MOD q]) (r : ℤ) (a j : ℕ) :
    residuePrefix q r (a * b ^ j) =
      ((a : ℚ) * b ^ j - (a % q : ℕ)) / q +
        (if r % q < ((a % q : ℕ) : ℤ) then 1 else 0) := by
  rw [residuePrefix_weightedDigit hq hbq]
  congr 1
  apply (eq_div_iff (by positivity : (q : ℚ) ≠ 0)).2
  have hd := Nat.div_add_mod (a * b ^ j) q
  rw [show (a * b ^ j) % q = a % q from modEq_weightedDigit hbq a j] at hd
  have H := congrArg (fun x : ℕ => (x : ℚ)) hd
  push_cast at H
  linarith

private theorem residuePrefix_pow {b q : ℕ} (hb : 2 ≤ b) (hq : 0 < q) (hbq : b ≡ 1 [MOD q])
    (r : ℤ) (j : ℕ) :
    residuePrefix q r (b ^ j) = ((b : ℚ) ^ j - 1) / q + residueIndicator q r 0 := by
  simpa only [Nat.cast_pow] using
    sum_residueIndicator_base (b := b ^ j) (Nat.one_le_pow _ _ (by omega)) hq
    (by simpa using hbq.pow j) r

-- The lower mirrored digits occupy strictly less than one unit of the leading half.
private theorem mirror_bounds {b : ℕ} (hb : 2 ≤ b) (e x : ℕ) :
    b ^ ((b.digits x).length - e) * x ≤ mirror b e x ∧
      mirror b e x < b ^ ((b.digits x).length - e) * (x + 1) := by
  let low := ((b.digits x).drop e).reverse
  have hl : low.length = (b.digits x).length - e := by simp [low]
  have hlt : Nat.ofDigits b low < b ^ low.length :=
    Nat.ofDigits_lt_base_pow_length hb fun _ hi =>
      Nat.digits_lt_base hb (List.mem_of_mem_drop (List.mem_reverse.mp hi))
  rw [← hl, mirror_eq]
  change _ ≤ Nat.ofDigits b (low ++ b.digits x) ∧ Nat.ofDigits b (low ++ b.digits x) < _
  rw [Nat.ofDigits_append, Nat.ofDigits_digits, Nat.mul_succ]
  exact ⟨Nat.le_add_left _ _, by omega⟩

private theorem active_cutoff {b m k : ℕ} (hb : 2 ≤ b) (hk : (b.digits m).length = k + 1) :
    let H := m / b ^ ((k + 1) / 2)
    let e := (k + 1) % 2
    mirror b e H = palindromicHalfCopy b m ∧
      cutoff b e m + 1 = H + (if palindromicHalfCopy b m ≤ m then 1 else 0) := by
  dsimp only
  let t := (k + 1) / 2
  let e := (k + 1) % 2
  let H := m / b ^ t
  have hlen : (b.digits H).length - e = t := by
    simp only [H, digits_drop_div hb, List.length_drop, hk, e, t]
    omega
  have hcopy : mirror b e H = palindromicHalfCopy b m := by
    simp only [mirror_eq, H, digits_drop_div hb, List.drop_drop, halfCopy_eq_ofDigits, hk,
      e, t]
  refine ⟨hcopy, ?_⟩
  have ht : 0 < b ^ t := by positivity
  have hlo : H * b ^ t ≤ m := Nat.div_mul_le_self _ _
  have hhi : m < (H + 1) * b ^ t := (Nat.div_lt_iff_lt_mul ht).mp (Nat.lt_succ_self H)
  have below (x : ℕ) (hx : x < H) : x ≤ cutoff b e m := by
    apply (le_cutoff hb).mpr
    have hlen' : (b.digits x).length - e ≤ t := hlen ▸
      Nat.sub_le_sub_right (Nat.le_length_digits_le b x H hx.le) e
    calc
      mirror b e x ≤ b ^ ((b.digits x).length - e) * (x + 1) := (mirror_bounds hb e x).2.le
      _ ≤ b ^ t * H := Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) hlen') (by omega)
      _ ≤ m := by rwa [mul_comm]
  have above (x : ℕ) (hx : H < x) : ¬ x ≤ cutoff b e m := by
    rw [le_cutoff hb]
    have hlen' : t ≤ (b.digits x).length - e := hlen ▸
      Nat.sub_le_sub_right (Nat.le_length_digits_le b H x hx.le) e
    apply not_le_of_gt
    calc
      m < (H + 1) * b ^ t := hhi
      _ ≤ b ^ ((b.digits x).length - e) * x := by
        rw [mul_comm (H + 1)]
        exact Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) hlen') (by omega)
      _ ≤ mirror b e x := (mirror_bounds hb e x).1
  change cutoff b e m + 1 = H + _
  have hup : cutoff b e m ≤ H := by
    by_contra! h
    exact above _ h le_rfl
  by_cases h : palindromicHalfCopy b m ≤ m
  · have hd : H ≤ cutoff b e m := (le_cutoff hb).mpr (hcopy.symm ▸ h)
    simp [h, le_antisymm hup hd]
  · have hne : ¬ H ≤ cutoff b e m := by rwa [le_cutoff hb, hcopy]
    have hd := below (H - 1) (by omega)
    simp only [h, ite_false, add_zero]
    omega

private theorem inactive_cutoff {b m k : ℕ} (hb : 2 ≤ b) (hk : (b.digits m).length = k + 1) :
    cutoff b (k % 2) m + 1 = b ^ ((k + 1) / 2) := by
  have hlt : m < b ^ (k + 1) := (Nat.digits_length_le_iff hb m).mp hk.le
  have hmono : Monotone (cutoff b (k % 2)) := fun _ _ h =>
    (le_cutoff hb).mpr (((le_cutoff hb).mp le_rfl).trans h)
  have he : k % 2 ≤ 1 := by omega
  have hupper := hmono hlt.le
  rw [cutoff_base_pow hb (by omega) he, show (k + 1 + k % 2) / 2 = (k + 1) / 2 by omega]
    at hupper
  have hpos : 0 < b ^ ((k + 1) / 2) := by positivity
  by_cases hz : k = 0
  · simp [hz] at hupper ⊢
    omega
  · have hle : b ^ k ≤ m := (Nat.lt_digits_length_iff hb m).mp (by rw [hk]; omega)
    have hlower := hmono hle
    rw [cutoff_base_pow hb (by omega) he, show (k + k % 2) / 2 = (k + 1) / 2 by omega]
      at hlower
    omega

private theorem sum_range_eq_filter_Ioc (n : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (∑ x ∈ range (n + 1), if p x then (1 : ℚ) else 0) =
      (((Ioc 0 n).filter p).card : ℚ) + if p 0 then 1 else 0 := by
  have h : range (n + 1) = insert 0 (Ioc 0 n) := by
    ext x
    simp only [mem_range, mem_insert, mem_Ioc]
    omega
  rw [h, sum_insert (by simp), ← sum_filter, sum_const, nsmul_one, add_comm]

private theorem mirror_center_modEq {b q : ℕ} (hb : 2 ≤ b) (hbq : b ≡ 1 [MOD q]) (x : ℕ) :
    mirror b 1 x ≡ 2 * (x / b) + x % b [MOD q] := by
  have h : mirror b 1 x ≡ x + x / b [MOD q] := by simpa using mirror_modEq hb hbq 1 x
  have hx : x ≡ x / b + x % b [MOD q] := by
    calc
      x = b * (x / b) + x % b := (Nat.div_add_mod x b).symm
      _ ≡ x / b + x % b [MOD q] := by simpa using (hbq.mul_right (x / b)).add_right (x % b)
  simpa only [two_mul, add_right_comm] using h.trans (hx.add_right (x / b))

private theorem mirror_zero_modEq {b q : ℕ} (hb : 2 ≤ b) (hbq : b ≡ 1 [MOD q]) (x : ℕ) :
    mirror b 0 x ≡ 2 * x [MOD q] := by
  simpa [two_mul] using mirror_modEq hb hbq 0 x

private theorem count_mirrorPrefixes {b m q r k : ℕ} (hb : 2 ≤ b)
    (hk : (b.digits m).length = k + 1) (hr : r < q) (hbq : b ≡ 1 [MOD q]) :
    let H := m / b ^ ((k + 1) / 2)
    let P := b ^ ((k + 1) / 2)
    (palindromeAPCount b m q r : ℚ) =
      doubledPrefix q r (if Odd k then H else P) + centeredPrefix b q r (if Odd k then P else H) -
        (if r = 0 then 2 else 0) +
        (if palindromicHalfCopy b m ≤ m ∧ palindromicHalfCopy b m ≡ r [MOD q] then 1 else 0) := by
  dsimp only
  let H := m / b ^ ((k + 1) / 2)
  let P := b ^ ((k + 1) / 2)
  let C := palindromicHalfCopy b m
  let z : ℚ := if r = 0 then 1 else 0
  let w : ℚ := if C ≤ m ∧ C ≡ r [MOD q] then 1 else 0
  have hz (e : ℕ) : (if mirror b e 0 ≡ r [MOD q] then (1 : ℚ) else 0) = z := by
    simp [z, mirror_eq, Nat.ModEq, Nat.mod_eq_of_lt hr, eq_comm]
  have hsum (e : ℕ) := sum_range_eq_filter_Ioc (cutoff b e m) (fun x => mirror b e x ≡ r [MOD q])
  have hactive := active_cutoff hb hk
  change mirror b ((k + 1) % 2) H = C ∧ cutoff b ((k + 1) % 2) m + 1 = H + _ at hactive
  have hinactive := inactive_cutoff hb hk
  have hactiveSum :
      (∑ x ∈ range (cutoff b ((k + 1) % 2) m + 1),
        if mirror b ((k + 1) % 2) x ≡ r [MOD q] then (1 : ℚ) else 0) =
        (∑ x ∈ range H, if mirror b ((k + 1) % 2) x ≡ r [MOD q] then (1 : ℚ) else 0) + w := by
    rw [hactive.2]
    by_cases hc : C ≤ m
    · simp only [C, hc, ite_true, sum_range_succ, hactive.1, true_and, w]
    · simp [C, hc, w]
  have he (n : ℕ) :
      (∑ x ∈ range n, if mirror b 0 x ≡ r [MOD q] then (1 : ℚ) else 0) = doubledPrefix q r n := by
    simp only [doubledPrefix, residueIndicator_eq, Int.natCast_modEq_iff]
    exact sum_congr rfl fun x _ => by
      simp only [show (mirror b 0 x ≡ r [MOD q]) ↔ (2 * x ≡ r [MOD q]) from
        ⟨(mirror_zero_modEq hb hbq x).symm.trans, (mirror_zero_modEq hb hbq x).trans⟩]
  have ho (n : ℕ) :
      (∑ x ∈ range n, if mirror b 1 x ≡ r [MOD q] then (1 : ℚ) else 0) =
        centeredPrefix b q r n := by
    simp only [centeredPrefix, residueIndicator_eq, Int.natCast_modEq_iff]
    exact sum_congr rfl fun x _ => by
      simp only [show (mirror b 1 x ≡ r [MOD q]) ↔ (2 * (x / b) + x % b ≡ r [MOD q]) from
        ⟨(mirror_center_modEq hb hbq x).symm.trans, (mirror_center_modEq hb hbq x).trans⟩]
  have hsub : (if r = 0 then (2 : ℚ) else 0) = z + z := by
    by_cases hr' : r = 0 <;> norm_num [z, hr']
  rw [count_split_card hb, Nat.cast_add, hsub]
  change _ = doubledPrefix q r (if Odd k then H else P) +
    centeredPrefix b q r (if Odd k then P else H) - (z + z) + w
  by_cases hodd : Odd k
  · have hp := Nat.odd_iff.mp hodd
    have hp' : (k + 1) % 2 = 0 := by omega
    simp only [hodd, ite_true]
    rw [hp', hsum, hz, he] at hactiveSum
    rw [hp] at hinactive
    have J := hsum 1
    rw [hinactive, ho, hz] at J
    linarith
  · have hp := Nat.even_iff.mp (Nat.not_odd_iff_even.mp hodd)
    have hp' : (k + 1) % 2 = 1 := by omega
    simp only [hodd, ite_false]
    rw [hp', hsum, hz, ho] at hactiveSum
    rw [hp] at hinactive
    have J := hsum 0
    rw [hinactive, he, hz] at J
    linarith

private theorem doubledPrefix_one {q r : ℕ} (hr : r < q) :
    doubledPrefix q r 1 = if r = 0 then 1 else 0 := by
  unfold doubledPrefix
  rw [show (1 : ℕ) = 0 + 1 from rfl, sum_range_succ]
  simp only [range_zero, sum_empty, zero_add, mul_zero, residueIndicator_eq,
    Int.natCast_modEq_iff,
    Nat.ModEq, Nat.zero_mod, Nat.mod_eq_of_lt hr, eq_comm]

private theorem doubledPrefix_pow_odd {b q r : ℕ} (hb : 2 ≤ b) (hr : r < q) (hq : Odd q)
    (hbq : b ≡ 1 [MOD q]) (j : ℕ) :
    doubledPrefix q r (b ^ j) = ((b : ℚ) ^ j - 1) / q + if r = 0 then 1 else 0 := by
  rw [doubledPrefix_odd hq, residuePrefix_pow hb (by omega) hbq]
  congr 1
  simpa [residuePrefix] using (doubledPrefix_odd hq r 1).symm.trans (doubledPrefix_one hr)

private theorem exact_halfModulus {q : ℕ} (hq : 0 < q) (hqe : Even q) (x : ℚ) :
    x / ((q / 2 : ℕ) : ℚ) = 2 * x / q := by
  have hpar := Nat.even_iff.mp hqe
  have h : ((q / 2 : ℕ) : ℚ) * 2 = q := by exact_mod_cast (show q / 2 * 2 = q by omega)
  have hne : (q : ℚ) ≠ 0 := by positivity
  have hd : ((q / 2 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (show q / 2 ≠ 0 by omega)
  apply (div_eq_div_iff hd hne).2
  rw [← h]
  ring

private theorem doubledPrefix_pow_even_even {b q r : ℕ} (hb : 2 ≤ b) (hr : r < q)
    (hq : Even q) (hre : Even r) (hbq : b ≡ 1 [MOD q]) (j : ℕ) :
    doubledPrefix q r (b ^ j) = 2 * ((b : ℚ) ^ j - 1) / q + if r = 0 then 1 else 0 := by
  have hpar := Nat.even_iff.mp hq
  have hd : q / 2 ∣ q := ⟨2, by omega⟩
  have hq' : 0 < q / 2 := by omega
  rw [doubledPrefix_even_even hq hre, residuePrefix_pow hb hq' (hbq.of_dvd hd),
    exact_halfModulus (by omega) hq]
  have h0 : residueIndicator (q / 2) ((r / 2 : ℕ) : ℤ) 0 = if r = 0 then 1 else 0 := by
    simpa [residuePrefix] using (doubledPrefix_even_even hq hre 1).symm.trans (doubledPrefix_one hr)
  rw [h0]

private theorem weightedPrefix_succ (b n : ℕ) (a : ℕ → ℕ) :
    (∑ i ∈ range (n + 1), a i * b ^ (n - i)) =
      b * (∑ i ∈ range n, a i * b ^ (n - i - 1)) + a n := by
  rw [sum_range_succ, mul_sum, Nat.sub_self, pow_zero, mul_one]
  congr 1
  apply sum_congr rfl
  intro i hi
  have := mem_range.mp hi
  have he : n - i = n - i - 1 + 1 := by omega
  rw (occs := .pos [1]) [he, pow_succ]
  ac_rfl

private theorem weightedPrefix_modEq {b q : ℕ} (hbq : b ≡ 1 [MOD q]) (a : ℕ → ℕ)
    (n : ℕ) (w : ℕ → ℕ) : (∑ i ∈ range n, a i * b ^ w i) ≡ ∑ i ∈ range n, a i [MOD q] :=
  Nat.ModEq.sum fun i _ => modEq_weightedDigit hbq (a i) (w i)

private theorem shiftedWeightedBlocks_odd {b q r n : ℕ} (hq : Odd q) (hbq : b ≡ 1 [MOD q])
    (a w : ℕ → ℕ) :
    doubledPrefix q r (∑ j ∈ range n, a j * b ^ w j) =
      ∑ j ∈ range n, ((((a j * b ^ w j) / q : ℕ) : ℚ) +
        (if ((((q + 1) / 2 * r : ℕ) : ℤ) - ∑ i ∈ range j, (a i : ℤ)) % q <
          ((a j % q : ℕ) : ℤ) then 1 else 0)) := by
  rw [doubledPrefix_odd hq, residuePrefix_blocks _ _ a
    (fun j _ => modEq_weightedDigit hbq (a j) (w j))]
  apply sum_congr rfl
  intro j _
  have hq' := Nat.odd_iff.mp hq
  exact residuePrefix_weightedDigit (by omega) hbq _ _ _

private theorem shiftedWeightedBlocks_even_even {b q r n : ℕ} (hq : Even q) (hr : Even r)
    (hq' : 0 < q) (hbq : b ≡ 1 [MOD q]) (a w : ℕ → ℕ) :
    doubledPrefix q r (∑ j ∈ range n, a j * b ^ w j) =
      ∑ j ∈ range n, ((2 * (a j : ℚ) * b ^ w j - 2 * (a j % (q / 2) : ℕ)) / q +
        (if ((((r / 2 : ℕ) : ℤ) - ∑ i ∈ range j, (a i : ℤ)) % (q / 2 : ℕ)) <
          ((a j % (q / 2) : ℕ) : ℤ) then 1 else 0)) := by
  have hpar := Nat.even_iff.mp hq
  have hd : q / 2 ∣ q := ⟨2, by omega⟩
  have hbq' := hbq.of_dvd hd
  rw [doubledPrefix_even_even hq hr, residuePrefix_blocks _ _ a
    (fun j _ => modEq_weightedDigit hbq' (a j) (w j))]
  apply sum_congr rfl
  intro j _
  rw [residuePrefix_weightedDigit_exact (by omega) hbq', exact_halfModulus hq' hq]
  congr 1
  ring

private theorem centeredIndicator {b q r n : ℕ} (hbq : b ≡ 1 [MOD q]) (u : ℕ)
    (a : ℕ → ℕ) (hu : u = ∑ j ∈ range n, a j * b ^ (n - j - 1)) :
    (2 * u + a n ≡ r [MOD q]) ↔
      ((r : ℤ) - 2 * ∑ i ∈ range n, (a i : ℤ)) % q = ((a n % q : ℕ) : ℤ) := by
  have h := (weightedPrefix_modEq hbq a n (fun i => n - i - 1))
  rw [← hu] at h
  rw [← Int.natCast_modEq_iff, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Int.natCast_emod]
  have hz := Int.natCast_modEq_iff.mpr h
  push_cast at hz
  have hc := (hz.mul_left 2).add_right (a n : ℤ)
  rw [show (2 * (u : ℤ) + a n ≡ r [ZMOD q]) ↔
      (2 * ∑ i ∈ range n, (a i : ℤ) + a n ≡ r [ZMOD q]) from ⟨hc.symm.trans, hc.trans⟩]
  let S : ℤ := 2 * ∑ i ∈ range n, (a i : ℤ)
  change (S + a n ≡ r [ZMOD q]) ↔ (r - S ≡ a n [ZMOD q])
  have hSr : S + ((r : ℤ) - S) = r := by ring
  constructor
  · intro h
    rw [← hSr] at h
    exact (Int.ModEq.add_left_cancel' S h).symm
  · intro h
    simpa only [hSr] using h.symm.add_left S

-- Moving one place to the left multiplies a block by `b`. The added contribution from
-- the `b - 1` complete residues is divisible by `q`, so it passes through the floor.
private theorem weightedBlock_add_center_odd {b q : ℕ} (hb : 2 ≤ b) (hq : 0 < q)
    (hbq : b ≡ 1 [MOD q]) (a j : ℕ) :
    ((b : ℚ) - 1) * ((a : ℚ) * b ^ j) / q + (((a * b ^ j) / q : ℕ) : ℚ) =
      (((a * b ^ (j + 1)) / q : ℕ) : ℚ) := by
  have hd := (Nat.modEq_iff_dvd' (by omega : 1 ≤ b)).mp hbq.symm
  have he : q ∣ (b - 1) * (a * b ^ j) := dvd_mul_of_dvd_left hd _
  have hsum : (b - 1) * (a * b ^ j) + a * b ^ j = a * b ^ (j + 1) := by
    rw [← Nat.add_one_mul, Nat.sub_add_cancel (by omega : 1 ≤ b), pow_succ]
    ac_rfl
  rw [← hsum, add_comm ((b - 1) * (a * b ^ j)), Nat.add_div_of_dvd_left he, Nat.cast_add,
    add_comm (↑(a * b ^ j / q) : ℚ), add_left_inj, eq_comm,
    eq_div_iff (by positivity : (q : ℚ) ≠ 0)]
  have H := congrArg (fun x : ℕ => (x : ℚ)) (Nat.div_mul_cancel he)
  push_cast [Nat.cast_sub (by omega : 1 ≤ b)] at H
  exact H

private theorem weightedPrefix_const_mul {b q : ℕ} (c : ℚ) (a w : ℕ → ℕ) (n : ℕ) :
    c * ((∑ j ∈ range n, a j * b ^ w j : ℕ) : ℚ) / q =
      ∑ j ∈ range n, c * ((a j : ℚ) * b ^ w j) / q := by
  push_cast
  simp only [div_eq_mul_inv, mul_sum, sum_mul]

private theorem centeredPrefix_pow {b q : ℕ} (hb : 2 ≤ b) (hq : 0 < q) (hbq : b ≡ 1 [MOD q])
    (r n : ℕ) : centeredPrefix b q r (b ^ (n + 1)) =
      ((b : ℚ) - 1) * (b : ℚ) ^ n / q + doubledPrefix q r (b ^ n) := by
  rw [pow_succ', ← Nat.add_zero (b * b ^ n), centeredPrefix_eq hb hq hbq r _ 0 (by omega)]
  simp [residuePrefix]

private theorem centeredPrefix_weighted_odd {b q r n : ℕ} (hb : 2 ≤ b) (hq : Odd q)
    (hq' : 0 < q) (hbq : b ≡ 1 [MOD q]) (a : ℕ → ℕ) (ha : a n ≤ b) :
    let u := ∑ j ∈ range n, a j * b ^ (n - j - 1)
    centeredPrefix b q r (b * u + a n) =
      (∑ j ∈ range n, ((((a j * b ^ (n - j)) / q : ℕ) : ℚ) +
        (if ((((q + 1) / 2 * r : ℕ) : ℤ) - ∑ i ∈ range j, (a i : ℤ)) % q <
          ((a j % q : ℕ) : ℤ) then 1 else 0))) +
      residuePrefix q ((r : ℤ) - 2 * u) (a n) := by
  dsimp only
  rw [centeredPrefix_eq hb hq' hbq r _ _ ha, shiftedWeightedBlocks_odd hq hbq,
    weightedPrefix_const_mul, ← sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro j hj
  have hj' := mem_range.mp hj
  rw [← add_assoc, weightedBlock_add_center_odd hb hq' hbq,
    show n - j - 1 + 1 = n - j by omega]

private theorem centeredPrefix_weighted_even_odd {b q r n : ℕ} (hb : 2 ≤ b) (hq : Even q)
    (hr : Odd r) (hq' : 0 < q) (hbq : b ≡ 1 [MOD q]) (a : ℕ → ℕ) (ha : a n ≤ b) :
    let u := ∑ j ∈ range n, a j * b ^ (n - j - 1)
    centeredPrefix b q r (b * u + a n) =
      (∑ j ∈ range n, (a j : ℚ) * ((b : ℚ) - 1) * b ^ (n - j - 1) / q) +
        residuePrefix q ((r : ℤ) - 2 * u) (a n) := by
  dsimp only
  rw [centeredPrefix_eq hb hq' hbq r _ _ ha, doubledPrefix_even_odd hq hr, add_zero,
    weightedPrefix_const_mul]
  congr 1
  apply sum_congr rfl
  intro j _
  ring

private theorem centeredPrefix_weighted_even_even {b q r n : ℕ} (hb : 2 ≤ b) (hq : Even q)
    (hr : Even r) (hq' : 0 < q) (hbq : b ≡ 1 [MOD q]) (a : ℕ → ℕ) (ha : a n ≤ b) :
    let u := ∑ j ∈ range n, a j * b ^ (n - j - 1)
    centeredPrefix b q r (b * u + a n) =
      (∑ j ∈ range n, (((a j : ℚ) * ((b : ℚ) + 1) * b ^ (n - j - 1) -
          2 * (a j % (q / 2) : ℕ)) / q +
        (if ((((r / 2 : ℕ) : ℤ) - ∑ i ∈ range j, (a i : ℤ)) % (q / 2 : ℕ)) <
          ((a j % (q / 2) : ℕ) : ℤ) then 1 else 0))) +
      residuePrefix q ((r : ℤ) - 2 * u) (a n) := by
  dsimp only
  rw [centeredPrefix_eq hb hq' hbq r _ _ ha, shiftedWeightedBlocks_even_even hq hr hq' hbq,
    weightedPrefix_const_mul, ← sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro j _
  ring

private theorem modEq_iff_residual {q : ℕ} {x y r s : ℤ} (h : x ≡ y + s [ZMOD q]) :
    (x ≡ r [ZMOD q]) ↔ (r - s) % (q : ℤ) = y % (q : ℤ) := by
  have hsr : r - s + s = r := by ring
  change _ ↔ r - s ≡ y [ZMOD q]
  calc
    (x ≡ r [ZMOD q]) ↔ (y + s ≡ r [ZMOD q]) := ⟨h.symm.trans, h.trans⟩
    _ ↔ (y ≡ r - s [ZMOD q]) := by
      conv_lhs => rw [← hsr]
      exact ⟨Int.ModEq.add_right_cancel' s, fun h => h.add_right s⟩
    _ ↔ _ := Int.modEq_comm

private theorem weightedPrefix_modEq_last {b q n : ℕ} (hbq : b ≡ 1 [MOD q]) (a : ℕ → ℕ) :
    ((∑ j ∈ range (n + 1), a j * b ^ (n - j) : ℕ) : ℤ) ≡
      (a n : ℤ) + ∑ i ∈ range n, (a i : ℤ) [ZMOD q] := by
  have h := Int.natCast_modEq_iff.mpr (weightedPrefix_modEq hbq a (n + 1) (fun j => n - j))
  simpa only [sum_range_succ, Nat.cast_add, Nat.cast_sum, add_comm (a n : ℤ)] using h

/-- **Palindromes in residue classes modulo a divisor of the base minus one.** Let $b \ge 2$,
$m \ge 1$ and $q \ge 1$ be natural numbers with $b \equiv 1 \pmod q$, and let $r$ be a natural
number with $r < q$. Write $m = (a_k a_{k-1} \cdots a_0)_b$ in base $b$. Write $A_b(m, q, r)$ for
the number of base-$b$ palindromes $n$ with $1 \le n \le m$ and $n \equiv r \pmod q$, $C_b(m)$
for the palindromic half copy of $m$, $[P]$ for $1$ if $P$ holds and $0$ otherwise, and
$t \bmod d$ for the least nonnegative residue of an integer $t$ modulo a positive integer $d$.
For $j \ge 0$ define integers $s_j$ and $r_j$ as follows. If $q$ is even and $2j \ne k$, let
$s_j = a_{k-j} \bmod (q/2)$ and
$r_j = \bigl(\lfloor r/2 \rfloor - \sum_{i=0}^{j-1} a_{k-i}\bigr) \bmod (q/2)$. If $q$ is odd
and $2j \ne k$, let $s_j = a_{k-j} \bmod q$ and
$r_j = \bigl(\frac{q+1}{2} r - \sum_{i=0}^{j-1} a_{k-i}\bigr) \bmod q$. If $2j = k$, let
$s_j = a_{k-j} \bmod q$ and $r_j = \bigl(r - 2 \sum_{i=0}^{k/2-1} a_{k-i}\bigr) \bmod q$. Put
$\delta = [C_b(m) \le m] \, [r_{\lfloor k/2 \rfloor} = s_{\lfloor k/2 \rfloor}]$ and

$$m_1^* = \sum_{j=0}^{\lfloor (k-1)/2 \rfloor}
\left( \frac{2 a_{k-j} b^{\lfloor (k-1)/2 \rfloor - j} - 2 s_j}{q} + [r_j < s_j] \right),$$

$$m_2^* = \sum_{j=0}^{\lfloor k/2 \rfloor - 1}
\frac{a_{k-j} (b - 1) b^{\lfloor k/2 \rfloor - j - 1}}{q},$$

$$m_3^* = \sum_{j=0}^{\lfloor k/2 \rfloor - 1}
\left( \frac{a_{k-j} (b + 1) b^{\lfloor k/2 \rfloor - j - 1} - 2 s_j}{q} + [r_j < s_j] \right).$$

Then, as rational numbers, if $q$ is odd,

$$A_b(m, q, r) = \frac{b^{\lfloor (k+1)/2 \rfloor} - 1}{q} +
\sum_{j=0}^{\lfloor k/2 \rfloor} \left( \left\lfloor \frac{a_{k-j} b^{\lfloor k/2 \rfloor - j}}{q}
\right\rfloor + [r_j < s_j] \right) - [r = 0] + \delta,$$

and if $q$ is even, $A_b(m, q, r)$ equals $(b - 1) b^{(k-1)/2}/q$ when $k$ and $r$ are odd,
$((b + 1) b^{(k-1)/2} - 2)/q + m_1^* - [r = 0] + \delta$ when $k$ is odd and $r$ is even,
$\lfloor a_{k/2}/q \rfloor + m_2^* + [r_{k/2} < s_{k/2}] + \delta$ when $k$ is even and $r$ is
odd, and $2(b^{k/2} - 1)/q + \lfloor a_{k/2}/q \rfloor + m_3^* - [r = 0] +
[r_{k/2} < s_{k/2}] + \delta$ when $k$ and $r$ are both even.

Source: K. Onphaeng, T. Khemaratchatakumthorn, P. N. Phunphayap and P. Pongsriiam, *Exact
Formulas for the Number of Palindromes in Certain Arithmetic Progressions*, Journal of Integer
Sequences 27 (2024), Article 24.4.8, Theorem 9. -/
public theorem palindromeAPCount_of_modEq_one {b m q r : ℕ} (hb : 2 ≤ b) (hm : 1 ≤ m)
    (hq : 1 ≤ q) (hr : r < q) (hbq : b ≡ 1 [MOD q]) :
    let a : ℕ → ℕ := fun i => (Nat.digits b m).getD i 0
    let k : ℕ := (Nat.digits b m).length - 1
    let rr : ℕ → ℤ := fun j =>
      if 2 * j = k then ((r : ℤ) - 2 * ∑ i ∈ Finset.range (k / 2), (a (k - i) : ℤ)) % q
      else if Even q then (((r / 2 : ℕ) : ℤ) - ∑ i ∈ Finset.range j, (a (k - i) : ℤ)) % (q / 2 : ℕ)
      else ((((q + 1) / 2 * r : ℕ) : ℤ) - ∑ i ∈ Finset.range j, (a (k - i) : ℤ)) % q
    let ss : ℕ → ℤ := fun j =>
      if Even q ∧ 2 * j ≠ k then ((a (k - j) % (q / 2) : ℕ) : ℤ) else ((a (k - j) % q : ℕ) : ℤ)
    let δ : ℚ :=
      (if palindromicHalfCopy b m ≤ m then 1 else 0) * (if rr (k / 2) = ss (k / 2) then 1 else 0)
    let m₁ : ℚ := ∑ j ∈ Finset.range ((k - 1) / 2 + 1),
      ((2 * (a (k - j) : ℚ) * (b : ℚ) ^ ((k - 1) / 2 - j) - 2 * (ss j : ℚ)) / q +
        (if rr j < ss j then 1 else 0))
    let m₂ : ℚ := ∑ j ∈ Finset.range (k / 2),
      (a (k - j) : ℚ) * ((b : ℚ) - 1) * (b : ℚ) ^ (k / 2 - j - 1) / q
    let m₃ : ℚ := ∑ j ∈ Finset.range (k / 2),
      (((a (k - j) : ℚ) * ((b : ℚ) + 1) * (b : ℚ) ^ (k / 2 - j - 1) - 2 * (ss j : ℚ)) / q +
        (if rr j < ss j then 1 else 0))
    (Odd q →
      (palindromeAPCount b m q r : ℚ) =
        ((b : ℚ) ^ ((k + 1) / 2) - 1) / q +
          ∑ j ∈ Finset.range (k / 2 + 1),
            ((((a (k - j) * b ^ (k / 2 - j)) / q : ℕ) : ℚ) + (if rr j < ss j then 1 else 0)) -
          (if r = 0 then 1 else 0) + δ) ∧
    (Even q →
      (palindromeAPCount b m q r : ℚ) =
        if Odd k ∧ Odd r then ((b : ℚ) - 1) * (b : ℚ) ^ ((k - 1) / 2) / q
        else if Odd k then
          (((b : ℚ) + 1) * (b : ℚ) ^ ((k - 1) / 2) - 2) / q + m₁ - (if r = 0 then 1 else 0) + δ
        else if Odd r then
          ((a (k / 2) / q : ℕ) : ℚ) + m₂ + (if rr (k / 2) < ss (k / 2) then 1 else 0) + δ
        else
          2 * ((b : ℚ) ^ (k / 2) - 1) / q + ((a (k / 2) / q : ℕ) : ℚ) + m₃ -
            (if r = 0 then 1 else 0) + (if rr (k / 2) < ss (k / 2) then 1 else 0) + δ) := by
  dsimp only
  let k := (b.digits m).length - 1
  let n := k / 2
  let a (j : ℕ) := (b.digits m).getD (k - j) 0
  let P := b ^ ((k + 1) / 2)
  let H := m / P
  let U := ∑ j ∈ range n, a j * b ^ (n - j - 1)
  let C := palindromicHalfCopy b m
  let z : ℚ := if r = 0 then 1 else 0
  let w : ℚ := if C ≤ m ∧ C ≡ r [MOD q] then 1 else 0
  have hlen : (b.digits m).length = k + 1 := by
    have hpos := List.length_pos_iff.mpr ((Nat.digits_ne_nil_iff_ne_zero (b := b)).mpr
      (show m ≠ 0 by omega))
    dsimp [k]
    omega
  have hH : H = ∑ j ∈ range (n + 1), a j * b ^ (n - j) := prefix_as_sum hb hlen
  have hHu : H = b * U + a n := hH.trans (weightedPrefix_succ b n a)
  have ha : a n < b := by
    dsimp [a]
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact Nat.digits_lt_base hb (List.getElem_mem _)
  have hUb : H / b = U := by
    rw [hHu, Nat.mul_add_div (by omega), Nat.div_eq_of_lt ha, add_zero]
  have hCb : H % b = a n := by rw [hHu, Nat.mul_add_mod, Nat.mod_eq_of_lt ha]
  have hC := (active_cutoff hb hlen).1.symm
  change C = mirror b ((k + 1) % 2) H at hC
  have hcount := count_mirrorPrefixes hb hlen hr hbq
  change (palindromeAPCount b m q r : ℚ) =
    doubledPrefix q r (if Odd k then H else P) + centeredPrefix b q r (if Odd k then P else H) -
      (if r = 0 then 2 else 0) + w at hcount
  have hz : (if r = 0 then (2 : ℚ) else 0) = z + z := by
    by_cases hr0 : r = 0 <;> norm_num [hr0, z]
  rw [hz] at hcount
  have hq' : 0 < q := by omega
  let rc := ((r : ℤ) - 2 * ∑ i ∈ range n, (a i : ℤ)) % q
  let sc := ((a n % q : ℕ) : ℤ)
  let rr (j : ℕ) : ℤ :=
    if 2 * j = k then rc
    else if Even q then (((r / 2 : ℕ) : ℤ) - ∑ i ∈ range j, (a i : ℤ)) % (q / 2 : ℕ)
    else ((((q + 1) / 2 * r : ℕ) : ℤ) - ∑ i ∈ range j, (a i : ℤ)) % q
  let ss (j : ℕ) : ℤ :=
    if Even q ∧ 2 * j ≠ k then ((a j % (q / 2) : ℕ) : ℤ) else ((a j % q : ℕ) : ℤ)
  let δ : ℚ := (if C ≤ m then 1 else 0) * (if rr n = ss n then 1 else 0)
  let mid := (b.digits m).getD n 0
  change (Odd q →
    (palindromeAPCount b m q r : ℚ) = ((b : ℚ) ^ ((k + 1) / 2) - 1) / q +
      (∑ j ∈ range (n + 1), ((((a j * b ^ (n - j)) / q : ℕ) : ℚ) +
        (if rr j < ss j then 1 else 0))) - z + δ) ∧
    (Even q → (palindromeAPCount b m q r : ℚ) =
      if Odd k ∧ Odd r then ((b : ℚ) - 1) * (b : ℚ) ^ ((k - 1) / 2) / q
      else if Odd k then (((b : ℚ) + 1) * (b : ℚ) ^ ((k - 1) / 2) - 2) / q +
        (∑ j ∈ range ((k - 1) / 2 + 1),
          ((2 * (a j : ℚ) * (b : ℚ) ^ ((k - 1) / 2 - j) - 2 * (ss j : ℚ)) / q +
            (if rr j < ss j then 1 else 0))) - z + δ
      else if Odd r then ((mid / q : ℕ) : ℚ) +
        (∑ j ∈ range n, (a j : ℚ) * ((b : ℚ) - 1) * (b : ℚ) ^ (n - j - 1) / q) +
        (if rr n < ss n then 1 else 0) + δ
      else 2 * ((b : ℚ) ^ n - 1) / q + ((mid / q : ℕ) : ℚ) +
        (∑ j ∈ range n, (((a j : ℚ) * ((b : ℚ) + 1) * (b : ℚ) ^ (n - j - 1) - 2 * (ss j : ℚ)) / q +
          (if rr j < ss j then 1 else 0))) - z + (if rr n < ss n then 1 else 0) + δ)
  have hcenter : residuePrefix q ((r : ℤ) - 2 * U) (a n) =
      (((a n / q : ℕ) : ℚ) + if rc < sc then 1 else 0) := by
    have hu := Int.natCast_modEq_iff.mpr (weightedPrefix_modEq hbq a n (fun j => n - j - 1))
    change ((U : ℕ) : ℤ) ≡ ↑(∑ j ∈ range n, a j) [ZMOD q] at hu
    push_cast at hu
    have he := (Int.ModEq.refl (r : ℤ)).sub (hu.mul_left 2)
    unfold residuePrefix
    rw [sum_residueIndicator_range _ hq']
    simp only [rc, sc, Int.ModEq] at he ⊢
    rw [he]
  by_cases hk : Odd k
  · have hk' := Nat.odd_iff.mp hk
    have hp : P = b ^ (n + 1) := by dsimp [P, n]; congr 1; omega
    have hkn : (k - 1) / 2 = n := by dsimp [n]; omega
    have hkp : ((k + 1) / 2) = n + 1 := by dsimp [n]; omega
    have hne (j : ℕ) : 2 * j ≠ k := by omega
    have hmr : C ≡ 2 * H [MOD q] := by
      rw [hC, show (k + 1) % 2 = 0 by omega]
      exact mirror_zero_modEq hb hbq H
    simp only [hk, ite_true] at hcount
    rw [hp, centeredPrefix_pow hb hq' hbq] at hcount
    constructor
    · intro hqo
      have hqe : ¬ Even q := (Nat.not_even_iff_odd.mpr hqo)
      have hEnd : (C ≡ r [MOD q]) ↔
          ((((q + 1) / 2 * r : ℕ) : ℤ) - ∑ i ∈ range n, (a i : ℤ)) % q = sc := by
        rw [show (C ≡ r [MOD q]) ↔ (2 * H ≡ r [MOD q]) from ⟨hmr.symm.trans, hmr.trans⟩,
          double_iff hqo, ← Int.natCast_modEq_iff]
        have hd := weightedPrefix_modEq_last hbq (n := n) a
        rw [← hH] at hd
        simpa only [sc, Int.natCast_emod] using modEq_iff_residual hd
      have hw : w = (if C ≤ m then 1 else 0) *
          (if ((((q + 1) / 2 * r : ℕ) : ℤ) - ∑ i ∈ range n, (a i : ℤ)) % q = sc
            then 1 else 0) := by
        by_cases h : C ≤ m <;> simp [w, h, hEnd]
      rw [doubledPrefix_pow_odd hb hr hqo hbq] at hcount
      have hblocks := shiftedWeightedBlocks_odd (n := n + 1) hqo hbq (r := r) a (fun j => n - j)
      rw [← hH] at hblocks
      rw [hblocks, hw] at hcount
      simp only [δ, rr, ss, hne, hqe, false_and, ite_false, hkp]
      rw [hcount, pow_succ]
      ring
    · intro hqe
      have hpar := Nat.even_iff.mp hqe
      by_cases hro : Odd r
      · have hr0 : r ≠ 0 := by have := Nat.odd_iff.mp hro; omega
        have hEnd : ¬ C ≡ r [MOD q] := fun h =>
          doubledIndicator_even_odd hqe hro (hmr.symm.trans h)
        rw [doubledPrefix_even_odd hqe hro, doubledPrefix_even_odd hqe hro] at hcount
        simpa only [hk, hro, and_self, ite_true, hkn, z, hr0, ite_false, add_zero, zero_add,
          sub_zero, w, hEnd, and_false, C] using hcount
      · have hre := Nat.not_odd_iff_even.mp hro
        have hqd : q / 2 ∣ q := ⟨2, by omega⟩
        have hbqd := hbq.of_dvd hqd
        have hEnd : (C ≡ r [MOD q]) ↔
            (((r / 2 : ℕ) : ℤ) - ∑ i ∈ range n, (a i : ℤ)) % (q / 2 : ℕ) =
              ((a n % (q / 2) : ℕ) : ℤ) := by
          rw [show (C ≡ r [MOD q]) ↔ (2 * H ≡ r [MOD q]) from ⟨hmr.symm.trans, hmr.trans⟩,
            double_iff_half_modulus hqe hre, ← Int.natCast_modEq_iff]
          have hd := weightedPrefix_modEq_last hbqd (n := n) a
          rw [← hH] at hd
          simpa only [Int.natCast_emod] using modEq_iff_residual hd
        have hw : w = (if C ≤ m then 1 else 0) *
            (if (((r / 2 : ℕ) : ℤ) - ∑ i ∈ range n, (a i : ℤ)) % (q / 2 : ℕ) =
              ((a n % (q / 2) : ℕ) : ℤ) then 1 else 0) := by
          by_cases h : C ≤ m <;> simp [w, h, hEnd]
        rw [doubledPrefix_pow_even_even hb hr hqe hre hbq] at hcount
        have hblocks :=
          shiftedWeightedBlocks_even_even (n := n + 1) hqe hre hq' hbq a (fun j => n - j)
        rw [← hH] at hblocks
        rw [hblocks, hw] at hcount
        have hss (j : ℕ) : ss j = ((a j % (q / 2) : ℕ) : ℤ) := by
          simp only [ss, ite_eq_left (And.intro hqe (hne j))]
        simp only [hk, hro, and_false, ite_false, ite_true, hkn, δ, rr, hne, hqe, hss,
          Int.cast_natCast]
        rw [hcount]
        ring
  · have hk' := Nat.even_iff.mp (Nat.not_odd_iff_even.mp hk)
    have hp : P = b ^ n := by dsimp [P, n]; congr 1; omega
    have hn : 2 * n = k := by dsimp [n]; omega
    have hne {j : ℕ} (hj : j ∈ range n) : 2 * j ≠ k := by have := mem_range.mp hj; omega
    have hmr : C ≡ 2 * U + a n [MOD q] := by
      rw [hC, show (k + 1) % 2 = 1 by omega]
      simpa only [hUb, hCb] using mirror_center_modEq hb hbq H
    have hEnd : (C ≡ r [MOD q]) ↔ rc = sc := by
      exact (show (C ≡ r [MOD q]) ↔ (2 * U + a n ≡ r [MOD q]) from
        ⟨hmr.symm.trans, hmr.trans⟩).trans (centeredIndicator hbq U a rfl)
    have hw : w = (if C ≤ m then 1 else 0) * (if rc = sc then 1 else 0) := by
      by_cases h : C ≤ m <;> simp [w, h, hEnd]
    simp only [hk, ite_false] at hcount
    rw [hp, hw] at hcount
    constructor
    · intro hqo
      have hqe : ¬ Even q := (Nat.not_even_iff_odd.mpr hqo)
      rw [doubledPrefix_pow_odd hb hr hqo hbq, hHu,
        centeredPrefix_weighted_odd hb hqo hq' hbq a ha.le, hcenter] at hcount
      simp only [show (k + 1) / 2 = n by dsimp [n]; omega, δ, rr, ss, hn, ite_true, hqe, false_and,
        ite_false]
      rw [sum_range_succ]
      simp only [hn, ite_true, Nat.sub_self, pow_zero, mul_one]
      rw [hcount]
      have hblocks :
          (∑ j ∈ range n, ((((a j * b ^ (n - j)) / q : ℕ) : ℚ) +
            (if (if 2 * j = k then rc else
                ((((q + 1) / 2 * r : ℕ) : ℤ) - ∑ i ∈ range j, (a i : ℤ)) % q) <
              ((a j % q : ℕ) : ℤ) then 1 else 0))) =
          ∑ j ∈ range n, ((((a j * b ^ (n - j)) / q : ℕ) : ℚ) +
            (if ((((q + 1) / 2 * r : ℕ) : ℤ) - ∑ i ∈ range j, (a i : ℤ)) % q <
              ((a j % q : ℕ) : ℤ) then 1 else 0)) := by
        exact sum_congr rfl fun j hj => by simp only [hne hj, ite_false]
      rw [hblocks]
      ring
    · intro hqe
      have hmid : mid = a n := by
        dsimp only [mid, a]
        rw [show k - n = n by omega]
      rw [hmid]
      have hss : ss n = sc := ite_eq_right (fun h => h.2 hn)
      have hδ : δ = (if C ≤ m then 1 else 0) * (if rc = sc then 1 else 0) := by
        simp only [δ, rr, hss, hn, ite_true]
      have hlt : (rr n < ss n) ↔ rc < sc := by
        simp only [rr, hss, hn, ite_true]
      simp only [hk, false_and, ite_false, hδ, hlt]
      by_cases hro : Odd r
      · have hr0 : r ≠ 0 := by have := Nat.odd_iff.mp hro; omega
        rw [doubledPrefix_even_odd hqe hro, hHu,
          centeredPrefix_weighted_even_odd hb hqe hro hq' hbq a ha.le, hcenter] at hcount
        rw [ite_eq_left hro, hcount]
        simp only [z, hr0, ite_false, add_zero, sub_zero, zero_add]
        ring
      · have hre := Nat.not_odd_iff_even.mp hro
        rw [doubledPrefix_pow_even_even hb hr hqe hre hbq, hHu,
          centeredPrefix_weighted_even_even hb hqe hre hq' hbq a ha.le, hcenter] at hcount
        rw [ite_eq_right hro, hcount]
        have hblocks :
            (∑ j ∈ range n, (((a j : ℚ) * ((b : ℚ) + 1) * b ^ (n - j - 1) -
          2 * (ss j : ℚ)) / q +
              (if rr j < ss j then 1 else 0))) =
            ∑ j ∈ range n, (((a j : ℚ) * ((b : ℚ) + 1) * b ^ (n - j - 1) -
                2 * (a j % (q / 2) : ℕ)) / q +
              (if (((r / 2 : ℕ) : ℤ) - ∑ i ∈ range j, (a i : ℤ)) % (q / 2 : ℕ) <
                ((a j % (q / 2) : ℕ) : ℤ) then 1 else 0)) := by
          exact sum_congr rfl fun j hj => by
            have hs : ss j = ((a j % (q / 2) : ℕ) : ℤ) :=
              ite_eq_left ⟨hqe, hne hj⟩
            simp only [rr, hs, hne hj, ite_false, hqe, ite_true, Int.cast_natCast]
        rw [hblocks]
        ring

end MetaMathlibExt
