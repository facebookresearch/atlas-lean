/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.List.Palindrome
public import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Tactic.IntervalCases

/-!
# Palindromes in arithmetic progressions

For an odd divisor of the base minus one, `abs_palindromeAPCount_sub_le` bounds the discrepancy
between the palindrome count in a residue class and the average over all classes.

A palindrome with leading half `h` is congruent to `2 * h` for even digit length and to
`h + h / b` for odd digit length, with the central digit included in the odd leading half.
The latter sequence skips one integer at each multiple of the base. Counting the even prefixes,
the interval spanned by the odd prefixes, and its skipped values gives three interval counts.
Each has discrepancy at most one, and the skipped interval is empty below the square of the base.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Palindromes in an arithmetic progression.** For natural numbers $b$, $m$, $q$ and $r$,
$A_b(m, q, r)$ is the number of base-$b$ palindromes $n$ with $1 \le n \le m$ and
$n \equiv r \pmod q$, where a natural number is a base-$b$ palindrome when its string of base-$b$
digits reads the same in both directions.

Source: K. Onphaeng, T. Khemaratchatakumthorn, P. N. Phunphayap and P. Pongsriiam, *Exact
Formulas for the Number of Palindromes in Certain Arithmetic Progressions*, Journal of Integer
Sequences 27 (2024), Article 24.4.8, Section 1. -/
public def palindromeAPCount (b m q r : ℕ) : ℕ :=
  ((Finset.Icc 1 m).filter fun n => (Nat.digits b n).Palindrome ∧ n ≡ r [MOD q]).card

namespace abs_palindromeAPCount_sub_le

open Finset

-- With no central digit, mirror all of the prefix. With a central digit, omit it from the copy.
private def mirror (b e h : ℕ) : ℕ :=
  let ds := Nat.digits b h
  Nat.ofDigits b ((ds.drop e).reverse ++ ds)

private theorem digits_mirror {b : ℕ} (hb : 2 ≤ b) (e h : ℕ) :
    (b.digits (mirror b e h)) = ((b.digits h).drop e).reverse ++ b.digits h := by
  rcases eq_or_ne h 0 with rfl | hh
  · simp [mirror]
  apply Nat.digits_ofDigits b hb
  · intro x hx
    rcases List.mem_append.mp hx with hl | hr
    · exact Nat.digits_lt_base hb (List.mem_of_mem_drop (List.mem_reverse.mp hl))
    · exact Nat.digits_lt_base hb hr
  · intro _
    rw [List.getLast_append_of_right_ne_nil _ _ (Nat.digits_ne_nil_iff_ne_zero.mpr hh)]
    exact Nat.getLast_digit_ne_zero _ hh

private theorem mirror_palindrome {b : ℕ} (hb : 2 ≤ b) {e : ℕ} (he : e ≤ 1) (h : ℕ) :
    (b.digits (mirror b e h)).Palindrome := by
  rw [List.Palindrome.iff_reverse_eq, digits_mirror hb]
  interval_cases e
  · simp
  · cases b.digits h <;> simp [List.append_assoc]

private theorem mirror_strictMono {b : ℕ} (hb : 2 ≤ b) (e : ℕ) : StrictMono (mirror b e) := by
  intro h j hj
  let low (x : ℕ) := ((b.digits x).drop e).reverse
  have hlo (x : ℕ) : Nat.ofDigits b (low x) < b ^ (low x).length :=
    Nat.ofDigits_lt_base_pow_length hb fun _ hx =>
      Nat.digits_lt_base hb (List.mem_of_mem_drop (List.mem_reverse.mp hx))
  have hlen : (low h).length ≤ (low j).length := by
    simpa [low] using Nat.sub_le_sub_right (Nat.le_length_digits_le b h j hj.le) e
  have hp : b ^ (low h).length ≤ b ^ (low j).length := Nat.pow_le_pow_right (by omega) hlen
  change Nat.ofDigits b (low h ++ _) < Nat.ofDigits b (low j ++ _)
  simp only [Nat.ofDigits_append, Nat.ofDigits_digits]
  calc
    _ < b ^ (low h).length * (h + 1) := by
      rw [Nat.mul_succ, add_comm]
      exact Nat.add_lt_add_left (hlo h) _
    _ ≤ b ^ (low j).length * j := Nat.mul_le_mul hp hj
    _ ≤ _ := Nat.le_add_left _ _

private theorem mirror_parity {b h e : ℕ} (hb : 2 ≤ b) (hh : 0 < h) (he : e ≤ 1) :
    (b.digits (mirror b e h)).length % 2 = e := by
  have hl := List.length_pos_iff.mpr ((Nat.digits_ne_nil_iff_ne_zero (b := b)).mpr hh.ne')
  rw [digits_mirror hb]
  simp only [List.length_append, List.length_reverse, List.length_drop]
  omega

private theorem exists_mirror {b n : ℕ} (hb : 2 ≤ b) (hn : 0 < n)
    (hp : (b.digits n).Palindrome) :
    ∃ h > 0, mirror b ((b.digits n).length % 2) h = n := by
  let ds := b.digits n
  let k := ds.length / 2
  let hi := ds.drop k
  have hlen : 0 < ds.length := List.length_pos_iff.mpr (Nat.digits_ne_nil_iff_ne_zero.mpr hn.ne')
  have hhi : hi ≠ [] := List.length_pos_iff.mp (by simp [hi, k]; omega)
  have hlast : hi.getLast hhi ≠ 0 := by
    have h := Nat.getLast_digit_ne_zero b hn.ne'
    change ds.getLast _ ≠ 0 at h
    have heq : ds.take k ++ hi = ds := List.take_append_drop ..
    simpa only [← List.getLast_append_of_right_ne_nil (ds.take k) hi hhi, heq] using h
  have hd : b.digits (Nat.ofDigits b hi) = hi :=
    Nat.digits_ofDigits b hb _ (fun _ hx => Nat.digits_lt_base hb (List.mem_of_mem_drop hx))
      (fun _ => hlast)
  refine ⟨Nat.ofDigits b hi, ?_, ?_⟩
  · by_contra! hz
    simp_all
  · have hrev : (hi.drop (ds.length % 2)).reverse = ds.take k := by
      have hr := congrArg (List.take k) hp.reverse_eq
      change ds.reverse.take k = ds.take k at hr
      rw [List.take_reverse] at hr
      have hk : k + ds.length % 2 = ds.length - k := by dsimp [k]; omega
      simpa only [hi, List.drop_drop, hk] using hr
    change Nat.ofDigits b _ = n
    simp only [hd, hrev, hi, List.take_append_drop, ds, Nat.ofDigits_digits]

private def cutoff (b e m : ℕ) : ℕ :=
  Nat.findGreatest (fun h => mirror b e h ≤ m) m

private theorem le_cutoff {b e h m : ℕ} (hb : 2 ≤ b) :
    h ≤ cutoff b e m ↔ mirror b e h ≤ m := by
  have hmono := mirror_strictMono hb e
  constructor
  · intro hh
    apply (hmono.monotone hh).trans
    exact Nat.findGreatest_spec (P := fun h => mirror b e h ≤ m) (Nat.zero_le m) (by simp [mirror])
  · exact fun hn => Nat.le_findGreatest ((hmono.id_le h).trans hn) hn

private def countTo (n : ℕ) (p : ℕ → Prop) [DecidablePred p] : ℕ :=
  ((Ioc 0 n).filter p).card

private theorem countTo_succ (n : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    countTo (n + 1) p = countTo n p + if p (n + 1) then 1 else 0 := by
  simp [countTo, ← insert_Ioc_right_eq_Ioc_add_one (Nat.zero_le n), filter_insert,
    apply_ite card]
  split <;> simp_all

private theorem count_split {b : ℕ} (hb : 2 ≤ b) (m q r : ℕ) :
    palindromeAPCount b m q r =
      countTo (cutoff b 0 m) (fun h => mirror b 0 h ≡ r [MOD q]) +
      countTo (cutoff b 1 m) (fun h => mirror b 1 h ≡ r [MOD q]) := by
  let s (e : ℕ) := (Ioc 0 (cutoff b e m)).filter (fun h => mirror b e h ≡ r [MOD q])
  let t (e : ℕ) := (s e).image (mirror b e)
  have mem (e n : ℕ) : n ∈ t e ↔ ∃ h, (0 < h ∧ mirror b e h ≤ m) ∧
      mirror b e h ≡ r [MOD q] ∧ mirror b e h = n := by
    simp [t, s, le_cutoff hb, and_assoc]
  have hp (e n : ℕ) (he : e ≤ 1) (hn : n ∈ t e) :
      (1 ≤ n ∧ n ≤ m) ∧ (b.digits n).Palindrome ∧ n ≡ r [MOD q] := by
    obtain ⟨h, ⟨hh, hm⟩, hr, rfl⟩ := (mem e n).mp hn
    exact ⟨⟨hh.trans_le ((mirror_strictMono hb e).id_le h), hm⟩, mirror_palindrome hb he h, hr⟩
  have eq : (Icc 1 m).filter (fun n => (b.digits n).Palindrome ∧ n ≡ r [MOD q]) =
      t 0 ∪ t 1 := by
    ext n
    rw [mem_filter, mem_Icc, mem_union]
    refine ⟨fun ⟨⟨hn, hm⟩, hpal, hr⟩ => ?_, fun h => h.elim (hp 0 n (by decide))
      (hp 1 n (by decide))⟩
    obtain ⟨h, hh, heq⟩ := exists_mirror hb hn hpal
    have ht : n ∈ t ((b.digits n).length % 2) :=
      (mem _ _).mpr ⟨h, ⟨hh, by rw [heq]; exact hm⟩, by rw [heq]; exact hr, heq⟩
    rcases Nat.mod_two_eq_zero_or_one (b.digits n).length with H | H <;> simp_all
  have disj : Disjoint (t 0) (t 1) := by
    apply Finset.disjoint_left.mpr
    intro n h₀ h₁
    obtain ⟨h, ⟨hh, _⟩, _, heq⟩ := (mem 0 n).mp h₀
    obtain ⟨j, ⟨hj, _⟩, _, jeq⟩ := (mem 1 n).mp h₁
    have H := mirror_parity hb hh (Nat.zero_le 1)
    have J := mirror_parity hb hj (le_refl 1)
    rw [heq] at H
    rw [jeq] at J
    omega
  rw [palindromeAPCount, eq, card_union_of_disjoint disj]
  simp only [t, card_image_of_injective _ (mirror_strictMono hb _).injective]
  rfl

private theorem count_total {b : ℕ} (hb : 2 ≤ b) (m : ℕ) :
    palindromeAPCount b m 1 0 = cutoff b 0 m + cutoff b 1 m := by
  simp [count_split hb, countTo, Nat.modEq_one]

private theorem mirror_modEq {b q : ℕ} (hb : 2 ≤ b) (hbq : b ≡ 1 [MOD q]) (e h : ℕ) :
    mirror b e h ≡ h + h / b ^ e [MOD q] := by
  have digitSum (l : List ℕ) : Nat.ofDigits b l ≡ l.sum [MOD q] := by
    simpa [Nat.ofDigits_one] using Nat.ofDigits_modEq' b 1 q hbq l
  have H := digitSum (b.digits h)
  have J := digitSum ((b.digits h).drop e)
  simp only [Nat.ofDigits_digits] at H
  rw [Nat.self_div_pow_eq_ofDigits_drop e h hb]
  exact (by simpa [mirror, add_comm] using
    digitSum (((b.digits h).drop e).reverse ++ b.digits h) :
      mirror b e h ≡ (b.digits h).sum + ((b.digits h).drop e).sum [MOD q]).trans (H.add J).symm

-- Each residue occurs within one of its expected frequency in any initial interval.
private def residueCount (q r n : ℕ) := countTo n (fun x => x ≡ r [MOD q])

private theorem residue_error {q : ℕ} (hq : 0 < q) (r n : ℕ) :
    |(residueCount q r n : ℝ) - n / (q : ℝ)| ≤ 1 := by
  have hq' : 0 < (q : ℚ) := by exact_mod_cast hq
  have h := Nat.Ioc_filter_modEq_card 0 n hq r
  simp only [Nat.cast_zero, zero_sub] at h
  have hle : -(r : ℚ) / q ≤ (n - (r : ℚ)) / q := by gcongr; simp
  rw [max_eq_left (sub_nonneg.mpr (Int.floor_mono hle))] at h
  change ((residueCount q r n : ℕ) : ℤ) = _ at h
  have h' := congrArg (fun z : ℤ => (z : ℚ)) h
  push_cast at h'
  have hd : (n - (r : ℚ)) / q - - (r : ℚ) / q = n / (q : ℚ) := by ring
  have H₁ := Int.floor_le ((n - (r : ℚ)) / q)
  have H₂ := Int.lt_floor_add_one ((n - (r : ℚ)) / q)
  have H₃ := Int.floor_le (-(r : ℚ) / q)
  have H₄ := Int.lt_floor_add_one (-(r : ℚ) / q)
  have H : |(residueCount q r n : ℚ) - n / (q : ℚ)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_natCast, Rat.cast_div, Rat.cast_one] using
    (Rat.cast_le (K := ℝ)).mpr H

private theorem double_iff {q : ℕ} (hq : Odd q) (x r : ℕ) :
    2 * x ≡ r [MOD q] ↔ x ≡ ((q + 1) / 2) * r [MOD q] := by
  let u := (q + 1) / 2
  have hu : u * 2 ≡ 1 [MOD q] := by
    have h : u * 2 = 1 + q := by obtain ⟨k, hk⟩ := hq; dsimp [u]; omega
    rw [h, Nat.add_modulus_modEq_iff]
  constructor
  · intro h
    exact (by simpa [mul_assoc] using hu.symm.mul_right x :
      x ≡ u * (2 * x) [MOD q]).trans (h.mul_left u)
  · intro h
    apply (h.mul_left 2).trans
    simpa [u, mul_left_comm, mul_assoc, mul_comm] using hu.mul_right r

-- As the odd prefix h advances, h + h / b skips one value each time h crosses a multiple
-- of b. Adding one to the skipped value gives (b + 1) times the new quotient.
private theorem odd_count {b q : ℕ} (hq : Odd q) (hbq : b ≡ 1 [MOD q])
    (r n : ℕ) :
    countTo n (fun h => h + h / b ≡ r [MOD q]) +
        residueCount q (((q + 1) / 2) * (r + 1)) (n / b) =
      residueCount q r (n + n / b) := by
  induction n with
  | zero => simp [residueCount, countTo]
  | succ n ih =>
    unfold residueCount at *
    by_cases hd : b ∣ n + 1
    · have hs : (n + 1) / b = n / b + 1 := Nat.succ_div_of_dvd hd
      have he : (b + 1) * (n / b + 1) = (n + n / b + 1) + 1 := by
        have := Nat.mul_div_cancel' hd
        rw [hs] at this
        rw [add_mul, one_mul, this]
        omega
      have hstep : (n + n / b + 1 ≡ r [MOD q]) ↔
          n / b + 1 ≡ ((q + 1) / 2) * (r + 1) [MOD q] := by
        rw [← double_iff hq]
        have H : (n + n / b + 1) + 1 ≡ 2 * (n / b + 1) [MOD q] := by
          rw [← he]
          exact (hbq.add_right 1).mul_right _
        exact (Nat.ModEq.add_iff_right (Nat.ModEq.refl 1)).symm.trans
          ⟨fun h => H.symm.trans h, fun h => H.trans h⟩
      simp only [hs, show n + 1 + (n / b + 1) = n + n / b + 1 + 1 by omega, countTo_succ,
        ← hstep]
      omega
    · have hs := Nat.succ_div_of_not_dvd hd
      simp only [hs, show n + 1 + n / b = n + n / b + 1 by omega, countTo_succ]
      omega

private theorem count_identity {b q : ℕ} (hb : 2 ≤ b) (hq : Odd q) (hbq : b ≡ 1 [MOD q])
    (m r : ℕ) :
    let E := cutoff b 0 m
    let O := cutoff b 1 m
    let u := (q + 1) / 2
    palindromeAPCount b m q r + residueCount q (u * (r + 1)) (O / b) =
      residueCount q (u * r) E + residueCount q r (O + O / b) := by
  dsimp only
  rw [count_split hb, add_assoc]
  have he (h : ℕ) : mirror b 0 h ≡ r [MOD q] ↔ h ≡ ((q + 1) / 2) * r [MOD q] := by
    have H : mirror b 0 h ≡ 2 * h [MOD q] := by simpa [two_mul] using mirror_modEq hb hbq 0 h
    rw [← double_iff hq]
    exact ⟨H.symm.trans, H.trans⟩
  have ho (h : ℕ) : mirror b 1 h ≡ r [MOD q] ↔ h + h / b ≡ r [MOD q] := by
    have H : mirror b 1 h ≡ h + h / b [MOD q] := by simpa using mirror_modEq hb hbq 1 h
    exact ⟨H.symm.trans, H.trans⟩
  simpa only [residueCount, countTo, he, ho, add_right_inj] using
    congrArg (fun k => residueCount q (((q + 1) / 2) * r) (cutoff b 0 m) + k)
      (odd_count hq hbq r (cutoff b 1 m))

private theorem cutoff_lt_base {b m : ℕ} (hb : 2 ≤ b) (hm : m < b ^ 2) :
    cutoff b 1 m < b := by
  by_contra! hn
  have H := (le_cutoff hb).mp hn
  have hd : b.digits b = [0, 1] := by
    rw [Nat.digits_eq_cons_digits_div hb (by omega)]
    simp [Nat.div_self (by omega : 0 < b), Nat.digits_of_lt b 1 one_ne_zero hb]
  simp [mirror, hd, Nat.ofDigits_cons] at H
  nlinarith

end abs_palindromeAPCount_sub_le

open abs_palindromeAPCount_sub_le in
/-- **Palindromes in residue classes: a logarithmic error bound.** Let $b \ge 2$ be a natural
number, let $q$ be an odd natural number with $b \equiv 1 \pmod q$, and let $r$ be a natural
number with $r < q$. For natural numbers $m$, $q'$ and $r'$, write $A_b(m, q', r')$ for the number
of base-$b$ palindromes $n$ with $1 \le n \le m$ and $n \equiv r' \pmod{q'}$; thus $A_b(m, 1, 0)$
is the number of all base-$b$ palindromes in $[1, m]$. Then for every natural number $m \ge 1$,

$$\left| A_b(m, q, r) - \frac{A_b(m, 1, 0)}{q} \right| \le \frac{\log m}{2 \log b} + 2,$$

where $\log$ is the natural logarithm.

Source: K. Onphaeng, T. Khemaratchatakumthorn, P. N. Phunphayap and P. Pongsriiam, *Exact
Formulas for the Number of Palindromes in Certain Arithmetic Progressions*, Journal of Integer
Sequences 27 (2024), Article 24.4.8, Corollary 12. -/
public theorem abs_palindromeAPCount_sub_le {b q r : ℕ} (hb : 2 ≤ b) (hq : Odd q)
    (hr : r < q) (hbq : b ≡ 1 [MOD q]) {m : ℕ} (hm : 1 ≤ m) :
    |(palindromeAPCount b m q r : ℝ) - (palindromeAPCount b m 1 0 : ℝ) / q| ≤
      Real.log m / (2 * Real.log b) + 2 := by
  let E := cutoff b 0 m
  let O := cutoff b 1 m
  let u := (q + 1) / 2
  let t := O / b
  have hpos : 0 < q := by omega
  have h₁ := abs_le.mp (residue_error hpos (u * r) E)
  have h₂ := abs_le.mp (residue_error hpos r (O + t))
  have h₃ := abs_le.mp (residue_error hpos (u * (r + 1)) t)
  have hid : (palindromeAPCount b m q r : ℝ) + residueCount q (u * (r + 1)) t =
      residueCount q (u * r) E + residueCount q r (O + t) := by
    exact_mod_cast count_identity hb hq hbq m r
  rw [count_total hb]
  change |(palindromeAPCount b m q r : ℝ) - ((E + O : ℕ) : ℝ) / q| ≤ _
  push_cast at h₂ ⊢
  rw [add_div] at h₂ ⊢
  have hlog : 0 < Real.log b := Real.log_pos (by exact_mod_cast hb)
  by_cases hm' : m < b ^ 2
  · have ht : t = 0 := Nat.div_eq_of_lt (cutoff_lt_base hb hm')
    have hz : residueCount q (u * (r + 1)) 0 = 0 := by simp [residueCount, countTo]
    simp only [ht, hz, Nat.cast_zero, add_zero] at hid
    have hnonneg : 0 ≤ Real.log m / (2 * Real.log b) :=
      div_nonneg (Real.log_nonneg (by exact_mod_cast hm)) (by positivity)
    rw [ht] at h₂
    simp only [Nat.cast_zero, zero_div, add_zero] at h₂
    rw [abs_le]
    constructor <;> linarith
  · have hlog₂ := Real.log_le_log (by positivity : 0 < (b : ℝ) ^ 2)
        (show (b : ℝ) ^ 2 ≤ m by exact_mod_cast (Nat.le_of_not_gt hm'))
    rw [Real.log_pow] at hlog₂
    have hratio : 1 ≤ Real.log m / (2 * Real.log b) := by
      rw [le_div_iff₀ (by positivity)]
      norm_num at hlog₂ ⊢
      exact hlog₂
    rw [abs_le]
    constructor <;> linarith

end

end MetaMathlibExt
