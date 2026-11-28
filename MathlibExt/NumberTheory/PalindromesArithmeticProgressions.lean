/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.List.Palindrome
public import Mathlib.Data.Nat.Count
public import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Tactic.IntervalCases
import MathlibExt.Data.Nat.Digits.Div

/-!
# Palindromes in arithmetic progressions

For an odd divisor of the base minus one, `abs_palindromeAPCount_sub_le` bounds the discrepancy
between the palindrome count in a residue class and the average over all classes.

A palindrome with leading half `h` is congruent to `2 * h` for even digit length and to
`h + h / b` for odd digit length, with the central digit included in the odd leading half.
The latter sequence skips one integer at each multiple of the base. Counting the even prefixes,
the interval spanned by the odd prefixes, and its skipped values gives three interval counts.
Each has discrepancy at most one, and the skipped interval is empty below the square of the base.

## References

* Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Phakhinkon Napp Phunphayap and
  Prapanpong Pongsriiam, *Exact Formulas for the Number of Palindromes in Certain Arithmetic
  Progressions*, Journal of Integer Sequences 27 (2024), Article 24.4.8, pp. 1–29,
  Section 1, Lemma 2(ii), and Corollaries 11 and 12.
-/

/-- For odd `q`, a natural number `x` satisfies `2 * x ≡ r [MOD q]` exactly when
`x ≡ ((q + 1) / 2) * r [MOD q]`. -/
public theorem Nat.two_mul_modEq_iff_of_odd {q : ℕ} (hq : Odd q) (x r : ℕ) :
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

-- As the odd prefix h advances, h + h / b skips one value each time h crosses a multiple
-- of b. Adding one to the skipped value gives (b + 1) times the new quotient.
private theorem odd_count_with_skips {b q : ℕ} (hbq : b ≡ 1 [MOD q]) (r n : ℕ) :
    countTo n (fun h => h + h / b ≡ r [MOD q]) +
        countTo (n / b) (fun u => 2 * u ≡ r + 1 [MOD q]) =
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
      have hstep : (n + n / b + 1 ≡ r [MOD q]) ↔ 2 * (n / b + 1) ≡ r + 1 [MOD q] := by
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

private theorem odd_count {b q : ℕ} (hq : Odd q) (hbq : b ≡ 1 [MOD q]) (r n : ℕ) :
    countTo n (fun h => h + h / b ≡ r [MOD q]) +
        residueCount q (((q + 1) / 2) * (r + 1)) (n / b) =
      residueCount q r (n + n / b) := by
  simpa only [Nat.two_mul_modEq_iff_of_odd hq, residueCount] using odd_count_with_skips hbq r n

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
    rw [← Nat.two_mul_modEq_iff_of_odd hq]
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

private theorem cutoff_base_pow {b k e : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k) (he : e ≤ 1) :
    cutoff b e (b ^ k) = b ^ ((k + e) / 2) - 1 := by
  have hendpoint : ¬ (b.digits (b ^ k)).Palindrome := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have hd : b.digits (b ^ (j + 1)) = List.replicate (j + 1) 0 ++ [1] := by
      simpa only [mul_one, Nat.digits_of_lt b 1 one_ne_zero hb] using
        Nat.digits_base_pow_mul (k := j + 1) hb Nat.zero_lt_one
    intro hp
    have H := congrArg List.head? hp.reverse_eq
    simp [hd, List.replicate_succ] at H
  have hlen (n : ℕ) (hn : n ≠ 0) (i : ℕ) : n < b ^ i ↔ (b.digits n).length ≤ i := by
    rw [Nat.length_digits b n hb hn, ← Nat.log_lt_iff_lt_pow hb hn]
    omega
  have hcut (h : ℕ) : h ≤ cutoff b e (b ^ k) ↔ h ≤ b ^ ((k + e) / 2) - 1 := by
    rw [le_cutoff hb]
    rcases eq_or_ne h 0 with rfl | hh
    · simp [mirror]
    have hhpos : 0 < h := Nat.pos_of_ne_zero hh
    have hmpos : 0 < mirror b e h := hhpos.trans_le ((mirror_strictMono hb e).id_le h)
    have hmne : mirror b e h ≠ b ^ k := fun H => hendpoint (H ▸ mirror_palindrome hb he h)
    have hp : 0 < b ^ ((k + e) / 2) := by positivity
    have hd := List.length_pos_iff.mpr ((Nat.digits_ne_nil_iff_ne_zero (b := b)).mpr hh)
    rw [le_iff_lt_or_eq, or_iff_left hmne,
      show h ≤ b ^ ((k + e) / 2) - 1 ↔ h < b ^ ((k + e) / 2) by omega,
      hlen _ hmpos.ne', hlen _ hh, digits_mirror hb]
    simp only [List.length_append, List.length_reverse, List.length_drop]
    omega
  exact le_antisymm ((hcut _).mp le_rfl) ((hcut _).mpr le_rfl)

-- The lower mirrored digits occupy strictly less than one unit of the leading half.
private theorem mirror_bounds {b : ℕ} (hb : 2 ≤ b) (e x : ℕ) :
    b ^ ((b.digits x).length - e) * x ≤ mirror b e x ∧
      mirror b e x < b ^ ((b.digits x).length - e) * (x + 1) := by
  let low := ((b.digits x).drop e).reverse
  have hl : low.length = (b.digits x).length - e := by simp [low]
  have hlt : Nat.ofDigits b low < b ^ low.length :=
    Nat.ofDigits_lt_base_pow_length hb fun _ hi =>
      Nat.digits_lt_base hb (List.mem_of_mem_drop (List.mem_reverse.mp hi))
  rw [← hl, mirror]
  change _ ≤ Nat.ofDigits b (low ++ b.digits x) ∧ Nat.ofDigits b (low ++ b.digits x) < _
  rw [Nat.ofDigits_append, Nat.ofDigits_digits, Nat.mul_succ]
  exact ⟨Nat.le_add_left _ _, by omega⟩

private theorem active_cutoff {b m k : ℕ} (hb : 2 ≤ b) (hk : (b.digits m).length = k + 1) :
    let H := m / b ^ ((k + 1) / 2)
    let e := (k + 1) % 2
    cutoff b e m + 1 = H + (if mirror b e H ≤ m then 1 else 0) := by
  dsimp only
  let t := (k + 1) / 2
  let e := (k + 1) % 2
  let H := m / b ^ t
  have hlen : (b.digits H).length - e = t := by
    simp only [H, Nat.digits_div_pow hb, List.length_drop, hk, e, t]
    omega
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
  change cutoff b e m + 1 = H + (if mirror b e H ≤ m then 1 else 0)
  have hup : cutoff b e m ≤ H := by
    by_contra! h
    exact above _ h le_rfl
  by_cases h : mirror b e H ≤ m
  · have hd : H ≤ cutoff b e m := (le_cutoff hb).mpr h
    simp [h, le_antisymm hup hd]
  · have hne : ¬ H ≤ cutoff b e m := by rwa [le_cutoff hb]
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

private theorem count_mirror_range (n : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    Nat.count p (n + 1) = countTo n p + if p 0 then 1 else 0 := by
  have h : range (n + 1) = insert 0 (Ioc 0 n) := by
    ext x
    simp only [mem_range, mem_insert, mem_Ioc]
    omega
  rw [Nat.count_eq_card_filter_range, h, filter_insert]
  by_cases hp : p 0 <;> simp [hp, countTo]

end abs_palindromeAPCount_sub_le

open abs_palindromeAPCount_sub_le in
/-- **Counting palindromes by filling the gaps in odd-length prefixes.** Let $b$, $k$, $q$, and $r$
be natural numbers with $b \ge 2$, $k \ge 1$, and $b \equiv 1 \pmod q$. Write $A_b(b^k,q,r)$ for the
count of positive base-$b$ palindromes up to $b^k$ congruent to $r$ modulo $q$. Put
$S = b^{\lfloor k/2 \rfloor}$ and $T = b^{\lfloor (k-1)/2 \rfloor}$. Let $C(N,c,a)$ count integers
$h$ with $1 \le h \le N$ and $ch \equiv a \pmod q$. Then

$$
A_b(b^k,q,r) + C(T-1,2,r+1) = C(S-1,2,r) + C((b+1)T-2,1,r).
$$

The even-length prefixes range from $1$ to $S-1$ and give the residues $2h$. The odd-length
prefixes range from $1$ to $bT-1$ and give the residues of $h + \lfloor h/b \rfloor$. This latter
sequence spans the interval from $1$ to $(b+1)T-2$, jumping by two whenever $h$ reaches a
multiple $bu$ of $b$. At such a jump the skipped value is $(b+1)u-1$. Since $b \equiv 1 \pmod q$,
the skipped value is congruent to $r$ exactly when $2u \equiv r+1 \pmod q$, giving the correction
term $C(T-1,2,r+1)$. -/
public theorem palindromeAPCount_base_pow_add_skipped_eq {b k q : ℕ} (hb : 2 ≤ b)
    (hk : 1 ≤ k) (hbq : b ≡ 1 [MOD q]) (r : ℕ) :
    palindromeAPCount b (b ^ k) q r +
      ((Finset.Ioc 0 (b ^ ((k - 1) / 2) - 1)).filter fun h => 2 * h ≡ r + 1 [MOD q]).card =
      ((Finset.Ioc 0 (b ^ (k / 2) - 1)).filter fun h => 2 * h ≡ r [MOD q]).card +
      ((Finset.Ioc 0 ((b + 1) * b ^ ((k - 1) / 2) - 2)).filter fun h => h ≡ r [MOD q]).card := by
  let t := b ^ ((k - 1) / 2)
  have ht : 0 < t := by dsimp [t]; positivity
  have hpow : b ^ ((k + 1) / 2) = t * b := by
    rw [show (k + 1) / 2 = (k - 1) / 2 + 1 by omega, pow_succ]
  have hdiv : (t * b - 1) / b = t - 1 := by
    have hpred : t - 1 + 1 = t := by omega
    have he : (t - 1) * b + b = t * b := by rw [← add_one_mul, hpred]
    apply Nat.div_eq_of_lt_le
    · omega
    · rw [hpred]
      omega
  have hsum : t * b - 1 + (t - 1) = (b + 1) * t - 2 := by
    have hp : 0 < t * b := by positivity
    rw [add_mul, one_mul, mul_comm b t]
    omega
  have he (h : ℕ) : (mirror b 0 h ≡ r [MOD q]) ↔ (2 * h ≡ r [MOD q]) := by
    have H : mirror b 0 h ≡ 2 * h [MOD q] := by simpa [two_mul] using mirror_modEq hb hbq 0 h
    exact ⟨H.symm.trans, H.trans⟩
  have ho (h : ℕ) : (mirror b 1 h ≡ r [MOD q]) ↔ (h + h / b ≡ r [MOD q]) := by
    have H : mirror b 1 h ≡ h + h / b [MOD q] := by simpa using mirror_modEq hb hbq 1 h
    exact ⟨H.symm.trans, H.trans⟩
  rw [count_split hb, cutoff_base_pow hb hk (by decide), cutoff_base_pow hb hk (by decide)]
  simp only [countTo, Nat.add_zero, hpow, he, ho, add_assoc]
  congr 1
  simpa only [hdiv, hsum, countTo, residueCount] using odd_count_with_skips hbq r (t * b - 1)

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

open abs_palindromeAPCount_sub_le Finset in
/-- For a base `b ≥ 2`, a bound `m` with `k + 1` base-`b` digits, and a residue `r < q`
with `b ≡ 1 [MOD q]`, the palindrome count splits into two counts of leading halves.
Write `P = b ^ ((k + 1) / 2)` and `H = m / P`. The upper bounds are exclusive: the prefixes
for even digit length run below `H` if `k` is odd and below `P` otherwise; those for odd digit
length use the other bound. Their residue tests are `2 * x ≡ r [MOD q]` and
`2 * (x / b) + x % b ≡ r [MOD q]`, respectively. Subtract the two zero prefixes when `r = 0`.
The last prefix `H` contributes separately if its reflection `C` fits below or at `m` and
passes the residue test for its digit length. -/
public theorem palindromeAPCount_eq_prefix_counts {b m q r k : ℕ} (hb : 2 ≤ b)
    (hk : (b.digits m).length = k + 1) (hr : r < q) (hbq : b ≡ 1 [MOD q]) :
    let P := b ^ ((k + 1) / 2)
    let H := m / P
    let ds := b.digits m
    let C := Nat.ofDigits b
      ((ds.drop (ds.length / 2 + ds.length % 2)).reverse ++ ds.drop (ds.length / 2))
    palindromeAPCount b m q r + (if r = 0 then 2 else 0) =
      Nat.count (fun x => 2 * x ≡ r [MOD q]) (if Odd k then H else P) +
      Nat.count (fun x => 2 * (x / b) + x % b ≡ r [MOD q]) (if Odd k then P else H) +
      (if C ≤ m ∧ (if Odd k then 2 * H else 2 * (H / b) + H % b) ≡ r [MOD q]
        then 1 else 0) := by
  dsimp only
  let P := b ^ ((k + 1) / 2)
  let H := m / P
  let e := (k + 1) % 2
  let C := Nat.ofDigits b
    (((b.digits m).drop ((b.digits m).length / 2 + (b.digits m).length % 2)).reverse ++
      (b.digits m).drop ((b.digits m).length / 2))
  change _ = Nat.count (fun x => 2 * x ≡ r [MOD q]) (if Odd k then H else P) +
    Nat.count (fun x => 2 * (x / b) + x % b ≡ r [MOD q]) (if Odd k then P else H) +
    (if C ≤ m ∧ (if Odd k then 2 * H else 2 * (H / b) + H % b) ≡ r [MOD q] then 1 else 0)
  have hcopy : mirror b e H = C := by
    simp only [C, mirror, H, P, e, Nat.digits_div_pow hb, List.drop_drop, hk]
  have hz (e' : ℕ) : (if mirror b e' 0 ≡ r [MOD q] then 1 else 0) =
      (if r = 0 then 1 else 0 : ℕ) := by
    simp [mirror, Nat.ModEq, Nat.mod_eq_of_lt hr, eq_comm]
  have hsum (e' : ℕ) := count_mirror_range (cutoff b e' m) (fun x => mirror b e' x ≡ r [MOD q])
  have hinactive := inactive_cutoff hb hk
  change cutoff b (k % 2) m + 1 = P at hinactive
  have hactive := active_cutoff hb hk
  change cutoff b e m + 1 = H + (if mirror b e H ≤ m then 1 else 0) at hactive
  have hsplit : Nat.count (fun x => mirror b e x ≡ r [MOD q]) (cutoff b e m + 1) =
      Nat.count (fun x => mirror b e x ≡ r [MOD q]) H +
        (if C ≤ m ∧ mirror b e H ≡ r [MOD q] then 1 else 0) := by
    rw [hactive, hcopy]
    by_cases hc : C ≤ m
    · simp [hc, Nat.count_succ, hcopy]
    · simp [hc]
  have he (x : ℕ) : (mirror b 0 x ≡ r [MOD q]) ↔ (2 * x ≡ r [MOD q]) :=
    ⟨(mirror_zero_modEq hb hbq x).symm.trans, (mirror_zero_modEq hb hbq x).trans⟩
  have ho (x : ℕ) : (mirror b 1 x ≡ r [MOD q]) ↔ (2 * (x / b) + x % b ≡ r [MOD q]) :=
    ⟨(mirror_center_modEq hb hbq x).symm.trans, (mirror_center_modEq hb hbq x).trans⟩
  have hz₂ : (if r = 0 then 2 else 0 : ℕ) =
      (if r = 0 then 1 else 0) + (if r = 0 then 1 else 0) := by
    split <;> decide
  rw [count_split hb, hz₂]
  by_cases hk' : Odd k
  · have hp := Nat.odd_iff.mp hk'
    have hp' : e = 0 := by dsimp [e]; omega
    rw [hp', hsum, hz] at hsplit
    simp only [he] at hsplit
    rw [hp] at hinactive
    have J := hsum 1
    rw [hinactive, hz] at J
    simp only [ho] at J
    simp only [he, ho, hk', ite_true]
    omega
  · have hp := Nat.even_iff.mp (Nat.not_odd_iff_even.mp hk')
    have hp' : e = 1 := by dsimp [e]; omega
    rw [hp', hsum, hz] at hsplit
    simp only [ho] at hsplit
    rw [hp] at hinactive
    have J := hsum 0
    rw [hinactive, hz] at J
    simp only [he] at J
    simp only [he, ho, hk', ite_false]
    omega

end MetaMathlibExt
