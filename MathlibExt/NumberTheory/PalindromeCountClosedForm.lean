/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PalindromesArithmeticProgressions
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.List.GetD

/-!
# Closed forms for palindrome counts

At a fixed digit length, a palindrome is determined by its upper half, including the
middle digit if there is one. Group these prefixes by their leading digit. All blocks
before the leading digit of the bound are unrestricted; the last block ends at the
bound's prefix, which is counted exactly when its reflection does not exceed the bound.
-/

namespace MetaMathlibExt

open Finset Int

@[expose] public section

/-- **Palindromic half copy.** For natural numbers $b$ and $m \ge 1$, write
$m = (a_k a_{k-1} \cdots a_0)_b$ for the base-$b$ digits of $m$. The palindromic half copy of $m$
is $C_b(m) = \sum_{j=0}^{k} a_{\max(j, k - j)} b^j$: the $b$-adic palindrome with the same number
of digits as $m$ whose upper digits $a_k, \dots, a_{\lceil k/2 \rceil}$ are those of $m$ and whose
lower digits mirror them. For $m = 0$, which has no digits, $C_b(0) = 0$.

Source: K. Onphaeng, T. Khemaratchatakumthorn, P. N. Phunphayap and P. Pongsriiam, *Exact
Formulas for the Number of Palindromes in Certain Arithmetic Progressions*, Journal of Integer
Sequences 27 (2024), Article 24.4.8, Definition 1. -/
public def palindromicHalfCopy (b m : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (Nat.digits b m).length,
    (Nat.digits b m).getD (max j ((Nat.digits b m).length - 1 - j)) 0 * b ^ j

end

private theorem ofDigits_sum (b : ℕ) (l : List ℕ) :
    Nat.ofDigits b l = ∑ i ∈ range l.length, l.getD i 0 * b ^ i := by
  rw [Nat.ofDigits_eq_sum_mapIdx, List.mapIdx_eq_ofFn, List.sum_ofFn, Finset.sum_range]
  exact sum_congr rfl fun i _ => by rw [List.getD_eq_getElem _ _ i.isLt, List.get_eq_getElem]

private def reflectDigits (l : List ℕ) : List ℕ :=
  (l.drop (l.length / 2 + l.length % 2)).reverse ++ l.drop (l.length / 2)

private theorem reflectDigits_length (l : List ℕ) : (reflectDigits l).length = l.length := by
  simp only [reflectDigits, List.length_append, List.length_reverse, List.length_drop]
  omega

private theorem reflectDigits_getD (l : List ℕ) {i : ℕ} (hi : i < l.length) :
    (reflectDigits l).getD i 0 = l.getD (max i (l.length - 1 - i)) 0 := by
  let j := l.length / 2
  let lo := l.drop (j + l.length % 2)
  let hi' := l.drop j
  have hlo : lo.reverse.length = j := by
    simp only [lo, j, List.length_reverse, List.length_drop]; omega
  have hmax : max i (l.length - 1 - i) < l.length := by omega
  have hidx : i < (lo.reverse ++ hi').length := by
    change i < (reflectDigits l).length
    simpa only [reflectDigits_length] using hi
  change (lo.reverse ++ hi').getD i 0 = _
  rw [List.getD_eq_getElem _ 0 hidx, List.getD_eq_getElem _ 0 hmax]
  by_cases hij : i < j
  · rw [List.getElem_append_left (by omega), List.getElem_reverse, List.getElem_drop]
    have he : j + l.length % 2 + ((lo.length - 1) - i) = max i (l.length - 1 - i) := by
      simp only [List.length_reverse] at hlo
      dsimp [j] at *
      omega
    congr 1
  · rw [List.getElem_append_right (by omega), List.getElem_drop]
    have he : j + (i - lo.reverse.length) = max i (l.length - 1 - i) := by
      dsimp [j] at *
      omega
    congr 1

private theorem reflectDigits_palindrome (l : List ℕ) : (reflectDigits l).Palindrome := by
  rw [List.Palindrome.iff_reverse_eq]
  refine List.ext_getElem (by simp) fun i hi hj => ?_
  rw [List.getElem_reverse, ← List.getD_eq_getElem _ 0, ← List.getD_eq_getElem _ 0,
    reflectDigits_getD, reflectDigits_getD]
  · simp only [reflectDigits_length] at hj ⊢
    congr 1
    omega
  · simpa only [reflectDigits_length] using hj
  · simpa only [reflectDigits_length] using (show (reflectDigits l).length - 1 - i <
        (reflectDigits l).length by omega)

private theorem getD_palindrome {l : List ℕ} (hp : l.Palindrome) {i : ℕ} (hi : i < l.length) :
    l.getD i 0 = l.getD (l.length - 1 - i) 0 := by
  have hrev : i < l.reverse.length := by simpa using hi
  calc
    l.getD i 0 = l.reverse.getD i 0 := by rw [hp.reverse_eq]
    _ = l.getD (l.length - 1 - i) 0 := by
      rw [List.getD_eq_getElem _ 0 hrev, List.getD_eq_getElem _ 0 (by omega), List.getElem_reverse]

private theorem reflectDigits_eq_self {l : List ℕ} (hp : l.Palindrome) : reflectDigits l = l := by
  refine List.ext_getElem (reflectDigits_length _) fun i hi hj => ?_
  rw [← List.getD_eq_getElem _ 0 hi, ← List.getD_eq_getElem _ 0 hj, reflectDigits_getD _ hj]
  by_cases h : l.length - 1 - i ≤ i
  · rw [max_eq_left h]
  · rw [max_eq_right (by omega), ← getD_palindrome hp hj]

private theorem halfCopy_ofDigits (b m : ℕ) :
    palindromicHalfCopy b m = Nat.ofDigits b (reflectDigits (b.digits m)) := by
  rw [palindromicHalfCopy, ofDigits_sum, reflectDigits_length]
  exact sum_congr rfl fun _ hi => by rw [reflectDigits_getD _ (mem_range.mp hi)]

private theorem last_drop_ne_zero (b n t : ℕ) (h : (b.digits n).drop t ≠ []) :
    ((b.digits n).drop t).getLast h ≠ 0 := by
  have hn : n ≠ 0 := by
    intro hn
    simp [hn] at h
  have H := Nat.getLast_digit_ne_zero b hn
  have he : (b.digits n).take t ++ (b.digits n).drop t = b.digits n := List.take_append_drop ..
  simpa only [← List.getLast_append_of_right_ne_nil ((b.digits n).take t) _ h, he] using H

private theorem digits_drop_div {b : ℕ} (hb : 2 ≤ b) (n t : ℕ) :
    b.digits (n / b ^ t) = (b.digits n).drop t := by
  rw [Nat.self_div_pow_eq_ofDigits_drop _ _ hb]
  exact Nat.digits_ofDigits b hb _ (fun _ hx => Nat.digits_lt_base hb (List.mem_of_mem_drop hx))
    (last_drop_ne_zero b n t)

private theorem digits_halfCopy {b : ℕ} (hb : 2 ≤ b) (m : ℕ) :
    b.digits (palindromicHalfCopy b m) = reflectDigits (b.digits m) := by
  rw [halfCopy_ofDigits]
  apply Nat.digits_ofDigits b hb
  · intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact Nat.digits_lt_base hb (List.mem_of_mem_drop (List.mem_reverse.mp h))
    · exact Nat.digits_lt_base hb (List.mem_of_mem_drop h)
  · intro hn
    have hd : (b.digits m).drop ((b.digits m).length / 2) ≠ [] := by
      intro hh
      have H := congrArg List.length hh
      simp only [List.length_drop, List.length_nil] at H
      apply hn
      apply List.length_eq_zero_iff.mp
      rw [reflectDigits_length]
      omega
    exact (List.getLast_append_of_right_ne_nil _ _ hd).symm ▸ last_drop_ne_zero b m _ hd

private theorem halfCopy_prefix {b : ℕ} (hb : 2 ≤ b) (m : ℕ) :
    palindromicHalfCopy b m / b ^ ((b.digits m).length / 2) =
      m / b ^ ((b.digits m).length / 2) := by
  let ds := b.digits m
  let lo := (ds.drop (ds.length / 2 + ds.length % 2)).reverse
  let hi := ds.drop (ds.length / 2)
  have hl : lo.length = ds.length / 2 := by
    simp only [lo, List.length_reverse, List.length_drop]; omega
  have hd : (lo ++ hi).drop (ds.length / 2) = hi := by rw [← hl, List.drop_left]
  rw [Nat.self_div_pow_eq_ofDigits_drop _ _ hb, Nat.self_div_pow_eq_ofDigits_drop _ m hb,
    digits_halfCopy hb, show reflectDigits ds = lo ++ hi from rfl, hd]

private theorem halfCopy_eq_self {b n : ℕ} (hp : (b.digits n).Palindrome) :
    palindromicHalfCopy b n = n := by
  rw [halfCopy_ofDigits, reflectDigits_eq_self hp, Nat.ofDigits_digits]

private theorem halfCopy_eq_of_prefix {b x y : ℕ} (hb : 2 ≤ b)
    (hlen : (b.digits x).length = (b.digits y).length)
    (h : x / b ^ ((b.digits x).length / 2) = y / b ^ ((b.digits y).length / 2)) :
    palindromicHalfCopy b x = palindromicHalfCopy b y := by
  have hd := congrArg (Nat.digits b) h
  simp only [digits_drop_div hb, hlen] at hd
  simp only [halfCopy_ofDigits, reflectDigits, ← List.drop_drop, hlen, hd]

private theorem length_digits_eq {b n k : ℕ} (hb : 2 ≤ b) (hn : n ≠ 0) :
    (b.digits n).length = k + 1 ↔ b ^ k ≤ n ∧ n < b ^ (k + 1) := by
  rw [Nat.length_digits b n hb hn, ← Nat.le_log_iff_pow_le hb hn,
    ← Nat.log_lt_iff_lt_pow hb hn]
  omega

private theorem leading_digit {b n k : ℕ} (hb : 2 ≤ b) (hn : n ≠ 0)
    (hk : (b.digits n).length = k + 1) : (b.digits n).getD k 0 = n / b ^ k := by
  have h := (length_digits_eq hb hn).mp hk
  have hb' : 0 < b ^ k := by positivity
  have hlo : 0 < n / b ^ k := Nat.le_div_iff_mul_le hb' |>.mpr (by simpa using h.1)
  have hhi : n / b ^ k < b := (Nat.div_lt_iff_lt_mul hb').mpr (by
    simpa only [pow_succ', Nat.succ_eq_add_one] using h.2)
  have hd : (b.digits n).drop k = [n / b ^ k] := by
    rw [← digits_drop_div hb, Nat.digits_of_lt b _ hlo.ne' hhi]
  have hl : k < (b.digits n).length := by omega
  rw [List.getD_eq_getElem _ 0 hl]
  have hi : 0 < ((b.digits n).drop k).length := by simp [hk]
  have he : ((b.digits n).drop k)[0] = (b.digits n)[k] := by simp [List.getElem_drop]
  rw [← he]
  exact (List.getElem_of_eq hd hi).trans rfl

private theorem palindrome_modEq_lead {b n k q r : ℕ} (hb : 2 ≤ b) (hn : n ≠ 0)
    (hqb : q ∣ b) (hk : (b.digits n).length = k + 1) (hp : (b.digits n).Palindrome) :
    (n ≡ r [MOD q]) ↔ (n / b ^ k ≡ r [MOD q]) := by
  have hFirst : (b.digits n).getD 0 0 = n % b := by
    rw [Nat.digits_eq_cons_digits_div hb hn]; rfl
  have he := getD_palindrome hp (i := 0) (by omega)
  rw [hFirst, Nat.sub_zero, show (b.digits n).length - 1 = k by omega, leading_digit hb hn hk] at he
  simp only [Nat.ModEq, ← he, Nat.mod_mod_of_dvd _ hqb]

-- With the digit length fixed, dividing by b^((k+1)/2) is a bijection onto an
-- interval of prefixes. The cutoff includes the last prefix precisely if its copy fits.
private theorem prefix_card {b m k q r : ℕ} (hb : 2 ≤ b) (hq : q ∣ b)
    (hm : b ^ k ≤ m) (hm' : m < b ^ (k + 1)) :
    let w := b ^ (k / 2)
    let c := b ^ ((k + 1) / 2)
    let h := m / c
    let d : ℕ := if palindromicHalfCopy b m ≤ m then 1 else 0
    ((Icc (b ^ k) m).filter fun n => (b.digits n).Palindrome ∧ n ≡ r [MOD q]).card =
      ((Ico w (h + d)).filter fun u => u / w ≡ r [MOD q]).card := by
  dsimp only
  let w := b ^ (k / 2)
  let c := b ^ ((k + 1) / 2)
  let h := m / c
  let d : ℕ := if palindromicHalfCopy b m ≤ m then 1 else 0
  change _ = ((Ico w (h + d)).filter fun u => u / w ≡ r [MOD q]).card
  have hwc : w * c = b ^ k := by rw [← pow_add]; congr 1; omega
  have hc : 0 < c := by dsimp [c]; positivity
  have hb' : 0 < b ^ k := by positivity
  have hlen {n : ℕ} (hn : b ^ k ≤ n) (hn' : n < b ^ (k + 1)) :
      (b.digits n).length = k + 1 :=
    (length_digits_eq hb (by omega)).mpr ⟨hn, hn'⟩
  have hlead (n : ℕ) : n / c / w = n / b ^ k := by
    rw [Nat.div_div_eq_div_mul, mul_comm, hwc]
  have copy_prefix {n : ℕ} (hl : (b.digits n).length = k + 1) :
      palindromicHalfCopy b n / c = n / c := by simpa only [hl] using halfCopy_prefix hb n
  have copy_eq {x y : ℕ} (hx : (b.digits x).length = k + 1)
      (hy : (b.digits y).length = k + 1) (he : x / c = y / c) :
      palindromicHalfCopy b x = palindromicHalfCopy b y :=
    halfCopy_eq_of_prefix hb (hx.trans hy.symm) (by simpa only [hx, hy] using he)
  have hd (u : ℕ) : u < h + d ↔ u < h ∨ u = h ∧ palindromicHalfCopy b m ≤ m := by
    dsimp [d]; split <;> omega
  refine card_bij (fun n _ => n / c) ?_ ?_ ?_
  · intro n hn
    simp only [mem_filter, mem_Icc] at hn
    obtain ⟨⟨hlo, hhi⟩, hp, hr⟩ := hn
    have hnlen := hlen hlo (hhi.trans_lt hm')
    refine mem_filter.mpr ⟨mem_Ico.mpr ⟨(Nat.le_div_iff_mul_le hc).mpr (hwc ▸ hlo), ?_⟩, ?_⟩
    · apply (hd _).mpr
      rcases lt_or_eq_of_le (Nat.div_le_div_right hhi : n / c ≤ h) with H | H
      · exact Or.inl H
      · exact Or.inr ⟨H, (copy_eq hnlen (hlen hm hm') H).symm ▸ ((halfCopy_eq_self hp).symm ▸ hhi)⟩
    · rw [hlead]
      exact (palindrome_modEq_lead hb (by omega) hq hnlen hp).mp hr
  · intro x hx y hy hxy
    simp only [mem_filter, mem_Icc] at hx hy
    have he := copy_eq (hlen hx.1.1 (hx.1.2.trans_lt hm')) (hlen hy.1.1 (hy.1.2.trans_lt hm')) hxy
    rwa [halfCopy_eq_self hx.2.1, halfCopy_eq_self hy.2.1] at he
  · intro u hu
    simp only [mem_filter, mem_Ico] at hu
    have hub := (hd _).mp hu.1.2
    have huh : u ≤ h := by omega
    let z := u * c
    have hzlo : b ^ k ≤ z := hwc ▸ Nat.mul_le_mul_right c hu.1.1
    have hzhi : z ≤ m := (Nat.le_div_iff_mul_le hc).mp huh
    have hzlen := hlen hzlo (hzhi.trans_lt hm')
    let n := palindromicHalfCopy b z
    have hnlen : (b.digits n).length = k + 1 := by
      simp only [n, digits_halfCopy hb, reflectDigits_length, hzlen]
    have hnpos : n ≠ 0 := by intro hn; simp [hn] at hnlen
    have hnlo := ((length_digits_eq hb hnpos).mp hnlen).1
    have hp : (b.digits n).Palindrome := by
      change (b.digits (palindromicHalfCopy b z)).Palindrome
      rw [digits_halfCopy hb]
      exact reflectDigits_palindrome _
    have hnu : n / c = u := by
      change palindromicHalfCopy b (u * c) / c = u
      rw [show palindromicHalfCopy b (u * c) / c = (u * c) / c from copy_prefix hzlen,
        mul_comm, Nat.mul_div_cancel_left _ hc]
    have hnhi : n ≤ m := by
      rcases hub with H | ⟨H, H'⟩
      · have H₁ := (Nat.div_lt_iff_lt_mul hc).mp (show n / c < h by rw [hnu]; exact H)
        have H₂ := (Nat.le_div_iff_mul_le hc).mp (le_refl h)
        exact H₁.le.trans H₂
      · have e : z / c = h := by
          change u * c / c = h
          rw [mul_comm, Nat.mul_div_cancel_left _ hc, H]
        exact (copy_eq hzlen (hlen hm hm') e).trans_le H'
    have hr : n ≡ r [MOD q] := (palindrome_modEq_lead hb hnpos hq hnlen hp).mpr (by
      rw [← hlead, hnu]
      exact hu.2)
    exact ⟨n, mem_filter.mpr ⟨mem_Icc.mpr ⟨hnlo, hnhi⟩, hp, hr⟩, hnu⟩

private theorem card_filter_Ico_split {l u v : ℕ} (h₁ : l ≤ u) (h₂ : u ≤ v)
    (p : ℕ → Prop) [DecidablePred p] :
    ((Ico l v).filter p).card = ((Ico l u).filter p).card + ((Ico u v).filter p).card := by
  rw [← Ico_union_Ico_eq_Ico h₁ h₂, filter_union, card_union_of_disjoint]
  exact (Ico_disjoint_Ico_consecutive l u v).mono (filter_subset _ _) (filter_subset _ _)

private theorem prefix_blocks {w : ℕ} (hw : 0 < w) (a q r : ℕ) :
    ((Ico w (a * w)).filter fun u => u / w ≡ r [MOD q]).card =
      ((Ico 1 a).filter fun i => i ≡ r [MOD q]).card * w := by
  conv_rhs => rw [← card_range w, ← card_product]
  refine card_bij' (fun u _ => (u / w, u % w)) (fun x _ => x.2 + w * x.1) ?_ ?_ ?_ ?_
  · intro u hu
    simp only [mem_filter, mem_Ico] at hu
    simp only [mem_product, mem_filter, mem_Ico, mem_range]
    exact ⟨⟨⟨(Nat.le_div_iff_mul_le hw).mpr (by simpa using hu.1.1),
      (Nat.div_lt_iff_lt_mul hw).mpr hu.1.2⟩, hu.2⟩, Nat.mod_lt _ hw⟩
  · intro x hx
    simp only [mem_product, mem_filter, mem_Ico, mem_range] at hx
    have he : (x.2 + w * x.1) / w = x.1 := by
      rw [Nat.add_mul_div_left _ _ hw, Nat.div_eq_of_lt hx.2, zero_add]
    have hlow : w ≤ x.2 + w * x.1 := by
      have hl : 1 ≤ (x.2 + w * x.1) / w := by rw [he]; exact hx.1.1.1
      simpa only [one_mul] using (Nat.le_div_iff_mul_le hw).mp hl
    simp only [mem_filter, mem_Ico, ← Nat.div_lt_iff_lt_mul hw, he]
    exact ⟨⟨hlow, hx.1.1.2⟩, hx.1.2⟩
  · intro u _
    exact Nat.mod_add_div ..
  · intro x hx
    have hl : x.2 < w := mem_range.mp (mem_product.mp hx).2
    simp [Nat.add_mul_div_left _ _ hw, Nat.div_eq_of_lt hl, Nat.mod_eq_of_lt hl]

private theorem prefix_partial {w h : ℕ} (hw : 0 < w) (hwh : w ≤ h) (q r : ℕ)
    (d : ℕ) (hd : d ≤ 1) :
    ((Ico w (h + d)).filter fun u => u / w ≡ r [MOD q]).card =
      ((Ico 1 (h / w)).filter fun i => i ≡ r [MOD q]).card * w +
        if h / w ≡ r [MOD q] then h % w + d else 0 := by
  let a := h / w
  have hal : 1 ≤ a := (Nat.le_div_iff_mul_le hw).mpr (by simpa using hwh)
  have H : a * w + h % w = h := by simpa only [mul_comm] using Nat.div_add_mod h w
  have hlow : a * w ≤ h + d := by omega
  have hhigh : h + d ≤ (a + 1) * w := by
    rw [add_mul, one_mul]
    have := Nat.mod_lt h hw
    omega
  rw [card_filter_Ico_split (by simpa using Nat.mul_le_mul_right w hal) hlow, prefix_blocks hw]
  congr 1
  have he : ∀ u ∈ Ico (a * w) (h + d), u / w = a := by
    intro u hu
    exact Nat.div_eq_of_lt_le (mem_Ico.mp hu).1 ((mem_Ico.mp hu).2.trans_le hhigh)
  change _ = if a ≡ r [MOD q] then h % w + d else 0
  by_cases hr : a ≡ r [MOD q]
  · have hf : (Ico (a * w) (h + d)).filter (fun u => u / w ≡ r [MOD q]) = Ico (a * w) (h + d) :=
      filter_true_of_mem fun u hu => he u hu ▸ hr
    rw [hf, ite_eq_left hr, Nat.card_Ico]
    omega
  · have hf : (Ico (a * w) (h + d)).filter (fun u => u / w ≡ r [MOD q]) = ∅ :=
      filter_false_of_mem fun u hu => he u hu ▸ hr
    simp [hf, hr]

private theorem full_length_card {b q : ℕ} (hb : 2 ≤ b) (hq : q ∣ b) (k r : ℕ) :
    ((Ico (b ^ k) (b ^ (k + 1))).filter fun n => (b.digits n).Palindrome ∧ n ≡ r [MOD q]).card =
      ((Ico 1 b).filter fun a => a ≡ r [MOD q]).card * b ^ (k / 2) := by
  let m := b ^ (k + 1) - 1
  let w := b ^ (k / 2)
  let c := b ^ ((k + 1) / 2)
  have hw : 0 < w := by dsimp [w]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have h₁ : b ^ k ≤ m := by
    dsimp [m]
    have H : b ^ k < b ^ (k + 1) := Nat.pow_lt_pow_right hb (Nat.lt_succ_self k)
    omega
  have h₂ : m < b ^ (k + 1) := by
    dsimp [m]
    have : 0 < b ^ (k + 1) := by positivity
    omega
  have hlen := (length_digits_eq hb (show m ≠ 0 by
    have : 0 < b ^ k := by positivity
    omega)).mpr ⟨h₁, h₂⟩
  have hd := digits_halfCopy hb m
  have hl : (b.digits (palindromicHalfCopy b m)).length = k + 1 := by
    rw [hd, reflectDigits_length, hlen]
  have hn : palindromicHalfCopy b m ≠ 0 := by intro hn; simp [hn] at hl
  have hbound : palindromicHalfCopy b m ≤ m := by
    have := ((length_digits_eq hb hn).mp hl).2
    omega
  have he : Ico (b ^ k) (b ^ (k + 1)) = Icc (b ^ k) m := by
    ext n; simp only [mem_Ico, mem_Icc]; omega
  rw [he, prefix_card hb hq h₁ h₂, ite_eq_left hbound]
  have hpow : b ^ (k + 1) = (b * w) * c := by
    rw [mul_assoc, ← pow_add, ← pow_succ']
    congr 1
    omega
  have hp : m / c + 1 = b * w := by
    have H : 0 < b * w := by positivity
    have HH : m / c = b * w - 1 := by
      apply Nat.div_eq_of_lt_le
      · have HH : (b * w - 1 + 1) * c = b ^ (k + 1) := by rw [Nat.sub_add_cancel (by omega), hpow]
        rw [add_mul, one_mul] at HH
        omega
      · rw [Nat.sub_add_cancel (by omega), ← hpow]
        exact h₂
    omega
  change ((Ico w (m / c + 1)).filter fun u => u / w ≡ r [MOD q]).card = _
  rw [hp, prefix_blocks hw]

private theorem short_count {b q : ℕ} (hb : 2 ≤ b) (hq : q ∣ b) (k r : ℕ) :
    ((Ico 1 (b ^ k)).filter fun n => (b.digits n).Palindrome ∧ n ≡ r [MOD q]).card =
      ((Ico 1 b).filter fun a => a ≡ r [MOD q]).card * ∑ j ∈ range k, b ^ (j / 2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [card_filter_Ico_split (show 1 ≤ b ^ k from Nat.one_le_pow _ _ (by omega))
      (Nat.pow_le_pow_right (by omega) (Nat.le_succ k)), ih, full_length_card hb hq,
      sum_range_succ, mul_add]

-- Group the admissible palindromes by whether their digit length is shorter
-- than the bound's. The two groups have disjoint intervals.
private theorem count_by_leading_digit {b m k q r : ℕ} (hb : 2 ≤ b) (hq : q ∣ b)
    (hm : b ^ k ≤ m) (hm' : m < b ^ (k + 1)) :
    let w := b ^ (k / 2)
    let h := m / b ^ ((k + 1) / 2)
    let a := m / b ^ k
    let d : ℕ := if palindromicHalfCopy b m ≤ m then 1 else 0
    palindromeAPCount b m q r = ((Ico 1 b).filter fun i => i ≡ r [MOD q]).card *
        (∑ j ∈ range k, b ^ (j / 2)) + ((Ico 1 a).filter fun i => i ≡ r [MOD q]).card * w +
      if a ≡ r [MOD q] then h % w + d else 0 := by
  dsimp only
  have hpow : b ^ (k / 2) * b ^ ((k + 1) / 2) = b ^ k := by rw [← pow_add]; congr 1; omega
  have hc : 0 < b ^ ((k + 1) / 2) := by positivity
  have hw : 0 < b ^ (k / 2) := by positivity
  have hwh : b ^ (k / 2) ≤ m / b ^ ((k + 1) / 2) := (Nat.le_div_iff_mul_le hc).mpr (hpow ▸ hm)
  have hlead : m / b ^ ((k + 1) / 2) / b ^ (k / 2) = m / b ^ k := by
    rw [Nat.div_div_eq_div_mul, mul_comm, hpow]
  have hpartition : Icc 1 m = Ico 1 (b ^ k) ∪ Icc (b ^ k) m := by
    ext n; simp only [mem_union, mem_Ico, mem_Icc]
    have H : 0 < b ^ k := by positivity
    omega
  have hdisj : Disjoint (Ico 1 (b ^ k)) (Icc (b ^ k) m) := by
    apply disjoint_left.mpr
    intro n h₁ h₂
    exact (mem_Ico.mp h₁).2.not_ge (mem_Icc.mp h₂).1
  unfold palindromeAPCount
  rw [hpartition, filter_union, card_union_of_disjoint
    (hdisj.mono (filter_subset _ _) (filter_subset _ _)), short_count hb hq,
    prefix_card hb hq hm hm',
    prefix_partial hw hwh _ _ _ (by split <;> decide), hlead, add_assoc]

private theorem prefix_as_sum {b m k : ℕ} (hb : 2 ≤ b) (hk : (b.digits m).length = k + 1) :
    (m / b ^ ((k + 1) / 2) : ℕ) =
      ∑ i ∈ range (k / 2 + 1), (b.digits m).getD (k - i) 0 * b ^ (k / 2 - i) := by
  let d := (k + 1) / 2
  let l := (b.digits m).drop d
  have hl : l.length = k / 2 + 1 := by simp only [l, List.length_drop, hk, d]; omega
  rw [Nat.self_div_pow_eq_ofDigits_drop _ _ hb]
  change Nat.ofDigits b l = _
  rw [ofDigits_sum, ← sum_range_reflect, hl]
  apply sum_congr rfl
  intro i hi
  have hi' := mem_range.mp hi
  have hr : k / 2 + 1 - 1 - i < l.length := by omega
  have hm : k - i < (b.digits m).length := by omega
  simp only [Nat.add_sub_cancel]
  have he : l.getD (k / 2 - i) 0 = (b.digits m).getD (k - i) 0 := by
    rw [List.getD_eq_getElem l 0 (by omega), List.getD_eq_getElem _ 0 hm]
    change ((b.digits m).drop d)[k / 2 - i] = _
    rw [List.getElem_drop]
    congr 1
    dsimp [d]
    omega
  rw [he]

private theorem short_geometric {b : ℕ} (hb : 2 ≤ b) (k : ℕ) :
    ∑ j ∈ range k, (b : ℚ) ^ (j / 2) =
      ((b : ℚ) ^ ((k + 1) / 2) + (b : ℚ) ^ (k / 2) - 2) / ((b : ℚ) - 1) := by
  have hb' : (b : ℚ) ≠ 1 := by exact_mod_cast (show b ≠ 1 by omega)
  have H (j : ℕ) : (∑ i ∈ range j, (b : ℚ) ^ (i / 2)) * ((b : ℚ) - 1) =
      (b : ℚ) ^ ((j + 1) / 2) + (b : ℚ) ^ (j / 2) - 2 := by
    induction j with
    | zero => norm_num
    | succ j ih =>
      have he : (j + 1 + 1) / 2 = j / 2 + 1 := by omega
      rw [sum_range_succ, add_mul, ih, he, pow_succ]
      ring
  apply (eq_div_iff (sub_ne_zero.mpr hb')).2 (H k)

private theorem card_even (a : ℕ) (ha : 1 ≤ a) :
    ((Ico 1 a).filter fun i => i ≡ 0 [MOD 2]).card = (a - 1) / 2 := by
  have he : Ico 1 a = Ioc 0 (a - 1) := by ext i; simp; omega
  rw [he]
  have h := Nat.Ioc_filter_modEq_card 0 (a - 1) (r := 2) (by decide) 0
  have hd : ⌊(((a - 1 : ℕ) : ℚ) / 2)⌋ = (((a - 1) / 2 : ℕ) : ℤ) := by
    apply floor_eq_iff.mpr
    rw [Int.cast_natCast]
    constructor <;> linarith [show (((a - 1 : ℕ) / 2 : ℕ) : ℚ) * 2 ≤ (↑(a - 1 : ℕ) : ℚ) by
        exact_mod_cast (show ((a - 1) / 2) * 2 ≤ a - 1 by omega),
      show (↑(a - 1 : ℕ) : ℚ) < (((a - 1 : ℕ) / 2 : ℕ) : ℚ) * 2 + 2 by
        exact_mod_cast (show a - 1 < ((a - 1) / 2) * 2 + 2 by omega)]
  have h' : (((Ioc 0 (a - 1)).filter fun i => i ≡ 0 [MOD 2]).card : ℤ) =
      max (⌊(((a - 1 : ℕ) : ℚ) / 2)⌋) 0 := by simpa using h
  rw [hd, max_eq_left (Int.natCast_nonneg _)] at h'
  exact_mod_cast h'

private theorem card_odd (a : ℕ) (ha : 1 ≤ a) :
    (((Ico 1 a).filter fun i => i ≡ 1 [MOD 2]).card : ℚ) = (⌈((a : ℚ) - 1) / 2⌉ : ℚ) := by
  have he : 0 ≤ ⌈((a : ℚ) - 1) / 2⌉ := by
    apply Int.ceil_nonneg
    have ha' : (1 : ℚ) ≤ a := by exact_mod_cast ha
    linarith
  have h := Nat.Ico_filter_modEq_card 1 a (r := 2) (by decide) 1
  have h' : (((Ico 1 a).filter fun i => i ≡ 1 [MOD 2]).card : ℤ) =
      ⌈((a : ℚ) - 1) / 2⌉ := by simpa [max_eq_left he] using h
  exact_mod_cast h'

private theorem card_even_base {b : ℕ} (hb : 2 ≤ b) (he : Even b) :
    (((Ico 1 b).filter fun i => i ≡ 0 [MOD 2]).card : ℚ) = (b : ℚ) / 2 - 1 := by
  rw [card_even _ (by omega)]
  obtain ⟨j, hj⟩ := he
  have : (b - 1) / 2 + 1 = j := by omega
  have hj' : (((b - 1) / 2 : ℕ) : ℚ) + 1 = j := by exact_mod_cast this
  have hb' : (b : ℚ) = j + j := by exact_mod_cast hj
  linarith

private theorem card_odd_base {b : ℕ} (he : Even b) :
    (((Ico 1 b).filter fun i => i ≡ 1 [MOD 2]).card : ℚ) = (b : ℚ) / 2 := by
  obtain ⟨j, hj⟩ := he
  have hb' : (b : ℚ) = j + j := by exact_mod_cast hj
  have hceil : ⌈((b : ℚ) - 1) / 2⌉ = (j : ℤ) := by
    apply ceil_eq_iff.mpr
    push_cast
    constructor <;> linarith
  by_cases hb : 1 ≤ b
  · rw [card_odd _ hb, hceil, Int.cast_natCast, hb']
    ring
  · have hzero : b = 0 := by omega
    simp [hzero]

@[expose] public section

/-- **Counting palindromes up to $m$ and by parity.** Let $b \ge 2$ and $m \ge 1$, and write
$m = (a_k a_{k-1} \cdots a_0)_b$ in base $b$, with leading digit $a_k \ne 0$. For natural numbers
$q$ and $r$, let $A_b(m, q, r)$ be the number of $b$-adic palindromes $n$ with $1 \le n \le m$
and $n \equiv r \pmod q$, and let $C_b(m)$ be the palindromic half copy of $m$. Put $\delta = 1$
if $C_b(m) \le m$ and $\delta = 0$ otherwise. Then
$A_b(m, 1, 0) = b^{\lceil k/2 \rceil} +
\sum_{i=0}^{\lfloor k/2 \rfloor} a_{k-i} b^{\lfloor k/2 \rfloor - i} + \delta - 2$.
If moreover $b$ is even, let
$\alpha = (b^{\lceil k/2 \rceil} + b^{\lfloor k/2 \rfloor} - 2)/(b - 1)$ and
$S = \sum_{i=1}^{\lfloor k/2 \rfloor} a_{k-i} b^{\lfloor k/2 \rfloor - i}$, let $\varepsilon_0 = 1$
if $a_k$ is even and $\varepsilon_0 = 0$ otherwise, and let $\varepsilon_1 = 1 - \varepsilon_0$.
Then $A_b(m, 2, 0) = (b/2 - 1)\alpha + \lfloor (a_k - 1)/2 \rfloor b^{\lfloor k/2 \rfloor} +
\varepsilon_0 (S + \delta)$ and
$A_b(m, 2, 1) = b\alpha/2 + \lceil (a_k - 1)/2 \rceil b^{\lfloor k/2 \rfloor} +
\varepsilon_1 (S + \delta)$.

Source: K. Onphaeng, T. Khemaratchatakumthorn, P. N. Phunphayap and P. Pongsriiam, *Exact
Formulas for the Number of Palindromes in Certain Arithmetic Progressions*, Journal of Integer
Sequences 27 (2024), Article 24.4.8, Corollary 8. -/
public theorem palindromeCount_closed_form {b m : ℕ} (hb : 2 ≤ b) (hm : 1 ≤ m) :
    let a : ℕ → ℕ := fun i => (Nat.digits b m).getD i 0
    let k : ℕ := (Nat.digits b m).length - 1
    let α : ℚ := ((b : ℚ) ^ ((k + 1) / 2) + (b : ℚ) ^ (k / 2) - 2) / ((b : ℚ) - 1)
    let S : ℚ := ∑ i ∈ Finset.Icc 1 (k / 2), (a (k - i) : ℚ) * (b : ℚ) ^ (k / 2 - i)
    let δ : ℚ := if palindromicHalfCopy b m ≤ m then 1 else 0
    (palindromeAPCount b m 1 0 : ℚ) =
        (b : ℚ) ^ ((k + 1) / 2) +
          ∑ i ∈ Finset.range (k / 2 + 1), (a (k - i) : ℚ) * (b : ℚ) ^ (k / 2 - i) + δ - 2 ∧
      (Even b →
        (palindromeAPCount b m 2 0 : ℚ) =
            ((b : ℚ) / 2 - 1) * α + (((a k - 1) / 2 : ℕ) : ℚ) * (b : ℚ) ^ (k / 2) +
              (if Even (a k) then 1 else 0) * (S + δ) ∧
          (palindromeAPCount b m 2 1 : ℚ) =
            (b : ℚ) * α / 2 + (⌈((a k : ℚ) - 1) / 2⌉ : ℚ) * (b : ℚ) ^ (k / 2) +
              (if Odd (a k) then 1 else 0) * (S + δ)) := by
  dsimp only
  set k := (b.digits m).length - 1
  set a := fun i : ℕ => (b.digits m).getD i 0
  set α : ℚ := ((b : ℚ) ^ ((k + 1) / 2) + (b : ℚ) ^ (k / 2) - 2) / ((b : ℚ) - 1)
  set S : ℚ := ∑ i ∈ Icc 1 (k / 2), (a (k - i) : ℚ) * (b : ℚ) ^ (k / 2 - i)
  set δ : ℚ := if palindromicHalfCopy b m ≤ m then 1 else 0
  have hm0 : m ≠ 0 := by omega
  have hlen : (b.digits m).length = k + 1 := by
    have H := List.length_pos_iff.mpr ((Nat.digits_ne_nil_iff_ne_zero (b := b)).mpr hm0)
    dsimp [k]
    omega
  have ⟨hlo, hhi⟩ := (length_digits_eq hb hm0).mp hlen
  have ha : a k = m / b ^ k := leading_digit hb hm0 hlen
  have ha₁ : 1 ≤ a k := by
    rw [ha]
    exact (Nat.le_div_iff_mul_le (by positivity)).mpr (by simpa using hlo)
  have hα : α * ((b : ℚ) - 1) = (b : ℚ) ^ ((k + 1) / 2) + (b : ℚ) ^ (k / 2) - 2 := by
    have hb' : (b : ℚ) ≠ 1 := by exact_mod_cast (show b ≠ 1 by omega)
    exact div_mul_cancel₀ _ (sub_ne_zero.mpr hb')
  have hs : ∑ i ∈ range (k / 2 + 1), (a (k - i) : ℚ) * (b : ℚ) ^ (k / 2 - i) =
      (a k : ℚ) * (b : ℚ) ^ (k / 2) + S := by
    rw [sum_range_succ']
    have hi : Icc 1 (k / 2) = Ico 1 (k / 2 + 1) := by ext i; simp
    dsimp [S]
    rw [hi, sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    simp only [add_comm]
  have htail : ((m / b ^ ((k + 1) / 2) % b ^ (k / 2) : ℕ) : ℚ) = S := by
    have hprefix : ((m / b ^ ((k + 1) / 2) : ℕ) : ℚ) = (a k : ℚ) * (b : ℚ) ^ (k / 2) + S := by
      rw [← hs]
      exact_mod_cast prefix_as_sum hb hlen
    have H := congrArg (fun n : ℕ => (n : ℚ))
      (Nat.div_add_mod (m / b ^ ((k + 1) / 2)) (b ^ (k / 2)))
    push_cast only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow] at H
    have hpow : b ^ ((k + 1) / 2) * b ^ (k / 2) = b ^ k := by rw [← pow_add]; congr 1; omega
    rw [Nat.div_div_eq_div_mul, hpow, ← ha, hprefix] at H
    linarith
  have counts {q r : ℕ} (hq : q ∣ b) :
      (palindromeAPCount b m q r : ℚ) = (((Ico 1 b).filter fun i => i ≡ r [MOD q]).card : ℚ) * α +
        (((Ico 1 (a k)).filter fun i => i ≡ r [MOD q]).card : ℚ) * (b : ℚ) ^ (k / 2) +
        (if a k ≡ r [MOD q] then 1 else 0) * (S + δ) := by
    have H := congrArg (fun n : ℕ => (n : ℚ)) (count_by_leading_digit (r := r) hb hq hlo hhi)
    push_cast only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_sum, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero] at H
    rw [short_geometric hb, ← ha, htail] at H
    rw [H]
    change _ + (if a k ≡ r [MOD q] then S + δ else 0) = _
    split_ifs <;> simp only [one_mul, zero_mul] <;> rfl
  constructor
  · have H := counts (q := 1) (r := 0) (one_dvd _)
    simp only [Nat.modEq_one, filter_true, Nat.card_Ico, ite_true, one_mul,
      Nat.cast_sub (show 1 ≤ b by omega), Nat.cast_sub ha₁, Nat.cast_one] at H
    rw [H, hs]
    linarith
  · intro hbEven
    have hdvd : 2 ∣ b := even_iff_two_dvd.mp hbEven
    constructor
    · rw [counts hdvd, card_even_base hb hbEven, card_even _ ha₁]
      simp only [show (a k ≡ 0 [MOD 2]) ↔ Even (a k) from Nat.even_iff.symm]
      rfl
    · rw [counts hdvd, card_odd_base hbEven, card_odd _ ha₁]
      simp only [show (a k ≡ 1 [MOD 2]) ↔ Odd (a k) from Nat.odd_iff.symm]
      ring

end

end MetaMathlibExt
