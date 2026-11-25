/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Set.Card
public import MathlibExt.Combinatorics.Enumerative.AscentSequenceQuadruplePatterns
import Mathlib.Data.List.Basic

/-!
# Weak-ascent Wilf equivalence in Class 162

The Class 162 bijection moves repeated copies of the maximum across the smaller letters
following its first occurrence, and acts recursively on the prefix before that occurrence.
It preserves the multiset of letters and the total number of weak ascents.
-/

namespace MetaMathlibExt
namespace weakAscent_wilf_class162

open List

private def patterns : Bool → Finset (List ℕ)
  | false => {[0, 1, 0], [1, 0, 0], [1, 0, 1], [1, 2, 0]}
  | true => {[0, 1, 0], [1, 0, 0], [1, 1, 0], [1, 2, 0]}

private def Bad (side : Bool) (a b c : ℕ) : Prop :=
  (c ≤ a ∧ a < b) ∨ (b = c ∧ b < a) ∨
    (if side then a = b ∧ c < a else a = c ∧ b < a)

private def Avoid (side : Bool) (w : List ℕ) : Prop :=
  ∀ ⦃a b c⦄, [a, b, c] <+ w → ¬ Bad side a b c

private theorem contains_triple {w : List ℕ} {x y z : ℕ} :
    ContainsPattern w [x, y, z] ↔ ∃ a b c, [a, b, c] <+ w ∧
      ((a < b ↔ x < y) ∧ (b < a ↔ y < x) ∧ (a < c ↔ x < z) ∧ (c < a ↔ z < x) ∧
        (b < c ↔ y < z) ∧ (c < b ↔ z < y)) := by
  constructor
  · rintro ⟨s, hs, hl, ho⟩
    obtain ⟨a, b, c, rfl⟩ : ∃ a b c, s = [a, b, c] := by
      exact List.length_eq_three.mp hl
    refine ⟨a, b, c, hs, ?_⟩
    simp only [length_cons, length_nil, Nat.forall_lt_succ_left] at ho
    simpa [List.getD, and_assoc, and_left_comm, and_comm] using ho
  · rintro ⟨a, b, c, hs, ho⟩
    refine ⟨[a, b, c], hs, rfl, ?_⟩
    simp only [length_cons, length_nil, Nat.forall_lt_succ_left]
    simpa [List.getD, and_assoc, and_left_comm, and_comm] using ho

private theorem avoid_iff (s : Bool) (w : List ℕ) :
    (∀ p ∈ patterns s, ¬ ContainsPattern w p) ↔ Avoid s w := by
  cases s <;> simp [patterns, contains_triple, Avoid, Bad] <;> grind

private theorem Avoid.sub {s : Bool} {u w : List ℕ} (h : Avoid s w) (hs : u <+ w) :
    Avoid s u := fun _ _ _ ht => h (ht.trans hs)

private theorem triple_append {a b c : ℕ} {u v : List ℕ} :
    [a, b, c] <+ u ++ v ↔ [a, b, c] <+ u ∨ ([a, b] <+ u ∧ c ∈ v) ∨
      (a ∈ u ∧ [b, c] <+ v) ∨ [a, b, c] <+ v := by
  rw [sublist_append_iff]
  simp [cons_eq_append_iff, or_and_right, exists_or, and_assoc, or_comm, or_left_comm, or_assoc]

private theorem pair_append {a b : ℕ} {u v : List ℕ} :
    [a, b] <+ u ++ v ↔ [a, b] <+ u ∨ (a ∈ u ∧ b ∈ v) ∨ [a, b] <+ v := by
  rw [sublist_append_iff]
  simp [cons_eq_append_iff, or_and_right, exists_or, and_assoc, or_comm, or_left_comm]

/-- Avoiding 101 puts the extra maxima first. Avoiding 110 puts them last. -/
private def tailBlock (side : Bool) (H k : ℕ) (v : List ℕ) : List ℕ :=
  if side then v ++ replicate k H else replicate k H ++ v

private theorem mem_tailBlock {s : Bool} {x H k : ℕ} {v : List ℕ} :
    x ∈ tailBlock s H k v ↔ x ∈ v ∨ k ≠ 0 ∧ x = H := by
  cases s <;> simp [tailBlock, or_comm]

private theorem tailBlock_perm (s : Bool) (H k : ℕ) (v : List ℕ) :
    tailBlock (!s) H k v ~ tailBlock s H k v := by
  cases s <;> exact perm_append_comm

private theorem stable_partition {p : ℕ → Bool} {t : List ℕ}
    (h : t.Pairwise (fun x y => p y = true → p x = true)) :
    t.filter p ++ t.filter (fun x => !p x) = t := by
  induction t with
  | nil => rfl
  | cons a t ih =>
    obtain ⟨ha, ht⟩ := pairwise_cons.mp h
    cases he : p a with
    | true => simpa [filter_cons, he] using congrArg (a :: ·) (ih ht)
    | false =>
      have hnil : t.filter p = [] := filter_eq_nil_iff.mpr (fun x hx hp => by
        simpa [he] using ha x hx hp)
      simpa [filter_cons, he, hnil] using congrArg (a :: ·) (ih ht)

/-- Read off the order of the maxima from triples starting at the first maximum. -/
private theorem tail_eq {s : Bool} {H : ℕ} {t : List ℕ}
    (ht : ∀ x ∈ t, x ≤ H) (hw : Avoid s (H :: t)) :
    t = tailBlock s H (t.count H) (t.filter (· != H)) := by
  have hp {a b : ℕ} (h : [a, b] <+ t) := hw (h.cons_cons H)
  have hle {a b : ℕ} (h : [a, b] <+ t) : a ≤ H ∧ b ≤ H :=
    ⟨ht _ (h.subset (by simp)), ht _ (h.subset (by simp))⟩
  cases s with
  | false =>
    have h := stable_partition (p := (· == H)) (t := t) (pairwise_of_forall_sublist (by
      intro a b hab
      have := hp hab
      have := hle hab
      simp [Bad] at *
      omega))
    simpa [tailBlock, filter_beq, bne] using h.symm
  | true =>
    have h := stable_partition (p := (· != H)) (t := t) (pairwise_of_forall_sublist (by
      intro a b hab
      have := hp hab
      have := hle hab
      simp [Bad] at *
      omega))
    simpa [tailBlock, bne, filter_beq] using h.symm

private theorem separated_append {s : Bool} {u v : List ℕ} (hu : Avoid s u) (hv : Avoid s v)
    (hsep : ∀ a ∈ u, ∀ c ∈ v, a < c) : Avoid s (u ++ v) := by
  intro a b c ht
  rcases triple_append.mp ht with h | ⟨hab, hc⟩ | ⟨ha, hbc⟩ | h
  · exact hu h
  · have := hsep _ (hab.subset (by simp : a ∈ [a, b])) _ hc
    cases s <;> simp [Bad] <;> omega
  · have := hsep _ ha _ (hbc.subset (by simp : c ∈ [b, c]))
    cases s <;> simp [Bad] <;> omega
  · exact hv h

private theorem avoid_flip {s : Bool} {v : List ℕ} (hd : v.Nodup) (hv : Avoid s v) :
    Avoid (!s) v := by
  intro a b c ht
  have h := hv ht
  have := hd.sublist ht
  simp at this
  cases s <;> simp [Bad] at * <;> omega

private theorem avoid_block {s : Bool} {H k : ℕ} {v : List ℕ}
    (hl : ∀ x ∈ v, x < H) (hd : v.Nodup) (hv : Avoid s v) :
    Avoid s (H :: tailBlock s H k v) := by
  have hdiff {a b : ℕ} (h : [a, b] <+ v) : a ≠ b := by simpa using hd.sublist h
  have hmem {a b : ℕ} (h : [a, b] <+ v) : a < H ∧ b < H :=
    ⟨hl _ (h.subset (by simp)), hl _ (h.subset (by simp))⟩
  have hp {a b : ℕ} {j : ℕ} (h : [a, b] <+ replicate j H) : a = H ∧ b = H :=
    ⟨eq_of_mem_replicate (h.subset (by simp)), eq_of_mem_replicate (h.subset (by simp))⟩
  have ht {a b c : ℕ} {j : ℕ} (h : [a, b, c] <+ replicate j H) : a = H ∧ b = H ∧ c = H :=
    ⟨eq_of_mem_replicate (h.subset (by simp)), eq_of_mem_replicate (h.subset (by simp)),
      eq_of_mem_replicate (h.subset (by simp))⟩
  cases s with
  | false =>
    change Avoid false (replicate (k + 1) H ++ v)
    intro a b c h
    rcases triple_append.mp h with h | ⟨hab, hc⟩ | ⟨ha, hbc⟩ | h
    · obtain ⟨rfl, rfl, rfl⟩ := ht h
      simp [Bad]
    · obtain ⟨rfl, rfl⟩ := hp hab
      simp [Bad]
    · have := eq_of_mem_replicate ha
      have := hmem hbc
      have := hdiff hbc
      simp [Bad]
      omega
    · exact hv h
  | true =>
    have hfirst : Avoid true (H :: v) := by
      intro a b c h
      obtain h | ⟨rfl, hbc⟩ := cons_sublist_cons'.mp h
      · exact hv h
      · have := hmem hbc
        have := hdiff hbc
        simp [Bad]
        omega
    have hle (a) (ha : a ∈ H :: v) : a ≤ H := by
      obtain rfl | ha := mem_cons.mp ha
      · rfl
      · exact (hl _ ha).le
    change Avoid true ((H :: v) ++ replicate k H)
    intro a b c h
    rcases triple_append.mp h with h | ⟨hab, hc⟩ | ⟨ha, hbc⟩ | h
    · exact hfirst h
    · have := eq_of_mem_replicate hc
      have := hle a (hab.subset (by simp))
      have := hle b (hab.subset (by simp))
      simp [Bad]
      omega
    · obtain ⟨rfl, rfl⟩ := hp hbc
      have := hle a ha
      simp [Bad]
      omega
    · obtain ⟨rfl, rfl, rfl⟩ := ht h
      simp [Bad]

/-- The step from a nonempty prefix to its new maximum is one weak ascent. -/
private theorem ascents_append_max {H : ℕ} (p t : List ℕ) (hp : ∀ x ∈ p, x ≤ H) :
    wordWeakAscents (p ++ H :: t) =
      wordWeakAscents p + (if p = [] then 0 else 1) + wordWeakAscents (H :: t) := by
  induction p using wordWeakAscents.induct with
  | case1 => simp [wordWeakAscents]
  | case2 a => simp [wordWeakAscents, hp a (by simp)]
  | case3 a b p ih =>
    have := ih (fun x hx => hp x (.tail _ hx))
    simpa [wordWeakAscents, Nat.add_assoc] using this

private theorem ascents_max_cons {H : ℕ} {v : List ℕ} (hl : ∀ x ∈ v, x < H) :
    wordWeakAscents (H :: v) = wordWeakAscents v := by
  cases v with
  | nil => rfl
  | cons a v => simp [wordWeakAscents, (hl a (by simp)).not_ge]

private theorem ascents_replicate (H k : ℕ) : wordWeakAscents (H :: replicate k H) = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [replicate_succ, wordWeakAscents, ih, Nat.add_comm]

private theorem ascents_block (s : Bool) (H k : ℕ) (v : List ℕ) (hl : ∀ x ∈ v, x < H) :
    wordWeakAscents (H :: tailBlock s H k v) = k + wordWeakAscents v := by
  cases s with
  | false =>
    induction k with
    | zero => simpa [tailBlock] using ascents_max_cons hl
    | succ k ih =>
      change wordWeakAscents (H :: H :: (replicate k H ++ v)) = _
      simp only [wordWeakAscents, le_refl, ite_true]
      change 1 + wordWeakAscents (H :: tailBlock false H k v) = _
      rw [ih]
      omega
  | true =>
    cases k with
    | zero => simpa [tailBlock] using ascents_max_cons hl
    | succ k =>
      change wordWeakAscents ((H :: v) ++ H :: replicate k H) = _
      have hle (x) (hx : x ∈ H :: v) : x ≤ H := by
        obtain rfl | hx := mem_cons.mp hx
        · rfl
        · exact (hl _ hx).le
      rw [ascents_append_max _ _ hle, ascents_max_cons hl, ascents_replicate]
      simp only [reduceCtorEq, ite_false]
      omega

private theorem ascents_le_append (p t : List ℕ) :
    wordWeakAscents p ≤ wordWeakAscents (p ++ t) := by
  induction p using wordWeakAscents.induct with
  | case1 => exact Nat.zero_le _
  | case2 => exact Nat.zero_le _
  | case3 a b p ih => simpa only [cons_append, wordWeakAscents, Nat.add_le_add_iff_left] using ih

/-- After a permitted maximum, every smaller letter satisfies the weak-ascent bound. -/
private theorem weak_append_max {H : ℕ} {p t : List ℕ} (ht : ∀ x ∈ t, x ≤ H) :
    IsWeakAscentSeq (p ++ H :: t) ↔
      IsWeakAscentSeq p ∧ (p = [] → H = 0) ∧ H ≤ wordWeakAscents p + 1 := by
  constructor
  · intro hw
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · intro h
      have ha := hw.1 (by simp)
      rwa [getElem_append_left h] at ha
    · intro i hi
      have ha := hw.2 i (by simp; omega)
      rwa [getElem_append_left hi, take_append_of_le_length hi.le] at ha
    · rintro rfl
      exact hw.1 (by simp)
    · have ha := hw.2 p.length (by simp)
      rw [getElem_append_right le_rfl] at ha
      simpa only [Nat.sub_self, getElem_cons_zero, take_append_length] using ha
  · rintro ⟨hw, hz, hH⟩
    constructor
    · intro _
      cases p with
      | nil => exact hz rfl
      | cons a p => exact hw.1 (by simp)
    · intro i hi
      by_cases hp : i < p.length
      · simpa only [getElem_append_left hp, take_append_of_le_length hp.le] using hw.2 i hp
      · have hp' : p.length ≤ i := by omega
        rw [getElem_append_right hp']
        have hle (a) (ha : a ∈ H :: t) : a ≤ H := by
          obtain rfl | ha := mem_cons.mp ha
          · rfl
          · exact ht _ ha
        have hx := hle _ (getElem_mem (l := H :: t) (n := i - p.length) (by
          simp only [length_append] at hi
          omega))
        have hpre : p <+: (p ++ H :: t).take i :=
          prefix_take_iff.mpr ⟨prefix_append .., hp'⟩
        obtain ⟨r, hr⟩ := hpre
        rw [← hr]
        have := ascents_le_append p r
        omega

/-- Split an avoider at its first maximum. The smaller letters after it are distinct
and strictly exceed every letter before it, by avoidance of 100, 010 and 120. -/
private theorem split_max {s : Bool} {w : List ℕ} (hw : Avoid s w) (hn : w ≠ []) :
    ∃ p H k v, w = p ++ H :: tailBlock s H k v ∧
      (∀ a ∈ p, a < H) ∧ (∀ a ∈ v, a < H) ∧ (∀ a ∈ p, ∀ b ∈ v, a < b) ∧
      v.Nodup ∧ Avoid s p ∧ Avoid s v := by
  let H := w.max hn
  obtain ⟨p, t, he, hnot⟩ := eq_append_cons_of_mem (max_mem hn)
  change w = p ++ H :: t at he
  change H ∉ p at hnot
  have hmax : ∀ a ∈ p ++ H :: t, a ≤ H := by
    rw [← he]
    exact fun _ ha => le_max_of_mem ha
  rw [he] at hw ⊢
  have hp (a) (ha : a ∈ p) : a < H :=
    lt_of_le_of_ne (hmax a (mem_append_left _ ha)) (fun h => hnot (h ▸ ha))
  have ht (a) (ha : a ∈ t) : a ≤ H := hmax a (by simp [ha])
  let v := t.filter (· != H)
  have hsub : v <+ t := filter_sublist
  have hl (a) (ha : a ∈ v) : a < H := by
    have := mem_filter.mp ha
    exact lt_of_le_of_ne (ht _ this.1) (by simpa using this.2)
  have hb := hw.sub (sublist_append_right ..)
  refine ⟨p, H, t.count H, v, ?_, hp, hl, ?_, pairwise_of_forall_sublist ?_,
    hw.sub (sublist_append_left ..), hb.sub (hsub.cons H)⟩
  · rw [← tail_eq ht hb]
  · intro a ha b hbb
    have hab : [H, b] <+ H :: t := (singleton_sublist.mpr (hsub.subset hbb)).cons_cons H
    have h := hw (triple_append.mpr (.inr (.inr (.inl ⟨ha, hab⟩))))
    have := hp _ ha
    dsimp [Bad] at h
    omega
  · intro a b hab
    have h := hb ((hab.trans hsub).cons_cons H)
    have := hl a (hab.subset (by simp))
    dsimp [Bad] at h
    omega

/-- With enough fuel, recurse on the prefix and put the extra maxima on the opposite side. -/
private def turn (s : Bool) : ℕ → List ℕ → List ℕ
  | 0, w => w
  | fuel + 1, w =>
    if w = [] then [] else
      let H := w.max?.getD 0
      let p := w.takeWhile (· != H)
      let t := (w.dropWhile (· != H)).tail
      turn s fuel p ++ H :: tailBlock (!s) H (t.count H) (t.filter (· != H))

private theorem turn_block {s : Bool} {p v : List ℕ} {H k : ℕ} (fuel : ℕ)
    (hp : ∀ x ∈ p, x < H) (hv : ∀ x ∈ v, x < H) :
    turn s (fuel + 1) (p ++ H :: tailBlock s H k v) =
      turn s fuel p ++ H :: tailBlock (!s) H k v := by
  have hmax : (p ++ H :: tailBlock s H k v).max? = some H := by
    apply max?_eq_some_iff.mpr
    refine ⟨by simp, ?_⟩
    simp only [mem_append, mem_cons, mem_tailBlock]
    grind
  have hp' : ∀ x ∈ p, (x != H) = true := by simpa using fun x hx => (hp x hx).ne
  have hv' : ∀ x ∈ v, (x != H) = true := by simpa using fun x hx => (hv x hx).ne
  have hc : v.count H = 0 := count_eq_zero.mpr (fun hh => (hv H hh).false)
  simp only [turn, append_eq_nil_iff, reduceCtorEq, and_false, ite_false, hmax, Option.getD_some,
    takeWhile_append_of_pos hp', dropWhile_append_of_pos hp']
  cases s <;> simp [tailBlock, count_append, hc, filter_append, filter_eq_self.mpr hv']

private theorem turn_nil (s : Bool) (fuel : ℕ) : turn s fuel [] = [] := by
  cases fuel <;> simp [turn]

private theorem turn_spec (s : Bool) (fuel : ℕ) (w : List ℕ) (hf : w.length ≤ fuel)
    (hw : Avoid s w) (hs : IsWeakAscentSeq w) :
    turn s fuel w ~ w ∧ wordWeakAscents (turn s fuel w) = wordWeakAscents w ∧
      IsWeakAscentSeq (turn s fuel w) ∧ Avoid (!s) (turn s fuel w) ∧
      turn (!s) fuel (turn s fuel w) = w := by
  induction fuel generalizing w with
  | zero =>
    obtain rfl : w = [] := length_eq_zero_iff.mp (by omega)
    refine ⟨.refl _, rfl, hs, ?_, rfl⟩
    intro a b c h
    cases h
  | succ fuel ih =>
    by_cases hn : w = []
    · subst w
      simp [turn_nil, hs, Avoid]
    obtain ⟨p, H, k, v, rfl, hp, hv, hsep, hd, hap, hav⟩ := split_max hw hn
    have hbound (side : Bool) (a) (ha : a ∈ tailBlock side H k v) : a ≤ H := by
      rcases mem_tailBlock.mp ha with ha | ⟨_, rfl⟩
      · exact (hv _ ha).le
      · rfl
    obtain ⟨hsp, hz, hH⟩ := (weak_append_max (hbound s)).mp hs
    have hf' : p.length ≤ fuel := by
      simp only [length_append, length_cons] at hf
      omega
    obtain ⟨hperm, hasc, hweak, havoid, hinv⟩ := ih p hf' hap hsp
    let q := turn s fuel p
    have hq (a) (ha : a ∈ q) : a < H := hp a (hperm.mem_iff.mp ha)
    rw [turn_block fuel hp hv]
    refine ⟨hperm.append ((tailBlock_perm s H k v).cons H), ?_, ?_, ?_, ?_⟩
    · rw [ascents_append_max _ _ (fun a h => (hq a h).le),
        ascents_append_max _ _ (fun a h => (hp a h).le), ascents_block _ _ _ _ hv,
        ascents_block _ _ _ _ hv, hasc]
      have he : q = [] ↔ p = [] := by simpa only [← length_eq_zero_iff] using
          (show q.length = 0 ↔ p.length = 0 by rw [hperm.length_eq])
      simp only [← he, q]
    · apply (weak_append_max (hbound (!s))).mpr
      refine ⟨hweak, fun h => hz ?_, hasc ▸ hH⟩
      apply length_eq_zero_iff.mp
      rw [← hperm.length_eq, h]
      rfl
    · apply separated_append havoid (avoid_block hv hd (avoid_flip hd hav))
      intro a ha b hb
      rcases mem_cons.mp hb with rfl | hb
      · exact hq a ha
      · rcases mem_tailBlock.mp hb with hb | ⟨_, rfl⟩
        · exact hsep _ (hperm.mem_iff.mp ha) _ hb
        · exact hq a ha
    · rw [turn_block fuel hq hv, Bool.not_not, hinv]

end weakAscent_wilf_class162

open weakAscent_wilf_class162

/-- **Weak-ascent Wilf equivalence in Class 162.** For every natural number $n$, the number of
weak ascent sequences of length $n$ avoiding every pattern in $\{010, 100, 101, 120\}$ equals the
number avoiding every pattern in $\{010, 100, 110, 120\}$.

That is, the two sets are WA-Wilf equivalent.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Theorem 8 (`integers-2025-A80-thm-8`). -/
public theorem weakAscent_wilf_class162 (n : ℕ) :
    (weakAscentAvoiders {[0, 1, 0], [1, 0, 0], [1, 0, 1], [1, 2, 0]} n).ncard =
      (weakAscentAvoiders {[0, 1, 0], [1, 0, 0], [1, 1, 0], [1, 2, 0]} n).ncard := by
  have maps (s : Bool) (w : List ℕ) (hw : w ∈ weakAscentAvoiders (patterns s) n) :
      turn s n w ∈ weakAscentAvoiders (patterns (!s)) n ∧ turn (!s) n (turn s n w) = w := by
    obtain ⟨hlen, hweak, hav⟩ := hw
    obtain ⟨hp, _, hs, ha, hi⟩ := turn_spec s n w hlen.le ((avoid_iff ..).mp hav) hweak
    exact ⟨⟨hp.length_eq.trans hlen, hs, (avoid_iff ..).mpr ha⟩, hi⟩
  apply Set.ncard_congr'
  exact {
    toFun := fun w => ⟨turn false n w, (maps false w w.property).1⟩
    invFun := fun w => ⟨turn true n w, (maps true w w.property).1⟩
    left_inv := fun w => Subtype.ext (maps false w w.property).2
    right_inv := fun w => Subtype.ext (maps true w w.property).2 }

end MetaMathlibExt
