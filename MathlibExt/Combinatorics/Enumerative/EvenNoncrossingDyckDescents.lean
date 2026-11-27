/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.DyckPeakDescents
public import MathlibExt.Combinatorics.NoncrossingPartition.Basic
import Mathlib.Data.Finset.Sort
import all MathlibExt.Combinatorics.Enumerative.ColoredCompositionsDyckPolygons

/-!
# Noncrossing partitions and Dyck descents

Scan the vertices from left to right, pushing each new vertex onto a stack. At the last vertex
of a block, its members are on top of the stack: an intervening vertex still on the stack would
interleave that block with one ending later. Emit one up step per vertex and one down step per
pop. Conversely, a descent closes a block by popping its members from the stack.

## References

* Taras Goy and Mark Shattuck, *Determinants of Toeplitz-Hessenberg Matrices with Fuss-Catalan
  Entries*, Journal of Integer Sequences 29 (2026), Article 26.1.2, Lemma 10 (p. 19). We use a stack
  bijection rather than the paper's recursive bijection.
* Martin Klazar, *On abab-Free and abba-Free Set Partitions*, European Journal of Combinatorics
  17 (1996), 53–68, §1 (the noncrossing characterization cited by Goy and Shattuck).
-/

namespace MetaMathlibExt

open DyckStep Finset

/-- On the first `n` vertices, a label is the last vertex of a completed block, or the sentinel
`n` for a vertex still on the stack. The nesting inequality rules out interleaved blocks. -/
private structure EndMap (n : ℕ) where
  label : ℕ → ℕ
  outside : ∀ i, n ≤ i → label i = i
  lower : ∀ i, i ≤ label i
  upper : ∀ i, i < n → label i ≤ n
  closed : ∀ i, label (label i) = label i
  nested : ∀ i j, i < j → j < label i → label j ≤ label i

private theorem EndMap.eq_of_label {n : ℕ} {p q : EndMap n} (h : p.label = q.label) : p = q := by
  cases p; cases q; cases h; rfl

private def EndMap.fiber {n : ℕ} (p : EndMap n) (j : ℕ) : Finset ℕ :=
  (range n).filter fun i => p.label i = j

private theorem mem_fiber {n i j : ℕ} {p : EndMap n} :
    i ∈ p.fiber j ↔ i < n ∧ p.label i = j := by simp [EndMap.fiber]

private def EndMap.stack {n : ℕ} (p : EndMap n) : Finset ℕ := insert n (p.fiber n)

private theorem mem_stack {n i : ℕ} {p : EndMap n} :
    i ∈ p.stack ↔ i ≤ n ∧ p.label i = n := by
  rw [EndMap.stack, mem_insert, mem_fiber]
  have h := p.outside n le_rfl
  constructor
  · rintro (rfl | h')
    · exact ⟨le_rfl, h⟩
    · exact ⟨h'.1.le, h'.2⟩
  · intro h'
    rcases h'.1.eq_or_lt with he | hl
    · exact Or.inl he
    · exact Or.inr ⟨hl, h'.2⟩

private theorem card_stack {n : ℕ} (p : EndMap n) : p.stack.card = (p.fiber n).card + 1 := by
  apply card_insert_of_notMem
  simp [mem_fiber]

/-- Cut off the last vertex, postponing its block's closure. -/
private def EndMap.cut {n : ℕ} (p : EndMap (n + 1)) : EndMap n where
  label i := if i < n then min (p.label i) n else i
  outside i hi := ite_eq_right (not_lt.mpr hi)
  lower i := by
    split_ifs with h
    · exact le_min (p.lower i) h.le
    · rfl
  upper i hi := by simp [hi]
  closed i := by
    by_cases hi : i < n
    · by_cases hj : p.label i < n
      · simp [hi, hj, min_eq_left hj.le, p.closed]
      · simp [hi, min_eq_right (le_of_not_gt hj)]
    · simp [hi]
  nested i j hij hj := by
    have hi : i < n := by by_contra! hi; simp [hi.not_gt] at hj; omega
    simp only [ite_eq_left hi, lt_min_iff] at hj
    simp only [ite_eq_left hi, ite_eq_left hj.2]
    exact min_le_min_right _ (p.nested i j hij hj.1)

/-- A suffix of a stack, when vertices are ordered by increasing position. -/
private def IsStackSuffix (s c : Finset ℕ) : Prop :=
  c ⊆ s ∧ ∀ ⦃i j⦄, i ∈ c → j ∈ s → i < j → j ∈ c

private theorem IsStackSuffix.eq_of_card {s c d : Finset ℕ}
    (hc : IsStackSuffix s c) (hd : IsStackSuffix s d) (hcard : c.card = d.card) : c = d := by
  suffices c ⊆ d ∨ d ⊆ c by
    rcases this with h | h
    · exact eq_of_subset_of_card_le h hcard.ge
    · exact (eq_of_subset_of_card_le h hcard.le).symm
  classical
  by_contra! h
  obtain ⟨i, hi, hid⟩ := not_subset.mp h.1
  obtain ⟨j, hj, hjc⟩ := not_subset.mp h.2
  rcases lt_trichotomy i j with hlt | rfl | hgt
  · exact hjc (hc.2 hi (hd.1 hj) hlt)
  · exact hjc hi
  · exact hid (hd.2 hj (hc.1 hi) hgt)

private theorem exists_stackSuffix (s : Finset ℕ) (k : ℕ) (hk : k ≤ s.card) :
    ∃ c, IsStackSuffix s c ∧ c.card = k := by
  classical
  induction s using Finset.induction_on_min generalizing k with
  | empty =>
    have : k = 0 := by simpa using hk
    subst k
    exact ⟨∅, ⟨Subset.rfl, by simp⟩, rfl⟩
  | @insert a s hmin ih =>
    have ha : a ∉ s := fun h => (hmin a h).false
    by_cases h : k ≤ s.card
    · obtain ⟨c, hc, hcard⟩ := ih k h
      refine ⟨c, ⟨hc.1.trans (subset_insert _ _), ?_⟩, hcard⟩
      intro i j hi hj hij
      rcases mem_insert.mp hj with rfl | hj
      · exact ((hmin i (hc.1 hi)).not_gt hij).elim
      · exact hc.2 hi hj hij
    · exact ⟨insert a s, ⟨Subset.rfl, fun _ _ _ hj _ => hj⟩, by
          rw [card_insert_of_notMem ha] at hk ⊢
          omega⟩

/-- Close a suffix of the stack as the block ending at the new vertex `n`. -/
private def EndMap.close {n : ℕ} (p : EndMap n) (c : Finset ℕ)
    (hc : IsStackSuffix p.stack c) : EndMap (n + 1) where
  label i := if i ∈ p.stack then (if i ∈ c then n else n + 1) else p.label i
  outside i hi := by
    rw [ite_eq_right, p.outside i (by omega)]
    exact fun h => (mem_stack.mp h).1.not_gt (by omega)
  lower i := by
    split_ifs with h hc'
    · exact (mem_stack.mp h).1
    · exact (mem_stack.mp h).1.trans (Nat.le_succ _)
    · exact p.lower i
  upper i hi := by
    have hn : n ∈ p.stack := mem_insert_self _ _
    by_cases hs : i ∈ p.stack
    · split_ifs with h <;> omega
    · rw [ite_eq_right hs]
      have : i < n := (Nat.lt_succ_iff.mp hi).lt_of_ne (fun he => hs (he ▸ hn))
      exact (p.upper _ this).trans (Nat.le_succ _)
  closed i := by
    have hn : n ∈ p.stack := mem_insert_self _ _
    have hn' : n + 1 ∉ p.stack := fun h => by have := (mem_stack.mp h).1; omega
    by_cases hs : i ∈ p.stack
    · by_cases hi : i ∈ c
      · have hnc : n ∈ c := by
          rcases (mem_stack.mp hs).1.eq_or_lt with he | hl
          · exact he ▸ hi
          · exact hc.2 hi hn hl
        simp [hs, hi, hn, hnc]
      · simp [hs, hi, hn', p.outside]
    · have hl : p.label i ∉ p.stack := by
        intro h
        apply hs
        rw [mem_stack] at h ⊢
        exact ⟨(p.lower i).trans h.1, by simpa only [p.closed] using h.2⟩
      simp [hs, hl, p.closed]
  nested i j hij hj := by
    by_cases hs : i ∈ p.stack
    · by_cases hi : i ∈ c
      · simp only [ite_eq_left hs, ite_eq_left hi] at hj ⊢
        by_cases ht : j ∈ p.stack
        · simp [ht, hc.2 hi ht hij]
        · simpa [ht] using p.upper j hj
      · simp only [ite_eq_left hs, ite_eq_right hi] at hj ⊢
        by_cases ht : j ∈ p.stack
        · split_ifs <;> omega
        · simpa [ht] using (p.upper j (Nat.lt_of_succ_le (by
            have hn : n ∈ p.stack := mem_insert_self _ _
            have hne : j ≠ n := fun he => ht (he ▸ hn)
            omega))).trans (Nat.le_succ _)
    · simp only [ite_eq_right hs] at hj ⊢
      have hi : i < n := by
        by_contra! h
        rw [p.outside i h] at hj
        omega
      have hni : p.label i < n := by
        have := p.upper i hi
        by_contra! h
        exact hs (mem_stack.mpr ⟨hi.le, by omega⟩)
      have hle := p.nested i j hij hj
      have hns : j ∉ p.stack := fun h => by have := (mem_stack.mp h).2; omega
      simpa [hns] using hle

private theorem cut_label {n i : ℕ} (p : EndMap (n + 1)) (hi : i < n) :
    p.cut.label i = min (p.label i) n := ite_eq_left hi

private theorem top_label {n i : ℕ} (p : EndMap (n + 1)) :
    i ∈ p.cut.stack ↔ i ≤ n ∧ n ≤ p.label i := by
  rw [mem_stack]
  by_cases hi : i < n
  · rw [cut_label p hi]
    constructor
    · exact fun h => ⟨h.1, by have := h.2; omega⟩
    · exact fun h => ⟨h.1, min_eq_right h.2⟩
  · constructor
    · exact fun h => ⟨h.1, by have := p.lower i; omega⟩
    · exact fun h => ⟨h.1, by rw [p.cut.outside i (by omega)]; omega⟩

private theorem fiber_isStackSuffix {n : ℕ} (p : EndMap (n + 1)) :
    IsStackSuffix p.cut.stack (p.fiber n) := by
  refine ⟨fun i hi => ?_, fun i j hi hj hij => ?_⟩
  · rw [mem_fiber] at hi
    exact (top_label p).2 ⟨by omega, by omega⟩
  · rw [mem_fiber] at hi ⊢
    rw [top_label] at hj
    refine ⟨by omega, ?_⟩
    rcases hj.1.eq_or_lt with rfl | hlt
    · simpa only [hi.2] using p.closed i
    · apply le_antisymm _ hj.2
      simpa only [hi.2] using p.nested i j hij (by rw [hi.2]; exact hlt)

private theorem close_cut {n : ℕ} (p : EndMap (n + 1)) :
    p.cut.close (p.fiber n) (fiber_isStackSuffix p) = p := by
  apply EndMap.eq_of_label
  funext i
  change (if i ∈ p.cut.stack then _ else _) = _
  by_cases hi : i < n + 1
  · simp only [top_label, mem_fiber]
    by_cases h : p.label i < n
    · have hi' := (p.lower i).trans_lt h
      simp [not_le.mpr h, cut_label p hi', min_eq_left h.le]
    · have hu := p.upper i hi
      rcases eq_or_lt_of_le (le_of_not_gt h) with he | he
      · simp [← he, Nat.lt_succ_iff.mp hi, hi]
      · simp [Nat.lt_succ_iff.mp hi, show p.label i = n + 1 by omega]
  · rw [ite_eq_right, p.cut.outside i (by omega), p.outside i (by omega)]
    exact fun h => by have := (top_label p).1 h; omega

private theorem cut_close {n : ℕ} (p : EndMap n) (c : Finset ℕ) (hc : IsStackSuffix p.stack c) :
    (p.close c hc).cut = p := by
  apply EndMap.eq_of_label
  funext i
  by_cases hi : i < n
  · rw [cut_label _ hi]
    change min (if i ∈ p.stack then _ else _) n = _
    by_cases hs : i ∈ p.stack
    · rw [ite_eq_left hs, (mem_stack.mp hs).2]
      split_ifs <;> omega
    · simp [hs, min_eq_left (p.upper i hi)]
  · rw [p.outside i (by omega), EndMap.outside _ i (by omega)]

private theorem fiber_close {n : ℕ} (p : EndMap n) (c : Finset ℕ) (hc : IsStackSuffix p.stack c) :
    (p.close c hc).fiber n = c := by
  ext i
  rw [mem_fiber]
  change (i < n + 1 ∧ (if i ∈ p.stack then _ else _) = n) ↔ i ∈ c
  by_cases hs : i ∈ p.stack
  · have hi := (mem_stack.mp hs).1
    simp [hs, hi]
  · have hnc : i ∉ c := fun h => hs (hc.1 h)
    simp [hs, hnc, ← mem_stack]

private theorem pending_close {n : ℕ} (p : EndMap n) (c : Finset ℕ)
    (hc : IsStackSuffix p.stack c) : (p.close c hc).fiber (n + 1) = p.stack \ c := by
  ext i
  rw [mem_fiber, mem_sdiff]
  change (i < n + 1 ∧ (if i ∈ p.stack then _ else _) = n + 1) ↔ _
  by_cases hs : i ∈ p.stack
  · have hi := (mem_stack.mp hs).1
    simp [hs, hi]
  · have h : i < n + 1 → p.label i ≤ n := by
      intro hi
      rcases (Nat.lt_succ_iff.mp hi).eq_or_lt with he | hl
      · subst i; exact (p.outside n le_rfl).le
      · exact p.upper i hl
    rw [ite_eq_right hs]
    simp only [hs, false_and, iff_false, not_and]
    exact fun hi he => by have := h hi; omega

private theorem old_fiber {n j : ℕ} (p : EndMap (n + 1)) (hj : j < n) :
    p.fiber j = p.cut.fiber j := by
  ext i
  simp only [mem_fiber]
  constructor
  · rintro ⟨_, h⟩
    have hi : i < n := (p.lower i).trans_lt (h ▸ hj)
    exact ⟨hi, by rw [cut_label _ hi, h, min_eq_left hj.le]⟩
  · rintro ⟨hi, h⟩
    rw [cut_label _ hi] at h
    exact ⟨by omega, by omega⟩

private theorem pending_card {n : ℕ} (p : EndMap (n + 1)) :
    (p.fiber (n + 1)).card + (p.fiber n).card = (p.cut.fiber n).card + 1 := by
  have hs := fiber_isStackSuffix p
  nth_rw 1 [← close_cut p]
  rw [pending_close, card_sdiff_of_subset hs.1, card_stack]
  have := card_le_card hs.1
  rw [card_stack] at this
  omega

private def PrefixOK (l : List DyckStep) : Prop :=
  ∀ i, (l.take i).count D ≤ (l.take i).count U

private def appendDescent (l : List DyckStep) (k : ℕ) : List DyckStep :=
  l ++ U :: List.replicate k D

private theorem count_U_appendDescent (l : List DyckStep) (k : ℕ) :
    (appendDescent l k).count U = l.count U + 1 := by
  simp [appendDescent, List.count_append, List.count_replicate]

private theorem count_D_appendDescent (l : List DyckStep) (k : ℕ) :
    (appendDescent l k).count D = l.count D + k := by
  simp [appendDescent, List.count_append]

open choose_mul_coloredDyckPathCount_eq (StrictPath strict_block)

-- Prepending one up step shifts weak prefix balance to strict prefix balance.
private theorem prefixOK_iff_strictPath (l : List DyckStep) :
    PrefixOK l ↔ StrictPath (U :: l) := by
  constructor
  · intro h
    rintro (_ | i) hi _
    · omega
    · simpa [List.count_cons] using Nat.lt_succ_of_le (h i)
  · intro h i
    have htake : l.take (min i l.length) = l.take i := by
      rw [← List.take_take, List.take_length]
    have ht := h (min i l.length + 1) (Nat.succ_pos _) (by simp)
    simp [htake] at ht
    omega

private theorem prefixOK_appendDescent_iff (l : List DyckStep) (k : ℕ) :
    PrefixOK (appendDescent l k) ↔ PrefixOK l ∧ l.count D + k ≤ l.count U + 1 := by
  simp only [prefixOK_iff_strictPath]
  change StrictPath ((U :: l) ++ (List.replicate 1 U ++ List.replicate k D)) ↔ _
  rw [strict_block _ Nat.one_pos]
  refine and_congr_right fun _ => ?_
  simp

private theorem prefixOK_appendDescent {l : List DyckStep} {k : ℕ}
    (hl : PrefixOK l) (hk : l.count D + k ≤ l.count U + 1) :
    PrefixOK (appendDescent l k) :=
  (prefixOK_appendDescent_iff l k).2 ⟨hl, hk⟩

private theorem prefixOK_of_appendDescent {l : List DyckStep} {k : ℕ}
    (h : PrefixOK (appendDescent l k)) : PrefixOK l :=
  ((prefixOK_appendDescent_iff l k).1 h).1

private theorem exists_appendDescent (l : List DyckStep) (h : 0 < l.count U) :
    ∃ p k, l = appendDescent p k := by
  induction l using List.reverseRecOn with
  | nil => simp at h
  | append_singleton l s ih =>
    cases s with
    | U => exact ⟨l, 0, rfl⟩
    | D =>
      obtain ⟨p, k, rfl⟩ := ih (by simpa [List.count_append] using h)
      exact ⟨p, k + 1, by simp [appendDescent, List.replicate_succ', List.append_assoc]⟩

private theorem takeWhile_D_append_U (l r : List DyckStep) :
    (l ++ U :: r).takeWhile (· == D) = l.takeWhile (· == D) := by
  induction l with
  | nil => rfl
  | cons s l ih => cases s <;> simp [ih]

private theorem appendDescent_inj {p q : List DyckStep} {k m : ℕ}
    (h : appendDescent p k = appendDescent q m) : p = q ∧ k = m := by
  have hv (l : List DyckStep) (j : ℕ) :
      ((appendDescent l j).reverse.takeWhile (· == D)).length = j := by
    simp [appendDescent, List.reverse_append, List.reverse_cons, List.reverse_replicate,
      List.append_assoc]
  have hk : k = m := (hv p k).symm.trans ((congrArg (fun l : List DyckStep =>
    (l.reverse.takeWhile (· == D)).length) h).trans (hv q m))
  subst m
  exact ⟨List.append_cancel_right h, rfl⟩

private theorem peak_appendDescent {l : List DyckStep} {k j : ℕ} :
    j ∈ dyckPeakDescents (appendDescent l k) ↔
      j ∈ dyckPeakDescents l ∨ 0 < k ∧ j = k := by
  simp only [dyckPeakDescents, List.mem_map, List.mem_filter, List.mem_range,
    decide_eq_true_eq]
  have hget (i : ℕ) (hi : i < l.length) : (appendDescent l k)[i]? = l[i]? :=
    List.getElem?_append_left hi
  have hskip (i : ℕ) (hi : l.length ≤ i) :
      (appendDescent l k)[i]? = (U :: List.replicate k D)[i - l.length]? :=
    List.getElem?_append_right hi
  have hlen : (appendDescent l k).length = l.length + (k + 1) := by simp [appendDescent]
  have hrun (i : ℕ) (hi : i + 1 ≤ l.length) :
      (((appendDescent l k).drop (i + 1)).takeWhile (· == D)).length =
        ((l.drop (i + 1)).takeWhile (· == D)).length := by
    simp [appendDescent, List.drop_append, show i + 1 - l.length = 0 by omega,
      takeWhile_D_append_U]
  have hhead : (appendDescent l k)[l.length]? = some U := by simp [hskip]
  have htail : (appendDescent l k)[l.length + 1]? = some D ↔ 0 < k := by
    cases k <;> simp [hskip]
  have hlast : (((appendDescent l k).drop (l.length + 1)).takeWhile (· == D)).length = k := by
    simp [appendDescent, List.drop_append, List.drop_of_length_le]
  constructor
  · rintro ⟨i, ⟨hi, hu, hd⟩, rfl⟩
    rcases lt_trichotomy i l.length with hlt | rfl | hgt
    · have hlt' : i + 1 < l.length := by
        by_contra! hh
        have he : i + 1 = l.length := by omega
        rw [he, hhead] at hd
        cases hd
      left
      exact ⟨i, ⟨hlt, (hget i hlt).symm.trans hu, (hget _ hlt').symm.trans hd⟩,
        (hrun i hlt'.le).symm⟩
    · exact Or.inr ⟨htail.mp hd, hlast⟩
    · have hi' : i - l.length ≠ 0 := by omega
      rw [hskip i hgt.le] at hu
      cases he : i - l.length with
      | zero => exact (hi' he).elim
      | succ m => simp [he, List.getElem?_replicate] at hu
  · rintro (⟨i, ⟨hi, hu, hd⟩, rfl⟩ | ⟨hk, rfl⟩)
    · have hlt : i + 1 < l.length := List.getElem?_eq_some_iff.mp hd |>.choose
      exact ⟨i, ⟨by omega, (hget i hi).trans hu, (hget _ hlt).trans hd⟩, hrun i hlt.le⟩
    · exact ⟨l.length, ⟨by omega, hhead, htail.mpr hk⟩, hlast⟩

private theorem even_peak_appendDescent (l : List DyckStep) (k : ℕ) :
    (∀ j ∈ dyckPeakDescents (appendDescent l k), Even j) ↔
      (∀ j ∈ dyckPeakDescents l, Even j) ∧ Even k := by
  constructor
  · intro h
    refine ⟨fun j hj => h j (peak_appendDescent.mpr (Or.inl hj)), ?_⟩
    cases k with
    | zero => exact ⟨0, rfl⟩
    | succ k => exact h _ (peak_appendDescent.mpr (Or.inr ⟨Nat.succ_pos _, rfl⟩))
  · rintro ⟨h, hk⟩ j hj
    rcases peak_appendDescent.mp hj with h' | ⟨_, rfl⟩
    · exact h j h'
    · exact hk

/-- Emit one up step per vertex and a descent when its block closes. -/
private def EndMap.encode : {n : ℕ} → EndMap n → List DyckStep
  | 0, _ => []
  | n + 1, p => appendDescent (EndMap.encode p.cut) (p.fiber n).card

private theorem encode_spec {n : ℕ} (p : EndMap n) :
    p.encode.count U = n ∧ p.encode.count D + (p.fiber n).card = n ∧ PrefixOK p.encode := by
  induction n with
  | zero => simp [EndMap.encode, EndMap.fiber, PrefixOK]
  | succ n ih =>
    obtain ⟨hu, hd, hp⟩ := ih p.cut
    have hs := pending_card p
    rw [EndMap.encode, count_U_appendDescent, count_D_appendDescent, hu]
    exact ⟨rfl, by omega, prefixOK_appendDescent hp (by omega)⟩

private theorem encode_even {n : ℕ} (p : EndMap n) :
    (∀ j ∈ dyckPeakDescents p.encode, Even j) ↔ ∀ j < n, Even (p.fiber j).card := by
  induction n with
  | zero => simp [EndMap.encode, dyckPeakDescents]
  | succ n ih =>
    rw [EndMap.encode, even_peak_appendDescent, ih]
    constructor
    · rintro ⟨h, hn⟩ j hj
      rcases (Nat.lt_succ_iff.mp hj).eq_or_lt with rfl | hlt
      · exact hn
      · rw [old_fiber p hlt]; exact h j hlt
    · exact fun h => ⟨fun j hj => old_fiber p hj ▸ h j (by omega), h n (by omega)⟩

private theorem encode_injective (n : ℕ) : Function.Injective (@EndMap.encode n) := by
  induction n with
  | zero =>
    intro p q _
    exact EndMap.eq_of_label (funext fun i => (p.outside i (Nat.zero_le i)).trans
      (q.outside i (Nat.zero_le i)).symm)
  | succ n ih =>
    intro p q h
    have he := appendDescent_inj h
    have hc := ih he.1
    have hf : p.fiber n = q.fiber n := IsStackSuffix.eq_of_card
      (fiber_isStackSuffix p) (hc ▸ fiber_isStackSuffix q) he.2
    rw [← close_cut p, ← close_cut q]
    congr

private theorem exists_encode {n : ℕ} {l : List DyckStep} (hu : l.count U = n)
    (hp : PrefixOK l) : ∃ p : EndMap n, p.encode = l := by
  induction n generalizing l with
  | zero =>
    have hd := hp l.length
    rw [List.take_of_length_le le_rfl, hu] at hd
    have hl : l = [] := by
      cases l with
      | nil => rfl
      | cons s r => cases s <;> simp_all
    exact ⟨⟨id, fun _ _ => rfl, fun _ => le_rfl, by omega, fun _ => rfl,
      fun _ _ hij hji => (Nat.not_lt_of_ge hij.le hji).elim⟩, hl.symm⟩
  | succ n ih =>
    obtain ⟨r, k, rfl⟩ := exists_appendDescent l (by omega)
    have hru : r.count U = n := by rw [count_U_appendDescent] at hu; omega
    obtain ⟨p, rfl⟩ := ih hru (prefixOK_of_appendDescent hp)
    have hb := hp (appendDescent p.encode k).length
    rw [List.take_of_length_le le_rfl, count_U_appendDescent, count_D_appendDescent] at hb
    have hcard : k ≤ p.stack.card := by
      rw [card_stack]
      have h := (encode_spec p).2.1
      omega
    obtain ⟨c, hc, hck⟩ := exists_stackSuffix p.stack k hcard
    refine ⟨p.close c hc, ?_⟩
    rw [EndMap.encode, cut_close, fiber_close, hck]

open NoncrossingPartition in
private def blockEnd {n : ℕ} (p : _root_.NoncrossingPartition n) (i : Fin n) : Fin n :=
  (p.val.part i).max' ⟨i, mem_part_self p.val i⟩

private theorem blockEnd_mem {n : ℕ} (p : _root_.NoncrossingPartition n) (i : Fin n) :
    blockEnd p i ∈ p.val.part i := Finset.max'_mem _ _

open NoncrossingPartition in
private theorem blockEnd_eq_iff {n : ℕ} (p : _root_.NoncrossingPartition n) (a b : Fin n) :
    blockEnd p a = blockEnd p b ↔ p.val.part a = p.val.part b := by
  constructor
  · intro h
    exact p.val.eq_of_mem_parts (part_mem_parts _ _) (part_mem_parts _ _)
      (blockEnd_mem p a) (h ▸ blockEnd_mem p b)
  · intro h
    unfold blockEnd
    congr

open NoncrossingPartition in
private def ofPartition {n : ℕ} (p : _root_.NoncrossingPartition n) : EndMap n where
  label i := if hi : i < n then ↑(blockEnd p ⟨i, hi⟩) else i
  outside i hi := dite_eq_right hi.not_gt
  lower i := by
    split_ifs with hi
    · exact (p.val.part ⟨i, hi⟩).le_max' _ (mem_part_self p.val ⟨i, hi⟩)
    · rfl
  upper i hi := by simp only [dite_eq_left hi]; exact (blockEnd p ⟨i, hi⟩).isLt.le
  closed i := by
    by_cases hi : i < n
    · rw [dite_eq_left hi, dite_eq_left (blockEnd p ⟨i, hi⟩).isLt]
      have hb := p.val.part_eq_of_mem (part_mem_parts p.val ⟨i, hi⟩) (blockEnd_mem p ⟨i, hi⟩)
      exact congrArg Fin.val ((blockEnd_eq_iff _ _ _).2 hb)
    · simp [hi]
  nested i j hij hj := by
    by_cases hi : i < n
    · rw [dite_eq_left hi] at hj ⊢
      let a : Fin n := ⟨i, hi⟩
      let b : Fin n := ⟨j, hj.trans (blockEnd p a).isLt⟩
      rw [dite_eq_left b.isLt]
      by_contra! hlt
      have ha := p.val.part_eq_of_mem (part_mem_parts p.val a) (blockEnd_mem p a)
      have hb := p.val.part_eq_of_mem (part_mem_parts p.val b) (blockEnd_mem p b)
      apply p.property
      exact ⟨a, b, blockEnd p a, blockEnd p b, hij, hj, hlt, ha.symm, hb.symm,
        fun h => hlt.ne (congrArg Fin.val ((blockEnd_eq_iff _ _ _).2 h))⟩
    · rw [dite_eq_right hi] at hj
      omega

private theorem ofPartition_apply {n : ℕ} (p : _root_.NoncrossingPartition n) (i : Fin n) :
    (ofPartition p).label i = (blockEnd p i : ℕ) := dite_eq_left i.isLt

private theorem ofPartition_pending {n : ℕ} (p : _root_.NoncrossingPartition n) :
    (ofPartition p).fiber n = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro i hi
  obtain ⟨h, he⟩ := mem_fiber.mp hi
  have hl := ofPartition_apply p (⟨i, h⟩ : Fin n)
  have := (blockEnd p ⟨i, h⟩).isLt
  change (ofPartition p).label i = _ at hl
  omega

private theorem label_eq_iff_part_eq {n : ℕ} (p : _root_.NoncrossingPartition n) (a b : Fin n) :
    (ofPartition p).label a = (ofPartition p).label b ↔ p.val.part a = p.val.part b := by
  rw [ofPartition_apply, ofPartition_apply, ← Fin.ext_iff, blockEnd_eq_iff]

open NoncrossingPartition in
private theorem partition_ext {n : ℕ} {p q : _root_.NoncrossingPartition n}
    (h : ∀ i : Fin n, p.val.part i = q.val.part i) : p = q := by
  apply NoncrossingPartition.ext
  apply Finpartition.ext
  ext b
  constructor
  · intro hb
    obtain ⟨a, ha⟩ := p.val.nonempty_of_mem_parts hb
    rw [← p.val.part_eq_of_mem hb ha, h]
    exact part_mem_parts q.val a
  · intro hb
    obtain ⟨a, ha⟩ := q.val.nonempty_of_mem_parts hb
    rw [← q.val.part_eq_of_mem hb ha, ← h]
    exact part_mem_parts p.val a

open NoncrossingPartition in
private theorem ofPartition_injective (n : ℕ) : Function.Injective (@ofPartition n) := by
  intro p q h
  apply partition_ext
  intro i
  ext j
  rw [p.val.part_eq_iff_mem (part_mem_parts _ _ ) |>.symm,
    q.val.part_eq_iff_mem (part_mem_parts _ _ ) |>.symm,
    ← label_eq_iff_part_eq, ← label_eq_iff_part_eq, h]

open NoncrossingPartition in
private theorem fiber_eq_map_part {n : ℕ} (p : _root_.NoncrossingPartition n) (a : Fin n) :
    (ofPartition p).fiber (ofPartition p |>.label a) =
      (p.val.part a).map ⟨Fin.val, Fin.val_injective⟩ := by
  ext i
  rw [mem_fiber, mem_map]
  constructor
  · rintro ⟨hi, he⟩
    exact ⟨⟨i, hi⟩, (p.val.part_eq_iff_mem (part_mem_parts _ _)).1
        ((label_eq_iff_part_eq p ⟨i, hi⟩ a).1 he), rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b.isLt, (label_eq_iff_part_eq _ _ _).2 (p.val.part_eq_of_mem (part_mem_parts _ _) hb)⟩

open NoncrossingPartition in
private theorem even_fibers_iff {n : ℕ} (p : _root_.NoncrossingPartition n) :
    (∀ j < n, Even ((ofPartition p).fiber j).card) ↔ ∀ b ∈ p.val.parts, Even b.card := by
  constructor
  · intro h b hb
    obtain ⟨i, hi⟩ := p.val.nonempty_of_mem_parts hb
    have hi' := (blockEnd p i).isLt
    rw [← ofPartition_apply] at hi'
    simpa [fiber_eq_map_part, p.val.part_eq_of_mem hb hi] using h _ hi'
  · intro h j hj
    rcases (ofPartition p).fiber j |>.eq_empty_or_nonempty with he | ⟨i, hi⟩
    · simp [he]
    · obtain ⟨hi, he⟩ := mem_fiber.mp hi
      let a : Fin n := ⟨i, hi⟩
      change (ofPartition p).label a = j at he
      rw [← he, fiber_eq_map_part, card_map]
      exact h _ (part_mem_parts _ _)

private def labelSetoid {n : ℕ} (p : EndMap n) : Setoid (Fin n) where
  r a b := p.label a = p.label b
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

private instance {n : ℕ} (p : EndMap n) : DecidableRel (labelSetoid p).r :=
  fun a b => inferInstanceAs (Decidable (p.label a = p.label b))

private def labelPartition {n : ℕ} (p : EndMap n) : NoncrossingPartition.SetPartition n :=
  Finpartition.ofSetoid (labelSetoid p)

open NoncrossingPartition in
private theorem part_eq_iff_label_eq {n : ℕ} (p : EndMap n) (a b : Fin n) :
    (labelPartition p).part a = (labelPartition p).part b ↔ p.label a = p.label b :=
  ((labelPartition p).part_eq_iff_mem (part_mem_parts _ _)).trans
    Finpartition.mem_part_ofSetoid_iff_rel |>.trans eq_comm

open NoncrossingPartition in
private def toPartition {n : ℕ} (p : EndMap n) : _root_.NoncrossingPartition n :=
  ⟨labelPartition p, by
    rintro ⟨a, b, c, d, hab, hbc, hcd, hac, hbd, hne⟩
    have h₁ := (part_eq_iff_label_eq p a c).1 hac
    have h₂ := (part_eq_iff_label_eq p b d).1 hbd
    have hc := p.lower c
    have hd := p.lower d
    have h₃ := p.nested a b hab ((show (b : ℕ) < c from hbc).trans_le (h₁ ▸ hc))
    have h₄ := p.nested b c hbc ((show (c : ℕ) < d from hcd).trans_le (h₂ ▸ hd))
    apply hne
    exact (part_eq_iff_label_eq p a b).2 (by omega)⟩

private theorem ofPartition_toPartition {n : ℕ} (p : EndMap n) (h : p.fiber n = ∅) :
    ofPartition (toPartition p) = p := by
  apply EndMap.eq_of_label
  funext i
  by_cases hi : i < n
  · let a : Fin n := ⟨i, hi⟩
    have hp : p.label i < n := by
      have hu := p.upper i hi
      by_contra! hl
      have hm : i ∈ p.fiber n := mem_fiber.mpr ⟨hi, by omega⟩
      simp [h] at hm
    let b : Fin n := ⟨p.label i, hp⟩
    let c := blockEnd (toPartition p) a
    have hb : b ∈ (labelPartition p).part a :=
      Finpartition.mem_part_ofSetoid_iff_rel.mpr (p.closed i).symm
    have hbc : b ≤ c := (labelPartition p |>.part a).le_max' _ hb
    have hc : p.label a = p.label c :=
      Finpartition.mem_part_ofSetoid_iff_rel.mp (blockEnd_mem (toPartition p) a)
    have hcl := p.lower c
    change (ofPartition (toPartition p)).label a = _
    rw [ofPartition_apply]
    change (c : ℕ) = p.label i
    exact le_antisymm (hcl.trans_eq hc.symm) hbc
  · rw [(ofPartition (toPartition p)).outside i (by omega), p.outside i (by omega)]

private theorem equiv_even (n : ℕ) : Nonempty
    ({P : _root_.NoncrossingPartition n // ∀ B ∈ P.val.parts, Even B.card} ≃
      {p : DyckWord // p.semilength = n ∧ ∀ j ∈ dyckPeakDescents p.toList, Even j}) := by
  classical
  let f : {P : _root_.NoncrossingPartition n // ∀ B ∈ P.val.parts, Even B.card} →
      {p : DyckWord // p.semilength = n ∧ ∀ j ∈ dyckPeakDescents p.toList, Even j} := fun P => by
    have hs := encode_spec (ofPartition P.val)
    have hd := hs.2.1
    rw [ofPartition_pending, card_empty, add_zero] at hd
    exact ⟨⟨_, hs.1.trans hd.symm, hs.2.2⟩, hs.1,
      (encode_even _).2 ((even_fibers_iff _).2 P.property)⟩
  refine ⟨Equiv.ofBijective f ⟨?_, ?_⟩⟩
  · intro p q h
    exact Subtype.ext (ofPartition_injective n (encode_injective n
      (congrArg (fun d => d.val.toList) h)))
  · rintro ⟨l, hu, he⟩
    obtain ⟨p, hp⟩ := exists_encode hu l.count_D_le_count_U
    have hf : p.fiber n = ∅ := by
      apply card_eq_zero.mp
      have h := (encode_spec p).2.1
      rw [hp, ← l.count_U_eq_count_D] at h
      change l.toList.count U = n at hu
      omega
    let P := toPartition p
    have hP : ofPartition P = p := ofPartition_toPartition p hf
    have hPE : ∀ B ∈ P.val.parts, Even B.card := by
      apply (even_fibers_iff _).1
      rw [hP, ← encode_even, hp]
      exact he
    refine ⟨⟨P, hPE⟩, Subtype.ext (DyckWord.ext ?_)⟩
    change (ofPartition P).encode = l.toList
    rw [hP, hp]

/-- **Even noncrossing partitions and Dyck paths with even descents.** For every natural number
$n$, there is a bijection between the noncrossing partitions of $\{0, \dots, 2n - 1\}$ all of
whose blocks have even size and the Dyck paths of semilength $2n$ all of whose descents have even
length. Here the descents of a Dyck path are the lengths of its maximal runs of down steps, one
for each peak $UD$: the run of down steps starting at the $D$ of that peak.

Source: Taras Goy and Mark Shattuck, *Determinants of Toeplitz-Hessenberg Matrices with
Fuss-Catalan Entries*, Journal of Integer Sequences 29 (2026), Article 26.1.2, Lemma 10
(`jis-2026-26.1.2-lem-10`). -/
public theorem nonempty_equiv_evenNoncrossing_evenDescentDyck (n : ℕ) :
    Nonempty
      ({P : _root_.NoncrossingPartition (2 * n) // ∀ B ∈ P.val.parts, Even B.card} ≃
        {p : DyckWord // p.semilength = 2 * n ∧ ∀ j ∈ dyckPeakDescents p.toList, Even j}) :=
  equiv_even (2 * n)

end MetaMathlibExt
