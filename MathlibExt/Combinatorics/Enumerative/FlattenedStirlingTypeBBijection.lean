/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.FlattenedStirlingTypeBWord
import Mathlib.Data.List.TakeWhile
import MathlibExt.Combinatorics.Enumerative.FlattenedStirlingTypeBRuns

/-!
# The bijection between type B partitions and flattened Stirling permutations

For every natural number `n`, the word map restricted to type B set partitions of `[-n, n]`
is a bijection onto the flattened Stirling permutations of order `n + 1`. The case `n = 0`
is included: the only block is `{0}` and its word is `11`.

Read a flattened Stirling word from right to left. Its last letter delimits a wrapped positive
part; the maximal segment of larger letters immediately to its left comes from the negative
part. These segments are sorted pairs, because an internal descent would start a run with a
larger leader than the later descent to the label. The Stirling condition prevents a pair from
straddling either cut. Removing the block leaves a shorter prefix, whose last letter is
strictly smaller. The cuts are unique, and unshifting the letters reconstructs the partition.

## References

* Adam Buck, Jennifer Elder, Azia A. Figueroa, Pamela E. Harris, Kimberly J. Harry, and
  Anthony Simpson, *Flattened Stirling Permutations*, INTEGERS 24 (2024), Article A104,
  pp. 1–20, Proposition 1 and Theorem 3.
* V. È. Adler, *Set partitions and integrable hierarchies*, Teoret. Mat. Fiz. 187 (2016),
  no. 3, pp. 455–486, §4 (canonical representation of type B partitions).

The forward direction uses `typeBFlattenedWord_mem_flattenedStirling` from
`FlattenedStirlingTypeBWord`. For the inverse, the block facts from `FlattenedStirlingTypeBRuns`
include `IsTypeBSetPartition.part_neg`, `IsTypeBSetPartition.exists_mem_adlerBlockLabels` and
`eq_of_part_eq_of_mem_adlerBlockLabels`. The indexed word agrees with its word list by
`IsTypeBSetPartition.length_typeBFlattenedWordList` and `ofFn_typeBFlattenedWord_of_length_eq`.
-/

namespace MetaMathlibExt

/-! ### Conditions for parsing a reversed word -/

private def Twice (l : List ℕ) : Prop :=
  ∀ a, l.count a = 0 ∨ l.count a = 2

private def StirlingBetween (l : List ℕ) : Prop :=
  ∀ (u : List ℕ) (a : ℕ) (v t : List ℕ), l = u ++ a :: v ++ a :: t → ∀ x ∈ v, a < x

private def ReverseFlat (l : List ℕ) : Prop :=
  ∀ (i j a b c d : ℕ), i < j → l[i]? = some a → l[i + 1]? = some b →
    l[j]? = some c → l[j + 1]? = some d → a < b → c < d → c ≤ a

private theorem StirlingBetween.factor {u l t : List ℕ} (h : StirlingBetween (u ++ l ++ t)) :
    StirlingBetween l := by
  intro v a w z e x hx
  exact h (u ++ v) a w (z ++ t) (by simp [e, List.append_assoc]) x hx

private theorem StirlingBetween.separates {l r : List ℕ} {a x : ℕ}
    (h : StirlingBetween (l ++ a :: r)) (ha : a ≤ x) (hl : x ∈ l) : x ∉ r := by
  intro hr
  obtain ⟨u, v, rfl⟩ := List.mem_iff_append.mp hl
  obtain ⟨s, t, rfl⟩ := List.mem_iff_append.mp hr
  exact (h u x (v ++ a :: s) t (by simp [List.append_assoc]) a (by simp)).not_ge ha

private theorem ReverseFlat.factor {u l t : List ℕ} (h : ReverseFlat (u ++ l ++ t)) :
    ReverseFlat l := by
  intro i j a b c d hij ha hb hc hd hab hcd
  have lift {k x : ℕ} (hk : l[k]? = some x) : (u ++ l ++ t)[u.length + k]? = some x := by
    have hlt : k < l.length := by
      by_contra! hle
      simp [List.getElem?_eq_none hle] at hk
    rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      List.getElem?_append_left hlt]
    exact hk
  exact h (u.length + i) (u.length + j) a b c d (by omega) (lift ha)
    (by simpa only [Nat.add_assoc] using lift hb) (lift hc)
    (by simpa only [Nat.add_assoc] using lift hd) hab hcd

private theorem ReverseFlat.sorted_after {a : ℕ} {l : List ℕ}
    (h : ReverseFlat (a :: l)) (hgt : ∀ x ∈ l, a < x) : l.SortedGE := by
  apply List.sortedGE_iff_isChain.mpr
  apply List.isChain_iff_getElem.mpr
  intro i hi
  have hi' : i < l.length := by omega
  have h0 : 0 < l.length := by omega
  by_contra! hlt
  have hfirst : a < l[0] := hgt _ (List.getElem_mem h0)
  have hlater : a < l[i] := hgt _ (List.getElem_mem hi')
  have hle := h 0 (i + 1) a l[0] l[i] l[i + 1] (by omega)
    (by simp) (by simp [List.getElem?_eq_getElem h0])
    (by simp [List.getElem?_eq_getElem hi']) (by simp [List.getElem?_eq_getElem hi]) hfirst hlt
  omega

private theorem Twice.left {l r : List ℕ} (h : Twice (l ++ r)) (hd : ∀ x ∈ l, x ∉ r) :
    Twice l := by
  intro x
  by_cases hx : x ∈ l
  · simpa [List.count_append, List.count_eq_zero.mpr (hd x hx)] using h x
  · exact Or.inl (List.count_eq_zero.mpr hx)

private theorem Twice.right {l r : List ℕ} (h : Twice (l ++ r)) (hd : ∀ x ∈ l, x ∉ r) :
    Twice r := by
  intro x
  by_cases hx : x ∈ r
  · have hxl : x ∉ l := fun hmem => hd x hmem hx
    simpa [List.count_append, List.count_eq_zero.mpr hxl] using h x
  · exact Or.inl (List.count_eq_zero.mpr hx)

/-! ### The canonical block decomposition -/

private theorem mem_doubled {s : Finset ℕ} {x : ℕ} : x ∈ doubledWord s ↔ x ∈ s := by
  rw [← List.count_pos_iff, count_doubledWord]
  split <;> simp_all

private theorem eq_doubled_reverse {l : List ℕ} (hs : l.SortedGE) (ht : Twice l) :
    l = (doubledWord l.toFinset).reverse := by
  apply List.Perm.eq_of_sortedGE hs (sortedLE_doubledWord _).reverse
  apply List.perm_iff_count.mpr
  intro a
  simp only [List.count_reverse, count_doubledWord, List.mem_toFinset]
  by_cases ha : a ∈ l
  · exact by simpa [ha] using (ht a).resolve_left (fun e => List.count_eq_zero.mp e ha)
  · rw [ite_eq_right ha, List.count_eq_zero.mpr ha]

-- In a right-to-left block, the first and second copies of the label surround the positive
-- pairs; the negative pairs follow the second copy.
private structure WordBlock where
  label : ℕ
  pos : Finset ℕ
  neg : Finset ℕ
  deriving DecidableEq

private def WordBlock.word (b : WordBlock) : List ℕ :=
  b.label :: (doubledWord b.pos).reverse ++ b.label :: (doubledWord b.neg).reverse

private def WordBlock.Valid (b : WordBlock) : Prop := ∀ x ∈ b.pos ∪ b.neg, b.label < x

private def WordBlock.support (b : WordBlock) : Finset ℕ := insert b.label (b.pos ∪ b.neg)

private theorem WordBlock.mem_word {b : WordBlock} {x : ℕ} : x ∈ b.word ↔ x ∈ b.support := by
  simp [WordBlock.word, WordBlock.support, mem_doubled, or_left_comm]

private theorem WordBlock.le_of_mem_support {b : WordBlock} (hb : b.Valid) {x : ℕ}
    (hx : x ∈ b.support) : b.label ≤ x := by
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact le_rfl
  · exact (hb x hx).le

private theorem layout_head (bs : List WordBlock) :
    (bs.flatMap WordBlock.word).head? = bs.head?.map WordBlock.label := by
  cases bs <;> simp [WordBlock.word]

private theorem cut_word {a : ℕ} {l : List ℕ} (ht : Twice (a :: l))
    (hs : StirlingBetween (a :: l)) (hf : ReverseFlat (a :: l)) :
    ∃ b : WordBlock, ∃ r : List ℕ, b.Valid ∧ b.label = a ∧
      a :: l = b.word ++ r ∧ (∀ x, r.head? = some x → x < a) ∧ Twice r := by
  have hc : (a :: l).count a = 2 := (ht a).resolve_left (by simp)
  have ha : a ∈ l := by
    by_contra hn
    simp [List.count_eq_zero.mpr hn] at hc
  obtain ⟨p, s, rfl⟩ := List.mem_iff_append.mp ha
  have hp : ∀ x ∈ p, a < x := hs [] a p s (by simp)
  have hano : a ∉ p := fun h => (hp a h).false
  have has : a ∉ s := by
    apply List.count_eq_zero.mp
    simpa [List.count_append, List.count_eq_zero.mpr hano] using hc
  let ns := s.takeWhile (fun x => decide (a < x))
  let r := s.dropWhile (fun x => decide (a < x))
  have hsplit : ns ++ r = s := List.takeWhile_append_dropWhile
  have hns : ∀ x ∈ ns, a < x := fun x hx =>
    of_decide_eq_true (List.mem_takeWhile_imp (p := fun z => decide (a < z)) hx)
  have hless : ∀ x, r.head? = some x → x < a := by
    intro x hx
    have hxle : x ≤ a := by
      have h := List.head?_dropWhile_not (fun z => decide (a < z)) s
      have he : (s.dropWhile (fun z => decide (a < z))).head? = some x := hx
      rw [he] at h
      simpa using h
    have hxne : x ≠ a := by
      intro e
      subst x
      exact has (hsplit ▸ List.mem_append_right ns (List.mem_of_head? hx))
    omega
  have hsep₁ : ∀ x ∈ p, x ∉ ns ++ r := by
    intro x hx
    rw [hsplit]
    exact (StirlingBetween.factor (u := [a]) (t := []) (by simpa using hs)).separates
      (hp x hx).le hx
  have hsep₂ : ∀ x ∈ ns, x ∉ r := by
    intro x hx hxr
    have hxgt := hns x hx
    cases hr : r with
    | nil => simp [hr] at hxr
    | cons y t =>
      have hy := hless y (by simp [hr])
      have htmem : x ∈ t := (List.mem_cons.mp (hr ▸ hxr)).resolve_left (by omega)
      have hm : StirlingBetween (ns ++ y :: t) := by
        have hh : StirlingBetween (a :: p ++ [a] ++ (ns ++ y :: t) ++ []) := by
          have he : ns ++ y :: t = s := (congrArg (ns ++ ·) hr).symm.trans hsplit
          simpa [he, List.append_assoc] using hs
        exact hh.factor
      exact hm.separates (by omega) hx htmem
  have htail : Twice (p ++ (ns ++ r)) := by
    rw [hsplit]
    intro x
    by_cases he : x = a
    · subst x
      exact Or.inl (by simp [List.count_append, List.count_eq_zero.mpr hano,
        List.count_eq_zero.mpr has])
    · simpa [he, Ne.symm he, List.count_append] using ht x
  have hpsort : p.SortedGE :=
    (ReverseFlat.factor (u := []) (t := a :: s) (by simpa using hf)).sorted_after hp
  have hnsort : ns.SortedGE := by
    have h : ReverseFlat ((a :: p) ++ (a :: ns) ++ r) := by
      simpa only [List.append_assoc, List.cons_append, hsplit] using hf
    exact h.factor.sorted_after hns
  have hpp := eq_doubled_reverse hpsort (htail.left hsep₁)
  have hnss := eq_doubled_reverse hnsort ((htail.right hsep₁).left hsep₂)
  refine ⟨⟨a, p.toFinset, ns.toFinset⟩, r, ?_, rfl, ?_, hless, (htail.right hsep₁).right hsep₂⟩
  · intro x hx
    simp only [Finset.mem_union, List.mem_toFinset] at hx
    exact hx.elim (hp x) (hns x)
  · simp only [WordBlock.word, List.cons_append, List.append_assoc, ← hpp, ← hnss, hsplit]

private theorem reverse_layout (l : List ℕ) (ht : Twice l) (hs : StirlingBetween l)
    (hf : ReverseFlat l) :
    ∃ bs : List WordBlock, bs.flatMap WordBlock.word = l ∧
      bs.Pairwise (fun b c => c.label < b.label) ∧ ∀ b ∈ bs, b.Valid := by
  induction hlen : l.length using Nat.strong_induction_on generalizing l with
  | ind k ih =>
    cases l with
    | nil => exact ⟨[], rfl, by simp, by simp⟩
    | cons a l =>
      obtain ⟨b, r, hb, hba, eq, hhead, hrt⟩ := cut_word ht hs hf
      have hrlen : r.length < k := by
        have h := congrArg List.length eq
        simp [WordBlock.word] at h hlen
        omega
      have hrs : StirlingBetween r := StirlingBetween.factor (u := b.word) (t := [])
        (by simpa [← eq] using hs)
      have hrf : ReverseFlat r := ReverseFlat.factor (u := b.word) (t := [])
        (by simpa [← eq] using hf)
      obtain ⟨cs, hcs, hc, hvalid⟩ := ih r.length hrlen r hrt hrs hrf rfl
      refine ⟨b :: cs, by simp [hcs, eq], List.pairwise_cons.mpr ⟨?_, hc⟩, ?_⟩
      · intro c hmem
        cases cs with
        | nil => simp at hmem
        | cons d ds =>
          have hd : d.label < a := hhead _ (by rw [← hcs, layout_head]; rfl)
          rcases List.mem_cons.mp hmem with rfl | hmem
          · simpa [hba] using hd
          · exact hba ▸ ((List.pairwise_cons.mp hc).1 c hmem).trans hd
      · intro d hd
        exact (List.mem_cons.mp hd).elim (fun e => e ▸ hb) (hvalid d)

/-! ### Uniqueness and disjointness of the blocks -/

private def peel (a : ℕ) (l : List ℕ) : Finset ℕ × Finset ℕ × List ℕ :=
  let gt : ℕ → Bool := fun x => decide (a < x)
  let t := (l.dropWhile gt).tail
  ((l.takeWhile gt).toFinset, (t.takeWhile gt).toFinset, t.dropWhile gt)

private theorem peel_word {b : WordBlock} (hb : b.Valid) {r : List ℕ}
    (hr : ∀ x, r.head? = some x → x < b.label) :
    peel b.label (b.word ++ r).tail = (b.pos, b.neg, r) := by
  let gt : ℕ → Bool := fun x => decide (b.label < x)
  have hp : ∀ a ∈ (doubledWord b.pos).reverse, gt a := by
    intro x hx
    exact decide_eq_true (hb x (Finset.mem_union_left _ (mem_doubled.mp (List.mem_reverse.mp hx))))
  have hn : ∀ a ∈ (doubledWord b.neg).reverse, gt a := by
    intro x hx
    exact decide_eq_true (hb x (Finset.mem_union_right _ (mem_doubled.mp (List.mem_reverse.mp hx))))
  have hrt : r.takeWhile gt = [] := by
    cases r with
    | nil => rfl
    | cons x r => simp [gt, (hr x rfl).not_gt]
  have hrd : r.dropWhile gt = r := by
    simpa [hrt] using (List.takeWhile_append_dropWhile (l := r) (p := gt))
  have he (s : Finset ℕ) : (doubledWord s).reverse.toFinset = s := by
    ext x
    simp [mem_doubled]
  change (((b.word ++ r).tail.takeWhile gt).toFinset,
    ((((b.word ++ r).tail.dropWhile gt).tail).takeWhile gt).toFinset,
    (((b.word ++ r).tail.dropWhile gt).tail).dropWhile gt) = _
  simp only [WordBlock.word, List.cons_append, List.append_assoc, List.tail_cons]
  rw [List.takeWhile_append_of_pos hp, List.dropWhile_append_of_pos hp]
  simp only [gt, List.takeWhile_cons, List.dropWhile_cons, lt_irrefl, decide_false,
    Bool.false_eq_true, ite_false, List.append_nil, List.tail_cons, Prod.mk.injEq]
  change (doubledWord b.pos).reverse.toFinset = b.pos ∧
    (((doubledWord b.neg).reverse ++ r).takeWhile gt).toFinset = b.neg ∧
    ((doubledWord b.neg).reverse ++ r).dropWhile gt = r
  rw [List.takeWhile_append_of_pos hn, List.dropWhile_append_of_pos hn, hrt, hrd,
    List.append_nil, he, he]
  exact ⟨rfl, rfl, rfl⟩

private theorem layout_inj {bs cs : List WordBlock}
    (hb : bs.Pairwise (fun b c => c.label < b.label))
    (hc : cs.Pairwise (fun b c => c.label < b.label))
    (hv : ∀ b ∈ bs, b.Valid) (hw : ∀ c ∈ cs, c.Valid)
    (hword : bs.flatMap WordBlock.word = cs.flatMap WordBlock.word) : bs = cs := by
  induction bs generalizing cs with
  | nil => cases cs <;> simp_all [WordBlock.word]
  | cons b bs ih =>
    cases cs with
    | nil => simp [WordBlock.word] at hword
    | cons c cs =>
      have hlabel : b.label = c.label := by
        simpa only [layout_head, List.head?_cons, Option.map_some, Option.some.injEq] using
          congrArg List.head? hword
      have from_tail {d : WordBlock} {ds : List WordBlock}
          (h : (d :: ds).Pairwise (fun p q => q.label < p.label)) :
          ∀ x, (ds.flatMap WordBlock.word).head? = some x → x < d.label := by
        intro x hx
        cases ds with
        | nil => simp at hx
        | cons e es =>
          rw [layout_head] at hx
          have he : e.label = x := Option.some.inj hx
          exact he ▸ (List.pairwise_cons.mp h).1 e (by simp)
      have hpeel₁ := peel_word (hv b (by simp)) (from_tail hb)
      have hpeel₂ := peel_word (hw c (by simp)) (from_tail hc)
      rw [← List.flatMap_cons] at hpeel₁ hpeel₂
      rw [hword, hlabel, hpeel₂] at hpeel₁
      obtain ⟨hpos, hneg, ht⟩ := (by simpa only [Prod.mk.injEq] using hpeel₁ :
        c.pos = b.pos ∧ c.neg = b.neg ∧ cs.flatMap WordBlock.word = bs.flatMap WordBlock.word)
      have he : b = c := by cases b; cases c; simp_all
      rw [he, ih (List.pairwise_cons.mp hb).2 (List.pairwise_cons.mp hc).2
        (fun x hx => hv x (List.mem_cons_of_mem _ hx))
        (fun x hx => hw x (List.mem_cons_of_mem _ hx)) ht.symm]

private theorem WordBlock.two_le_count {b : WordBlock} {x : ℕ} (hx : x ∈ b.support) :
    2 ≤ b.word.count x := by
  simp only [WordBlock.word, List.count_cons, List.count_append, List.count_reverse,
    count_doubledWord, WordBlock.support, Finset.mem_insert, Finset.mem_union] at hx ⊢
  rcases hx with rfl | hx | hx <;> simp [*] <;> omega

private theorem layout_disjoint {bs : List WordBlock} (ht : Twice (bs.flatMap WordBlock.word)) :
    (∀ b ∈ bs, Disjoint b.pos b.neg) ∧ bs.Pairwise (fun b c => Disjoint b.support c.support) := by
  have hle (x : ℕ) := (ht x).elim (fun h => h.le.trans (by decide : 0 ≤ 2)) (fun h => h.le)
  have internal : ∀ b ∈ bs, Disjoint b.pos b.neg := by
    intro b hb
    rw [Finset.disjoint_left]
    intro x hp hn
    obtain ⟨u, v, rfl⟩ := List.mem_iff_append.mp hb
    have h := hle x
    simp only [List.flatMap_append, List.flatMap_cons, List.count_append, WordBlock.word,
      List.count_cons, List.count_reverse, count_doubledWord, hp, hn, ite_true] at h
    omega
  refine ⟨internal, ?_⟩
  clear internal ht
  induction bs with
  | nil => simp
  | cons b bs ih =>
    have ht' : ∀ x, (bs.flatMap WordBlock.word).count x ≤ 2 := by
      intro x
      have h := hle x
      simp only [List.flatMap_cons, List.count_append] at h
      omega
    refine List.pairwise_cons.mpr ⟨?_, ih ht'⟩
    intro c hc
    rw [Finset.disjoint_left]
    intro x hxb hxc
    obtain ⟨u, v, rfl⟩ := List.mem_iff_append.mp hc
    have h := hle x
    simp only [List.flatMap_append, List.flatMap_cons, List.count_append] at h
    have := b.two_le_count hxb
    have := c.two_le_count hxc
    omega

/-! ### Passage from indexed words to reversed lists -/

private theorem at_join {α : Type} (u v : List α) (a : α) :
    (u ++ a :: v)[u.length]? = some a := by
  rw [List.getElem?_append_right le_rfl, Nat.sub_self, List.getElem?_cons_zero]

private theorem at_reverse {m : ℕ} (w : Fin m → ℕ) (i : ℕ) (hi : i < m) :
    ((List.ofFn w).reverse)[i]? = some (w ⟨m - 1 - i, by omega⟩) := by
  have hi' : i < (List.ofFn w).reverse.length := by simpa using hi
  simp [List.getElem?_eq_getElem hi', List.getElem_reverse, Nat.sub_sub]

private theorem length_of_at_reverse {m i a : ℕ} {w : Fin m → ℕ}
    (h : ((List.ofFn w).reverse)[i]? = some a) : i < m := by
  by_contra! hle
  rw [List.getElem?_eq_none (by simpa using hle)] at h
  contradiction

private theorem eq_of_at_reverse {m i a : ℕ} {w : Fin m → ℕ}
    (h : ((List.ofFn w).reverse)[i]? = some a) :
    w ⟨m - 1 - i, by have := length_of_at_reverse h; omega⟩ = a := by
  rw [at_reverse w i (length_of_at_reverse h), Option.some.injEq] at h
  exact h

private theorem twice_reverse_ofFn {n : ℕ} {w : Fin (2 * n) → ℕ}
    (h : IsStirlingPermutation n w) : Twice (List.ofFn w).reverse := by
  intro a
  rw [List.count_reverse, h.count_ofFn]
  split <;> simp

private theorem between_reverse_ofFn {n : ℕ} {w : Fin (2 * n) → ℕ}
    (h : IsStirlingPermutation n w) : StirlingBetween (List.ofFn w).reverse := by
  intro u a v t he x hx
  obtain ⟨p, q, rfl⟩ := List.mem_iff_append.mp hx
  let i := u.length
  let j := (u ++ a :: p).length
  let k := ((u ++ a :: p) ++ x :: q).length
  have hi : ((List.ofFn w).reverse)[i]? = some a := by
    simpa only [he, List.cons_append, List.append_assoc] using at_join u (p ++ x :: q ++ a :: t) a
  have hj : ((List.ofFn w).reverse)[j]? = some x := by
    simpa only [he, List.cons_append, List.append_assoc] using at_join (u ++ a :: p) (q ++ a :: t) x
  have hk : ((List.ofFn w).reverse)[k]? = some a := by
    simpa only [k, he, List.cons_append, List.append_assoc] using
      at_join ((u ++ a :: p) ++ x :: q) t a
  have hki := length_of_at_reverse hk
  let A : Fin (2 * n) := ⟨2 * n - 1 - k, by omega⟩
  let B : Fin (2 * n) := ⟨2 * n - 1 - j, by omega⟩
  let C : Fin (2 * n) := ⟨2 * n - 1 - i, by omega⟩
  have hA : w A = a := eq_of_at_reverse hk
  have hB : w B = x := eq_of_at_reverse hj
  have hC : w C = a := eq_of_at_reverse hi
  have hij : i < j := by simp [i, j]
  have hjk : j < k := by simp [j, k]
  have hab : A < B := by change 2 * n - 1 - k < 2 * n - 1 - j; omega
  have hbc : B < C := by change 2 * n - 1 - j < 2 * n - 1 - i; omega
  simpa [hA, hB] using h.lt_of_eq_of_between hab hbc (hA.trans hC.symm)

private theorem flat_reverse_ofFn {m : ℕ} {w : Fin m → ℕ} (h : IsFlattenedWord w) :
    ReverseFlat (List.ofFn w).reverse := by
  intro i j a b c d hij ha hb hc hd hab hcd
  have hlt := length_of_at_reverse hd
  let A : Fin m := ⟨m - 1 - i, by omega⟩
  let B : Fin m := ⟨m - 1 - (i + 1), by omega⟩
  let C : Fin m := ⟨m - 1 - j, by omega⟩
  let D : Fin m := ⟨m - 1 - (j + 1), by omega⟩
  have hA : w A = a := eq_of_at_reverse ha
  have hB : w B = b := eq_of_at_reverse hb
  have hC : w C = c := eq_of_at_reverse hc
  have hD : w D = d := eq_of_at_reverse hd
  have hCA : C < A := by change m - 1 - j < m - 1 - i; omega
  simpa [hA, hC] using h.le_of_descents hCA (i' := D) (j' := B)
    (by simp [C, D]; omega) (by simp [A, B]; omega)
    (by simpa [hC, hD] using hcd) (by simpa [hA, hB] using hab)

private theorem mem_ofFn_stirling {n : ℕ} {w : Fin (2 * n) → ℕ}
    (hw : IsStirlingPermutation n w) (a : ℕ) : a ∈ List.ofFn w ↔ a ∈ Finset.Icc 1 n := by
  rw [← List.count_pos_iff, hw.count_ofFn]
  split <;> simp_all

private theorem first_one {n : ℕ} {w : Fin (2 * (n + 1)) → ℕ}
    (hw : IsStirlingPermutation (n + 1) w) (hf : IsFlattenedWord w) : w 0 = 1 := by
  have hm : 1 ∈ List.ofFn w := (mem_ofFn_stirling hw 1).mpr (by simp)
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hm
  have h0 : w 0 ∈ List.ofFn w := List.mem_ofFn.mpr ⟨0, rfl⟩
  exact le_antisymm (by simpa only [hi] using hf.first_le i)
    (Finset.mem_Icc.mp ((mem_ofFn_stirling hw _).mp h0)).1

/-! ### The signed partition associated to a layout -/

private abbrev Partition (n : ℕ) := Finpartition (Finset.Icc (-(n : ℤ)) n)

private def mirror (s : Finset ℤ) : Finset ℤ := s.image fun x => -x

private theorem mem_mirror {x : ℤ} {s : Finset ℤ} : x ∈ mirror s ↔ -x ∈ s := by
  simp [mirror, Finset.mem_image, neg_eq_iff_eq_neg]

private theorem mirror_mirror (s : Finset ℤ) : mirror (mirror s) = s := by
  ext x
  simp [mem_mirror]

private def WordBlock.signed (b : WordBlock) : Finset ℤ :=
  (insert b.label b.pos).image (fun a : ℕ => (a : ℤ) - 1) ∪ b.neg.image (fun a : ℕ => 1 - (a : ℤ))

private theorem WordBlock.mem_signed {b : WordBlock} (hb : b.Valid) (hb₁ : 1 ≤ b.label) {x : ℤ} :
    x ∈ b.signed ↔
      (0 ≤ x ∧ x.natAbs + 1 ∈ insert b.label b.pos) ∨
        (x < 0 ∧ x.natAbs + 1 ∈ b.neg) := by
  simp only [WordBlock.signed, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
    · have h : b.label ≤ a := b.le_of_mem_support hb (by
        simpa only [WordBlock.support, Finset.mem_insert, Finset.mem_union] using
          (Finset.mem_insert.mp ha).imp_right (Or.inl : a ∈ b.pos → a ∈ b.pos ∨ a ∈ b.neg))
      exact Or.inl ⟨by omega, by convert ha using 1; omega⟩
    · have h := hb a (Finset.mem_union_right _ ha)
      exact Or.inr ⟨by omega, by convert ha using 1; omega⟩
  · rintro (⟨hx, h⟩ | ⟨hx, h⟩)
    · exact Or.inl ⟨x.natAbs + 1, h, by omega⟩
    · exact Or.inr ⟨x.natAbs + 1, h, by omega⟩

private theorem WordBlock.root_mem_signed (b : WordBlock) : (b.label : ℤ) - 1 ∈ b.signed :=
  Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_, Finset.mem_insert_self _ _, rfl⟩)

private def WordBlock.parts (b : WordBlock) : Finset (Finset ℤ) :=
  if b.label = 1 then {b.signed ∪ mirror b.signed} else {b.signed, mirror b.signed}

private def layoutParts (bs : List WordBlock) : Finset (Finset ℤ) :=
  bs.toFinset.biUnion WordBlock.parts

private theorem mem_layoutParts {bs : List WordBlock} {s : Finset ℤ} :
    s ∈ layoutParts bs ↔ ∃ b ∈ bs, s ∈ b.parts := by
  simp [layoutParts, Finset.mem_biUnion]

private theorem WordBlock.mem_support_of_mem_part {b : WordBlock} (hb : b.Valid)
    (hb₁ : 1 ≤ b.label) {s : Finset ℤ} (hs : s ∈ b.parts) {x : ℤ} (hx : x ∈ s) :
    x.natAbs + 1 ∈ b.support := by
  have aux {z : ℤ} (hz : z ∈ b.signed) : z.natAbs + 1 ∈ b.support := by
    rcases (b.mem_signed hb hb₁).mp hz with ⟨_, h⟩ | ⟨_, h⟩
    · rcases Finset.mem_insert.mp h with e | hp
      · exact Finset.mem_insert.mpr (Or.inl e)
      · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hp)
    · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ h)
  have neg : x ∈ mirror b.signed → x.natAbs + 1 ∈ b.support := by
    intro h
    simpa only [Int.natAbs_neg] using aux (mem_mirror.mp h)
  by_cases he : b.label = 1
  · have h : s = b.signed ∪ mirror b.signed := by simpa [WordBlock.parts, he] using hs
    rw [h, Finset.mem_union] at hx
    exact hx.elim aux neg
  · have h : s = b.signed ∨ s = mirror b.signed := by simpa [WordBlock.parts, he] using hs
    exact h.elim (fun e => aux (e ▸ hx)) (fun e => neg (e ▸ hx))

private theorem WordBlock.part_exists {b : WordBlock} (hb : b.Valid) (hb₁ : 1 ≤ b.label)
    {x : ℤ} (hx : x.natAbs + 1 ∈ b.support) : ∃ s ∈ b.parts, x ∈ s := by
  have hx' : x.natAbs + 1 ∈ insert b.label b.pos ∨ x.natAbs + 1 ∈ b.neg := by
    simpa only [WordBlock.support, Finset.mem_insert, Finset.mem_union, or_assoc] using hx
  have hm : x ∈ b.signed ∨ x ∈ mirror b.signed := by
    rw [mem_mirror, b.mem_signed hb hb₁, b.mem_signed hb hb₁, Int.natAbs_neg]
    rcases hx' with hp | hn
    · by_cases h : 0 ≤ x
      · exact Or.inl (Or.inl ⟨h, hp⟩)
      · exact Or.inr (Or.inl ⟨by omega, hp⟩)
    · have hne : x ≠ 0 := by
        have := hb _ (Finset.mem_union_right _ hn)
        intro h
        simp [h] at this
        omega
      by_cases h : x < 0
      · exact Or.inl (Or.inr ⟨h, hn⟩)
      · exact Or.inr (Or.inr ⟨by omega, hn⟩)
  by_cases he : b.label = 1
  · exact ⟨_, by simp [WordBlock.parts, he], Finset.mem_union.mpr hm⟩
  · rcases hm with hp | hn
    · exact ⟨_, by simp [WordBlock.parts, he], hp⟩
    · exact ⟨_, by simp [WordBlock.parts, he], hn⟩

private theorem WordBlock.signed_disjoint_mirror {b : WordBlock} (hb : b.Valid) (hb₁ : 1 < b.label)
    (hdis : Disjoint b.pos b.neg) : Disjoint b.signed (mirror b.signed) := by
  rw [Finset.disjoint_left]
  intro x hx hnx
  have hx' := (b.mem_signed hb hb₁.le).mp hx
  have hn' := (b.mem_signed hb hb₁.le).mp (mem_mirror.mp hnx)
  rw [Int.natAbs_neg] at hn'
  have dis (a : ℕ) (hp : a ∈ insert b.label b.pos) (hn : a ∈ b.neg) : False := by
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact (hb _ (Finset.mem_union_right _ hn)).false
    · exact Finset.disjoint_left.mp hdis hp hn
  have ne : x ≠ 0 := by
    intro e
    subst x
    simp only [Int.natAbs_zero, zero_add, le_refl, true_and, lt_irrefl, false_and, or_false] at hx'
    rcases Finset.mem_insert.mp hx' with he | hp
    · omega
    · have := hb 1 (Finset.mem_union_left _ hp)
      omega
  rcases hx' with ⟨_, hp⟩ | ⟨_, hn⟩ <;> rcases hn' with ⟨_, hp'⟩ | ⟨_, hn'⟩
  · omega
  · exact dis _ hp hn'
  · exact dis _ hp' hn
  · omega

private theorem WordBlock.part_unique {b : WordBlock} (hb : b.Valid) (hb₁ : 1 ≤ b.label)
    (hd : Disjoint b.pos b.neg) {s t : Finset ℤ} (hs : s ∈ b.parts) (ht : t ∈ b.parts)
    {x : ℤ} (hx : x ∈ s) (hx' : x ∈ t) : s = t := by
  by_cases he : b.label = 1
  · simp [WordBlock.parts, he] at hs ht
    exact hs.trans ht.symm
  · simp only [WordBlock.parts, ite_eq_right he, Finset.mem_insert, Finset.mem_singleton] at hs ht
    have hdis := Finset.disjoint_left.mp (b.signed_disjoint_mirror hb (by omega) hd)
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · rfl
    · exact (hdis hx hx').elim
    · exact (hdis hx' hx).elim
    · rfl

private theorem WordBlock.mirror_mem_parts {b : WordBlock} {s : Finset ℤ} (h : s ∈ b.parts) :
    mirror s ∈ b.parts := by
  by_cases he : b.label = 1
  · simp only [WordBlock.parts, ite_eq_left he, Finset.mem_singleton] at h ⊢
    rw [h]
    ext x
    simp [mem_mirror, or_comm]
  · simp only [WordBlock.parts, ite_eq_right he, Finset.mem_insert, Finset.mem_singleton] at h ⊢
    rcases h with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (mirror_mirror _)

private theorem WordBlock.part_nonempty {b : WordBlock} {s : Finset ℤ} (h : s ∈ b.parts) :
    s.Nonempty := by
  have hp : b.signed.Nonempty := ⟨_, b.root_mem_signed⟩
  have hn : (mirror b.signed).Nonempty := hp.image _
  by_cases he : b.label = 1
  · simp only [WordBlock.parts, ite_eq_left he, Finset.mem_singleton] at h
    exact h ▸ hp.mono Finset.subset_union_left
  · simp [WordBlock.parts, he] at h
    exact h.elim (fun e => e ▸ hp) (fun e => e ▸ hn)

private theorem same_block_of_support {bs : List WordBlock}
    (hd : bs.Pairwise fun b c => Disjoint b.support c.support)
    {b c : WordBlock} (hb : b ∈ bs) (hc : c ∈ bs) {x : ℕ}
    (hxb : x ∈ b.support) (hxc : x ∈ c.support) : b = c := by
  induction bs with
  | nil => simp at hb
  | cons a l ih =>
    obtain ⟨ha, hl⟩ := List.pairwise_cons.mp hd
    rcases List.mem_cons.mp hb with e | hb
    · subst b
      rcases List.mem_cons.mp hc with e | hc
      · exact e.symm
      · exact (Finset.disjoint_left.mp (ha c hc) hxb hxc).elim
    · rcases List.mem_cons.mp hc with e | hc
      · subst c
        exact (Finset.disjoint_left.mp (ha b hb) hxc hxb).elim
      · exact ih hl hb hc

private theorem mem_support_of_layout {bs : List WordBlock} {x : ℕ} :
    (∃ b ∈ bs, x ∈ b.support) ↔ x ∈ bs.flatMap WordBlock.word := by
  simp [List.mem_flatMap, WordBlock.mem_word]

private theorem signed_interval_iff {n : ℕ} {x : ℤ} :
    x ∈ Finset.Icc (-(n : ℤ)) n ↔ x.natAbs + 1 ∈ Finset.Icc 1 (n + 1) := by
  simp only [Finset.mem_Icc]
  omega

private def fromLayout {n : ℕ} {bs : List WordBlock} (hv : ∀ b ∈ bs, b.Valid)
    (hi : ∀ b ∈ bs, Disjoint b.pos b.neg)
    (hd : bs.Pairwise fun b c => Disjoint b.support c.support)
    (ha : ∀ x, x ∈ bs.flatMap WordBlock.word ↔ x ∈ Finset.Icc 1 (n + 1)) : Partition n := by
  have root_pos {b : WordBlock} (hb : b ∈ bs) : 1 ≤ b.label :=
    (Finset.mem_Icc.mp ((ha _).mp (mem_support_of_layout.mp
      ⟨b, hb, Finset.mem_insert_self _ _⟩))).1
  apply Finpartition.ofExistsUnique (layoutParts bs)
  · intro s hs x hx
    obtain ⟨b, hb, hs⟩ := mem_layoutParts.mp hs
    exact signed_interval_iff.mpr ((ha _).mp (mem_support_of_layout.mp
      ⟨b, hb, b.mem_support_of_mem_part (hv b hb) (root_pos hb) hs hx⟩))
  · intro x hx
    obtain ⟨b, hb, hxb⟩ := mem_support_of_layout.mpr ((ha _).mpr (signed_interval_iff.mp hx))
    obtain ⟨s, hs, hxs⟩ := b.part_exists (hv b hb) (root_pos hb) hxb
    refine ⟨s, ⟨mem_layoutParts.mpr ⟨b, hb, hs⟩, hxs⟩, ?_⟩
    rintro t ⟨ht, hxt⟩
    obtain ⟨c, hc, ht⟩ := mem_layoutParts.mp ht
    have he := same_block_of_support hd hc hb
      (c.mem_support_of_mem_part (hv c hc) (root_pos hc) ht hxt) hxb
    subst c
    exact b.part_unique (hv b hb) (root_pos hb) (hi b hb) ht hs hxt hxs
  · intro h
    obtain ⟨b, _, hb⟩ := mem_layoutParts.mp h
    simpa using b.part_nonempty hb

private theorem fromLayout_typeB {n : ℕ} {bs : List WordBlock} (hv : ∀ b ∈ bs, b.Valid)
    (hi : ∀ b ∈ bs, Disjoint b.pos b.neg)
    (hd : bs.Pairwise fun b c => Disjoint b.support c.support)
    (ha : ∀ x, x ∈ bs.flatMap WordBlock.word ↔ x ∈ Finset.Icc 1 (n + 1)) :
    IsTypeBSetPartition (fromLayout hv hi hd ha) := by
  let P : Partition n := fromLayout hv hi hd ha
  have parts : P.parts = layoutParts bs := rfl
  apply isTypeBSetPartition_iff_neg_closed_and_zero_mem.mpr
  have closed (s : Finset ℤ) (hs : s ∈ P.parts) : mirror s ∈ P.parts := by
    rw [parts, mem_layoutParts] at hs ⊢
    obtain ⟨b, hb, hs⟩ := hs
    exact ⟨b, hb, b.mirror_mem_parts hs⟩
  refine ⟨closed, ?_⟩
  · intro s hs he
    have hroot {b : WordBlock} (hb : b ∈ bs) : 1 ≤ b.label :=
      (Finset.mem_Icc.mp ((ha _).mp (mem_support_of_layout.mp
        ⟨b, hb, Finset.mem_insert_self _ _⟩))).1
    obtain ⟨b, hb, hbs⟩ := mem_layoutParts.mp (parts ▸ hs)
    by_cases h : b.label = 1
    · have e : s = b.signed ∪ mirror b.signed := by simpa [WordBlock.parts, h] using hbs
      have hz := b.root_mem_signed
      exact e ▸ Finset.mem_union_left _ (by simpa [h] using hz)
    · have dis := b.signed_disjoint_mirror (hv b hb) (by have := hroot hb; omega) (hi b hb)
      have hm : s = b.signed ∨ s = mirror b.signed := by simpa [WordBlock.parts, h] using hbs
      have hne : mirror b.signed ≠ b.signed := by
        intro ee
        exact Finset.disjoint_left.mp dis b.root_mem_signed (ee.symm ▸ b.root_mem_signed)
      change mirror s = s at he
      rcases hm with rfl | rfl
      · exact (hne he).elim
      · rw [mirror_mirror] at he
        exact (hne he.symm).elim

/-! ### The layout associated to a signed partition -/

private def zeroWordBlock {n : ℕ} (P : Partition n) : WordBlock :=
  ⟨1, (typeBShift ((P.part 0).filter (0 ≤ ·))).erase 1, ∅⟩

private def adlerWordBlock {n : ℕ} (P : Partition n) (p : ℤ) : WordBlock :=
  ⟨p.toNat + 1, (typeBShift ((P.part p).filter (0 < ·))).erase (p.toNat + 1),
    typeBShift ((P.part p).filter (· < 0))⟩

private def partitionLayout {n : ℕ} (P : Partition n) : List WordBlock :=
  ((adlerBlockLabels P).sort (· ≤ ·)).reverse.map (adlerWordBlock P) ++ [zeroWordBlock P]

private theorem zero_shift_mem {n : ℕ} (P : Partition n) :
    1 ∈ typeBShift ((P.part 0).filter (0 ≤ ·)) :=
  mem_typeBShift.mpr ⟨0, Finset.mem_filter.mpr ⟨P.mem_part (by simp), le_rfl⟩, rfl⟩

private theorem adler_shift_mem {n : ℕ} {P : Partition n} {p : ℤ} (hp : p ∈ adlerBlockLabels P) :
    p.toNat + 1 ∈ typeBShift ((P.part p).filter (0 < ·)) := by
  have hp₀ := (Finset.mem_Icc.mp (adlerBlockLabels_subset P hp)).1
  exact mem_typeBShift.mpr ⟨p, Finset.mem_filter.mpr
    ⟨P.mem_part (mem_Icc_of_mem_adlerBlockLabels hp), by omega⟩, by omega⟩

private theorem zeroWordBlock_valid {n : ℕ} (P : Partition n) : (zeroWordBlock P).Valid := by
  intro a ha
  simp only [zeroWordBlock, Finset.union_empty, Finset.mem_erase] at ha ⊢
  obtain ⟨x, _, hx⟩ := mem_typeBShift.mp ha.2
  omega

private theorem adlerWordBlock_valid {n : ℕ} {P : Partition n} {p : ℤ}
    (hp : p ∈ adlerBlockLabels P) : (adlerWordBlock P p).Valid := by
  obtain ⟨hp₀, hmin⟩ := mem_adlerBlockLabels.mp hp
  have hp₁ := (Finset.mem_Icc.mp hp₀).1
  intro a ha
  simp only [adlerWordBlock, Finset.mem_union, Finset.mem_erase] at ha ⊢
  rcases ha with ⟨hne, hpos⟩ | hneg
  · obtain ⟨x, hx, hxe⟩ := mem_typeBShift.mp hpos
    obtain ⟨hx, hx₀⟩ := Finset.mem_filter.mp hx
    have := (hmin x hx).1 hx₀
    omega
  · obtain ⟨x, hx, hxe⟩ := mem_typeBShift.mp hneg
    obtain ⟨hx, hx₀⟩ := Finset.mem_filter.mp hx
    have := (hmin x hx).2 hx₀
    omega

private theorem adlerWordBlock_label_gt {n : ℕ} {P : Partition n} {p : ℤ}
    (hp : p ∈ adlerBlockLabels P) : 1 < (adlerWordBlock P p).label := by
  have := (Finset.mem_Icc.mp (adlerBlockLabels_subset P hp)).1
  change 1 < p.toNat + 1
  omega

private theorem WordBlock.word_eq_reverse {b : WordBlock} (hb : b.Valid) :
    b.word = (doubledWord b.neg ++ wrappedWord (insert b.label b.pos)).reverse := by
  rw [wrappedWord_insert_of_lt (fun x hx => hb x (Finset.mem_union_left _ hx))]
  simp [WordBlock.word, List.reverse_append, List.reverse_cons, List.append_assoc]

private theorem doubledWord_empty : doubledWord ∅ = [] := by
  exact List.length_eq_zero_iff.mp (by simp [length_doubledWord])

private theorem partitionLayout_word {n : ℕ} (P : Partition n) :
    (partitionLayout P).flatMap WordBlock.word = (typeBFlattenedWordList P).reverse := by
  rw [reverse_typeBFlattenedWordList, partitionLayout, List.flatMap_append,
    List.flatMap_map, List.flatMap_singleton]
  congr 1
  · apply List.flatMap_congr
    intro p hp
    have hp' : p ∈ adlerBlockLabels P := by simpa using hp
    rw [(adlerWordBlock P p).word_eq_reverse (adlerWordBlock_valid hp')]
    simp [adlerWordBlock, Finset.insert_erase (adler_shift_mem hp'), List.reverse_append]
  · rw [(zeroWordBlock P).word_eq_reverse (zeroWordBlock_valid P)]
    simp [zeroWordBlock, doubledWord_empty, Finset.insert_erase (zero_shift_mem P)]

private theorem partitionLayout_valid {n : ℕ} (P : Partition n) :
    ∀ b ∈ partitionLayout P, b.Valid := by
  intro b hb
  simp only [partitionLayout, List.mem_append, List.mem_singleton, List.mem_map,
    List.mem_reverse, Finset.mem_sort] at hb
  rcases hb with ⟨p, hp, rfl⟩ | rfl
  · exact adlerWordBlock_valid hp
  · exact zeroWordBlock_valid P

private theorem partitionLayout_sorted {n : ℕ} (P : Partition n) :
    (partitionLayout P).Pairwise (fun b c => c.label < b.label) := by
  rw [partitionLayout, List.pairwise_append]
  refine ⟨?_, by simp, ?_⟩
  · rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_
      (List.pairwise_reverse.mpr (Finset.sortedLT_sort (adlerBlockLabels P)).pairwise)
    intro p q hp hq hlt
    have hp' : p ∈ adlerBlockLabels P := by simpa using hp
    have hq' : q ∈ adlerBlockLabels P := by simpa using hq
    have := (Finset.mem_Icc.mp (adlerBlockLabels_subset P hp')).1
    have := (Finset.mem_Icc.mp (adlerBlockLabels_subset P hq')).1
    change q.toNat + 1 < p.toNat + 1
    omega
  · intro b hb c hc
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hb
    obtain rfl := List.mem_singleton.mp hc
    exact adlerWordBlock_label_gt (by simpa using hp)

private theorem mem_shift_of_sign {s : Finset ℤ} {x : ℤ}
    (hs : ∀ y ∈ s, 0 ≤ y ↔ 0 ≤ x) : x.natAbs + 1 ∈ typeBShift s ↔ x ∈ s := by
  constructor
  · intro h
    obtain ⟨y, hy, he⟩ := mem_typeBShift.mp h
    have hyn := hs y hy
    have e : x = y := by omega
    rwa [e]
  · intro hx
    exact mem_typeBShift.mpr ⟨x, hx, rfl⟩

private theorem WordBlock.zero_mem_signed {b : WordBlock} (hb : b.Valid) (hb₀ : 1 ≤ b.label) :
    (0 : ℤ) ∈ b.signed ↔ b.label = 1 := by
  constructor
  · intro h
    have hx : 1 ∈ b.support := by
      have hpart : b.label ≤ 1 := by
        have h := (b.mem_signed hb hb₀).mp h
        simp only [Int.natAbs_zero, zero_add, le_rfl, true_and, Finset.mem_insert,
          lt_irrefl, false_and, or_false] at h
        rcases h with h | h
        · omega
        · have := hb 1 (Finset.mem_union_left _ h)
          omega
      exact Finset.mem_insert.mpr (Or.inl (by omega))
    have := b.le_of_mem_support hb hx
    omega
  · intro he
    simpa [he] using b.root_mem_signed

private theorem adlerWordBlock_signed {n : ℕ} {P : Partition n} (hP : IsTypeBSetPartition P)
    {p : ℤ} (hp : p ∈ adlerBlockLabels P) : (adlerWordBlock P p).signed = P.part p := by
  let b := adlerWordBlock P p
  have hb := adlerWordBlock_valid hp
  have hb₁ := adlerWordBlock_label_gt hp
  ext x
  change x ∈ b.signed ↔ x ∈ P.part p
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [b.mem_signed hb hb₁.le]
    simp only [hx, hx.not_ge, false_and, true_and, false_or]
    change x.natAbs + 1 ∈ typeBShift ((P.part p).filter (· < 0)) ↔ _
    rw [mem_shift_of_sign (fun y hy => by have := (Finset.mem_filter.mp hy).2; omega)]
    simp [hx]
  · have hne : b.label ≠ 1 := hb₁.ne'
    simp [b.zero_mem_signed hb hb₁.le, hne, hP.zero_notMem_part_of_mem_adlerBlockLabels hp]
  · rw [b.mem_signed hb hb₁.le]
    simp only [hx.le, hx.not_gt, true_and, false_and, or_false]
    change x.natAbs + 1 ∈ insert (p.toNat + 1)
      ((typeBShift ((P.part p).filter (0 < ·))).erase (p.toNat + 1)) ↔ _
    rw [Finset.insert_erase (adler_shift_mem hp),
      mem_shift_of_sign (fun y hy => by have := (Finset.mem_filter.mp hy).2; omega)]
    simp [hx]

private theorem zeroWordBlock_signed {n : ℕ} (P : Partition n) :
    (zeroWordBlock P).signed = (P.part 0).filter (0 ≤ ·) := by
  ext x
  rw [(zeroWordBlock P).mem_signed (zeroWordBlock_valid P) (by rfl)]
  simp only [zeroWordBlock, Finset.notMem_empty, and_false, or_false,
    Finset.insert_erase (zero_shift_mem P)]
  by_cases hx : 0 ≤ x
  · rw [mem_shift_of_sign (fun y hy => by have := (Finset.mem_filter.mp hy).2; simp [hx, this])]
    simp [hx]
  · simp [hx]

private theorem partitionLayout_parts {n : ℕ} {P : Partition n} (hP : IsTypeBSetPartition P) :
    layoutParts (partitionLayout P) = P.parts := by
  have zero_parts : (zeroWordBlock P).parts = {P.part 0} := by
    have hlabel : (zeroWordBlock P).label = 1 := rfl
    rw [WordBlock.parts, ite_eq_left hlabel, zeroWordBlock_signed]
    congr 1
    ext x
    rw [Finset.mem_union, mem_mirror]
    simp only [Finset.mem_filter]
    constructor
    · rintro (⟨hx, -⟩ | ⟨hx, -⟩)
      · exact hx
      · simpa only [neg_neg] using hP.neg_mem_part_zero hx
    · intro hx
      by_cases he : 0 ≤ x
      · exact Or.inl ⟨hx, he⟩
      · exact Or.inr ⟨hP.neg_mem_part_zero hx, by omega⟩
  have adler_parts {p : ℤ} (hp : p ∈ adlerBlockLabels P) :
      (adlerWordBlock P p).parts = {P.part p, P.part (-p)} := by
    rw [WordBlock.parts, ite_eq_right (adlerWordBlock_label_gt hp).ne',
      adlerWordBlock_signed hP hp, hP.part_neg (mem_Icc_of_mem_adlerBlockLabels hp)]
    rfl
  have mem_neg {p : ℤ} (hp : p ∈ adlerBlockLabels P) : P.part (-p) ∈ P.parts := by
    apply P.part_mem.mpr
    have hpI := Finset.mem_Icc.mp (mem_Icc_of_mem_adlerBlockLabels hp)
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have mem₀ : P.part 0 ∈ P.parts := P.part_mem.mpr (by simp)
  ext s
  rw [mem_layoutParts]
  constructor
  · rintro ⟨b, hb, hs⟩
    simp only [partitionLayout, List.mem_append, List.mem_singleton, List.mem_map,
      List.mem_reverse, Finset.mem_sort] at hb
    rcases hb with ⟨p, hp, rfl⟩ | rfl
    · rw [adler_parts hp] at hs
      rcases Finset.mem_insert.mp hs with rfl | hs
      · exact P.part_mem.mpr (mem_Icc_of_mem_adlerBlockLabels hp)
      · obtain rfl := Finset.mem_singleton.mp hs
        exact mem_neg hp
    · rw [zero_parts, Finset.mem_singleton] at hs
      exact hs ▸ mem₀
  · intro hs
    obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hs
    have hx₀ := P.le hs hx
    by_cases hz : x ∈ P.part 0
    · have e := P.eq_of_mem_parts hs mem₀ hx hz
      exact ⟨zeroWordBlock P, by simp [partitionLayout], by simpa [zero_parts] using e⟩
    · obtain ⟨p, hp, hxp⟩ := hP.exists_mem_adlerBlockLabels hx₀ hz
      refine ⟨adlerWordBlock P p, by
        simp only [partitionLayout, List.mem_append, List.mem_map, List.mem_reverse,
          Finset.mem_sort]
        exact Or.inl ⟨p, hp, rfl⟩, ?_⟩
      rw [adler_parts hp]
      rcases hxp with hxp | hxp
      · have hp' := P.part_mem.mpr (mem_Icc_of_mem_adlerBlockLabels hp)
        rw [← P.part_eq_of_mem hs hx, P.part_eq_of_mem hp' hxp]
        simp
      · have hmem : x ∈ P.part (-p) := by
          rw [hP.part_neg (mem_Icc_of_mem_adlerBlockLabels hp)]
          exact mem_mirror.mpr hxp
        rw [← P.part_eq_of_mem hs hx, P.part_eq_of_mem (mem_neg hp) hmem]
        simp

/-! ### Recovering the layout of a decoded partition -/

private theorem layout_last {bs : List WordBlock} (hv : ∀ b ∈ bs, b.Valid)
    (hpos : ∀ b ∈ bs, 1 ≤ b.label) (hf : (bs.flatMap WordBlock.word).reverse.head? = some 1) :
    ∃ cs b, bs = cs ++ [b] ∧ b.label = 1 ∧ b.neg = ∅ := by
  cases he : bs.reverse with
  | nil =>
    have e : bs = [] := by simpa using congrArg List.reverse he
    simp [e] at hf
  | cons b ds =>
    have e : bs = ds.reverse ++ [b] := by simpa using congrArg List.reverse he
    have hm : b ∈ bs := by simp [e]
    have hne : b.word.reverse ≠ [] := by simp [WordBlock.word]
    have hhead : b.word.reverse.head? = some 1 := by
      simpa only [e, List.flatMap_append, List.flatMap_singleton, List.reverse_append,
        List.head?_append_of_ne_nil _ hne] using hf
    have h1 : 1 ∈ b.support := b.mem_word.mp (List.mem_reverse.mp (List.mem_of_head? hhead))
    have hl : b.label = 1 := le_antisymm (b.le_of_mem_support (hv b hm) h1) (hpos b hm)
    refine ⟨ds.reverse, b, e, hl, ?_⟩
    by_contra hn
    have hd : doubledWord b.neg ≠ [] := by
      intro hz
      have hcard : 2 * b.neg.card = 0 :=
        (length_doubledWord _).symm.trans (congrArg List.length hz)
      exact hn (Finset.card_eq_zero.mp (by omega))
    rw [b.word_eq_reverse (hv b hm), List.reverse_reverse,
      List.head?_append_of_ne_nil _ hd] at hhead
    exact (hv b hm 1 (Finset.mem_union_right _ (mem_doubled.mp (List.mem_of_head? hhead)))).not_ge
      (by omega)

private theorem WordBlock.shift_nonneg_signed {b : WordBlock} (hv : b.Valid) (ha : 1 ≤ b.label) :
    typeBShift (b.signed.filter (0 ≤ ·)) = insert b.label b.pos := by
  ext a
  constructor
  · intro hm
    obtain ⟨x, hx, rfl⟩ := mem_typeBShift.mp hm
    obtain ⟨hx, hx₀⟩ := Finset.mem_filter.mp hx
    rcases (b.mem_signed hv ha).mp hx with ⟨_, h⟩ | ⟨hn, _⟩
    · exact h
    · omega
  · intro hm
    have hle : b.label ≤ a := by
      rcases Finset.mem_insert.mp hm with rfl | hm
      · exact le_rfl
      · exact (hv a (Finset.mem_union_left _ hm)).le
    let x : ℤ := (a : ℤ) - 1
    have h₀ : 0 ≤ x := by dsimp [x]; omega
    have he : x.natAbs + 1 = a := by dsimp [x]; omega
    exact mem_typeBShift.mpr ⟨x, Finset.mem_filter.mpr
      ⟨(b.mem_signed hv ha).mpr (Or.inl ⟨h₀, he.symm ▸ hm⟩), h₀⟩, he⟩

private theorem WordBlock.shift_neg_signed {b : WordBlock} (hv : b.Valid) (ha : 1 ≤ b.label) :
    typeBShift (b.signed.filter (· < 0)) = b.neg := by
  ext a
  constructor
  · intro hm
    obtain ⟨x, hx, rfl⟩ := mem_typeBShift.mp hm
    obtain ⟨hx, hx₀⟩ := Finset.mem_filter.mp hx
    rcases (b.mem_signed hv ha).mp hx with ⟨hp, _⟩ | ⟨_, h⟩
    · omega
    · exact h
  · intro hm
    have hle := hv a (Finset.mem_union_right _ hm)
    let x : ℤ := 1 - (a : ℤ)
    have h₀ : x < 0 := by dsimp [x]; omega
    have he : x.natAbs + 1 = a := by dsimp [x]; omega
    exact mem_typeBShift.mpr ⟨x, Finset.mem_filter.mpr
      ⟨(b.mem_signed hv ha).mpr (Or.inr ⟨h₀, he.symm ▸ hm⟩), h₀⟩, he⟩

private def WordBlock.key (b : WordBlock) : ℤ := (b.label : ℤ) - 1

private theorem WordBlock.recover_adler {n : ℕ} {P : Partition n} {b : WordBlock}
    (hs : b.signed ∈ P.parts) (hv : b.Valid) (hlt : 1 < b.label) (hhi : b.label ≤ n + 1) :
    b.key ∈ adlerBlockLabels P ∧ adlerWordBlock P b.key = b := by
  have hkey : Finpartition.part P b.key = b.signed := P.part_eq_of_mem hs b.root_mem_signed
  have hl : b.key.toNat + 1 = b.label := by dsimp [WordBlock.key]; omega
  have hp : b.key ∈ adlerBlockLabels P := by
    apply mem_adlerBlockLabels.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
    · dsimp [WordBlock.key]; omega
    · dsimp [WordBlock.key]; omega
    rw [hkey]
    intro q hq
    rcases (b.mem_signed hv hlt.le).mp hq with ⟨hq₀, h⟩ | ⟨hq₀, h⟩
    · have hle : b.label ≤ q.natAbs + 1 := by
        rcases Finset.mem_insert.mp h with e | h
        · omega
        · exact (hv _ (Finset.mem_union_left _ h)).le
      dsimp [WordBlock.key]
      omega
    · have := hv _ (Finset.mem_union_right _ h)
      dsimp [WordBlock.key]
      omega
  refine ⟨hp, ?_⟩
  have hzero : (0 : ℤ) ∉ b.signed := fun h => hlt.ne' ((b.zero_mem_signed hv hlt.le).mp h)
  have hfilter : b.signed.filter (0 < ·) = b.signed.filter (0 ≤ ·) := by
    apply Finset.filter_congr
    intro q hq
    have hn : q ≠ 0 := fun e => hzero (e ▸ hq)
    omega
  have hex : b.label ∉ b.pos := fun h => (hv _ (Finset.mem_union_left _ h)).false
  rcases b with ⟨a, ps, ns⟩
  simp only [adlerWordBlock, hl, hkey, hfilter, WordBlock.shift_nonneg_signed hv hlt.le,
    WordBlock.shift_neg_signed hv hlt.le, Finset.erase_insert hex]

private theorem WordBlock.recover_zero {n : ℕ} {P : Partition n} {b : WordBlock}
    (hs : b.signed ∪ mirror b.signed ∈ P.parts) (hv : b.Valid) (hlabel : b.label = 1)
    (hneg : b.neg = ∅) : zeroWordBlock P = b := by
  have h₁ : 1 ≤ b.label := hlabel.ge
  have hm : (0 : ℤ) ∈ b.signed := (b.zero_mem_signed hv h₁).mpr hlabel
  have hpart : P.part 0 = b.signed ∪ mirror b.signed :=
    P.part_eq_of_mem hs (Finset.mem_union_left _ hm)
  have signed_pos {x : ℤ} (hx : x ∈ b.signed) : 0 ≤ x := by
    rcases (b.mem_signed hv h₁).mp hx with ⟨hx, _⟩ | ⟨_, hx⟩
    · exact hx
    · simp [hneg] at hx
  have hfilter : (P.part 0).filter (0 ≤ ·) = b.signed.filter (0 ≤ ·) := by
    ext x
    rw [hpart, Finset.mem_filter, Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hx | hx, hx₀⟩
      · exact ⟨hx, hx₀⟩
      · have hx₁ := signed_pos (mem_mirror.mp hx)
        have e : x = 0 := by omega
        exact ⟨e.symm ▸ hm, hx₀⟩
    · rintro ⟨hx, hx₀⟩
      exact ⟨Or.inl hx, hx₀⟩
  have hex : b.label ∉ b.pos := fun h => (hv _ (Finset.mem_union_left _ h)).false
  rw [zeroWordBlock, hfilter, b.shift_nonneg_signed hv h₁, ← hlabel, Finset.erase_insert hex]
  cases b
  simp_all

private theorem fromLayout_recovers {n : ℕ} {cs : List WordBlock} {b₀ : WordBlock}
    (hv : ∀ b ∈ cs ++ [b₀], b.Valid)
    (hi : ∀ b ∈ cs ++ [b₀], Disjoint b.pos b.neg)
    (hd : (cs ++ [b₀]).Pairwise fun b c => Disjoint b.support c.support)
    (ha : ∀ x, x ∈ (cs ++ [b₀]).flatMap WordBlock.word ↔ x ∈ Finset.Icc 1 (n + 1))
    (hs : (cs ++ [b₀]).Pairwise fun b c => c.label < b.label)
    (h₀ : b₀.label = 1) (hneg : b₀.neg = ∅) :
    partitionLayout (fromLayout hv hi hd ha) = cs ++ [b₀] := by
  let P : Partition n := fromLayout hv hi hd ha
  have Pparts : P.parts = layoutParts (cs ++ [b₀]) := rfl
  have Ptype : IsTypeBSetPartition P := fromLayout_typeB hv hi hd ha
  have hz : (b₀.signed ∪ mirror b₀.signed) ∈ P.parts := by
    rw [Pparts, mem_layoutParts]
    exact ⟨b₀, by simp, by simp [WordBlock.parts, h₀]⟩
  have hzpart := b₀.recover_zero hz (hv b₀ (by simp)) h₀ hneg
  have hzmem : (0 : ℤ) ∈ b₀.signed := (b₀.zero_mem_signed (hv _ (by simp)) h₀.ge).mpr h₀
  have hzblock : P.part 0 = b₀.signed ∪ mirror b₀.signed :=
    P.part_eq_of_mem hz (Finset.mem_union_left _ hzmem)
  have recovers {b : WordBlock} (hb : b ∈ cs) :
      b.key ∈ adlerBlockLabels P ∧ adlerWordBlock P b.key = b ∧ P.part b.key = b.signed := by
    have hbs : b ∈ cs ++ [b₀] := List.mem_append_left _ hb
    have hlt : 1 < b.label := h₀ ▸ (List.pairwise_append.mp hs).2.2 b hb b₀ (by simp)
    have hhi := (Finset.mem_Icc.mp ((ha _).mp
      (mem_support_of_layout.mp ⟨b, hbs, Finset.mem_insert_self _ _⟩))).2
    have hpart : b.signed ∈ P.parts := by
      rw [Pparts, mem_layoutParts]
      exact ⟨b, hbs, by simp [WordBlock.parts, hlt.ne']⟩
    obtain ⟨hp, hb'⟩ := b.recover_adler hpart (hv b hbs) hlt hhi
    exact ⟨hp, hb', P.part_eq_of_mem hpart b.root_mem_signed⟩
  have labels (p : ℤ) : p ∈ adlerBlockLabels P ↔ p ∈ cs.map WordBlock.key := by
    constructor
    · intro hp
      have hmem := P.part_mem.mpr (mem_Icc_of_mem_adlerBlockLabels hp)
      obtain ⟨b, hb, hpart⟩ := mem_layoutParts.mp (Pparts ▸ hmem)
      rcases List.mem_append.mp hb with hb | hb
      · obtain ⟨hl, _, he⟩ := recovers hb
        have hlt : 1 < b.label := h₀ ▸ (List.pairwise_append.mp hs).2.2 b hb b₀ (by simp)
        simp only [WordBlock.parts, ite_eq_right hlt.ne', Finset.mem_insert,
          Finset.mem_singleton] at hpart
        rcases hpart with hpart | hpart
        · have heq := eq_of_part_eq_of_mem_adlerBlockLabels hp hl (hpart.trans he.symm)
          exact List.mem_map.mpr ⟨b, hb, heq.symm⟩
        · rw [← he] at hpart
          exact (part_ne_neg_part_of_mem_adlerBlockLabels hl hp hpart).elim
      · have e := List.mem_singleton.mp hb
        subst b
        have hpart : P.part p = b₀.signed ∪ mirror b₀.signed := by
          simpa [WordBlock.parts, h₀] using hpart
        have hzero : (0 : ℤ) ∈ P.part p := hpart.trans hzblock.symm ▸ P.mem_part (by simp)
        exact (Ptype.zero_notMem_part_of_mem_adlerBlockLabels hp hzero).elim
    · rintro h
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp h
      exact (recovers hb).1
  have hsort : ((adlerBlockLabels P).sort (· ≤ ·)).reverse = cs.map WordBlock.key := by
    apply List.SortedGT.eq_of_mem_iff
    · exact (Finset.sortedLT_sort _).reverse
    · apply List.Pairwise.sortedGT
      rw [List.pairwise_map]
      exact (List.pairwise_append.mp hs).1.imp (by intro a b h; dsimp [WordBlock.key]; omega)
    · intro p
      simpa using labels p
  change partitionLayout P = _
  rw [partitionLayout, hsort, hzpart, List.map_map]
  suffices hmap : cs.map (adlerWordBlock P ∘ WordBlock.key) = cs by rw [hmap]
  conv_rhs => rw [← List.map_id cs]
  exact List.map_congr_left (fun b hb => (recovers hb).2.1)

/-! ### The bijection -/

private theorem ofFn_typeBFlattenedWord {n : ℕ} {P : Partition n} (hP : IsTypeBSetPartition P) :
    List.ofFn (typeBFlattenedWord P) = typeBFlattenedWordList P :=
  ofFn_typeBFlattenedWord_of_length_eq P hP.length_typeBFlattenedWordList

/-- **The map $\varphi$ is a bijection from type $B$ set partitions onto flattened Stirling
permutations.** For a natural number $n$, let $\varphi$ be the map of Buck et al.
(Proposition 1) that sends a set partition $P$ of $\{-n, \dots, n\}$ to a word of length
$2(n + 1)$ over the natural numbers, built from the zero block of $P$ and its Adler-labelled
blocks with each element $i$ replaced by $|i| + 1$. Then $\varphi$ sends the set of type $B$
set partitions of $\{-n, \dots, n\}$ bijectively onto the set of flattened Stirling
permutations of order $n + 1$: $\varphi$ is injective on type $B$ set partitions, sends each
of them to a flattened Stirling permutation of order $n + 1$, and every flattened Stirling
permutation of order $n + 1$ is $\varphi(\pi)$ for some type $B$ set partition $\pi$ of
$\{-n, \dots, n\}$.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Theorem 3. -/
public theorem bijOn_typeBFlattenedWord (n : ℕ) :
    Set.BijOn (typeBFlattenedWord (n := n))
      {P : Finpartition (Finset.Icc (-(n : ℤ)) n) | IsTypeBSetPartition P}
      {w : Fin (2 * (n + 1)) → ℕ | IsStirlingPermutation (n + 1) w ∧ IsFlattenedWord w} := by
  refine ⟨fun P hP => typeBFlattenedWord_mem_flattenedStirling P hP, ?_, ?_⟩
  · intro P hP Q hQ he
    have hp : IsTypeBSetPartition P := hP
    have hq : IsTypeBSetPartition Q := hQ
    have hl : typeBFlattenedWordList P = typeBFlattenedWordList Q := by
      rw [← ofFn_typeBFlattenedWord hp, ← ofFn_typeBFlattenedWord hq, he]
    have hparts := layout_inj (partitionLayout_sorted P) (partitionLayout_sorted Q)
      (partitionLayout_valid P) (partitionLayout_valid Q) (by simp [partitionLayout_word, hl])
    apply Finpartition.ext
    rw [← partitionLayout_parts hp, ← partitionLayout_parts hq, hparts]
  · rintro w ⟨hw, hf⟩
    have ht := twice_reverse_ofFn hw
    obtain ⟨bs, hword, hs, hv⟩ :=
      reverse_layout _ ht (between_reverse_ofFn hw) (flat_reverse_ofFn hf)
    have hfirst : (bs.flatMap WordBlock.word).reverse.head? = some 1 := by
      rw [hword, List.reverse_reverse, List.head?_eq_getElem?,
        List.getElem?_eq_getElem (by simp), List.getElem_ofFn]
      exact congrArg some (first_one hw hf)
    have ha (a : ℕ) : a ∈ bs.flatMap WordBlock.word ↔ a ∈ Finset.Icc 1 (n + 1) := by
      rw [hword, List.mem_reverse, mem_ofFn_stirling hw]
    have hpos (b : WordBlock) (hb : b ∈ bs) : 1 ≤ b.label :=
      (Finset.mem_Icc.mp ((ha _).mp (mem_support_of_layout.mp
        ⟨b, hb, Finset.mem_insert_self _ _⟩))).1
    obtain ⟨cs, b₀, rfl, h₀, hn⟩ := layout_last hv hpos hfirst
    obtain ⟨hi, hd⟩ := layout_disjoint (hword.symm ▸ ht)
    let P : Partition n := fromLayout hv hi hd ha
    have hP := fromLayout_typeB hv hi hd ha
    refine ⟨P, hP, List.ofFn_injective ?_⟩
    rw [ofFn_typeBFlattenedWord hP]
    apply List.reverse_injective
    rw [← partitionLayout_word P, fromLayout_recovers hv hi hd ha hs h₀ hn, hword]

end MetaMathlibExt
