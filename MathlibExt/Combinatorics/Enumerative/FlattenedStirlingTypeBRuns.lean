/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.FlattenedStirlingPermutations
import Mathlib.Algebra.BigOperators.Fin

/-!
# Runs of the word of a type `B` set partition

`MetaMathlibExt.wordRunCount_typeBFlattenedWord` counts the runs of the word `φ(π)` of a type `B`
set partition `π` of `[-n, n]`. The list of `π` has length `2(n + 1)`, because the absolute values
of the nonnegative elements of the zero block and of the elements of the kept blocks split
`{0, …, n}`, so the word is the list itself. A descent then occurs exactly at the end of each
wrapped block word with at least two letters and at the passage from the doubled word of a
nonempty negative part to the wrapped word of the same block.

## References

* Adam Buck, Jennifer Elder, Azia A. Figueroa, Pamela E. Harris, Kimberly J. Harry, and
  Anthony Simpson, *Flattened Stirling Permutations*, INTEGERS 24 (2024), Article A104,
  pp. 1–20, Notation 1, Proposition 1, and Lemma 4.
-/

namespace MetaMathlibExt
namespace wordRunCount_typeBFlattenedWord

/-! ### Descents of lists of letters -/

-- The number of descents of `l` when the letter `p` is written in front of it.
private def descentsAfter : ℕ → List ℕ → ℕ
  | _, [] => 0
  | p, a :: l => (if a < p then 1 else 0) + descentsAfter a l

-- The last letter of `l`, or `p` when `l` is empty.
private def lastOr : ℕ → List ℕ → ℕ
  | p, [] => p
  | _, a :: l => lastOr a l

private theorem descentsAfter_append (p : ℕ) (l l' : List ℕ) :
    descentsAfter p (l ++ l') = descentsAfter p l + descentsAfter (lastOr p l) l' := by
  induction l generalizing p with
  | nil => simp [descentsAfter, lastOr]
  | cons a l ih => simp [descentsAfter, lastOr, ih, Nat.add_assoc]

private theorem lastOr_append (p : ℕ) (l l' : List ℕ) :
    lastOr p (l ++ l') = lastOr (lastOr p l) l' := by
  induction l generalizing p with
  | nil => rfl
  | cons a l ih => exact ih a

private theorem lastOr_mem (p : ℕ) {l : List ℕ} (hl : l ≠ []) : lastOr p l ∈ l := by
  induction l generalizing p with
  | nil => exact absurd rfl hl
  | cons a l ih =>
    rcases eq_or_ne l [] with rfl | h
    · simp [lastOr]
    · exact List.mem_cons_of_mem a (ih a h)

-- Doubling every letter of a weakly increasing list creates no descent.
private theorem descentsAfter_double (l : List ℕ) (hl : l.Pairwise (· ≤ ·)) (p : ℕ)
    (hp : ∀ y ∈ l, p ≤ y) : descentsAfter p (l.flatMap fun s => [s, s]) = 0 := by
  induction l generalizing p with
  | nil => rfl
  | cons a l ih =>
    obtain ⟨ha, hl⟩ := List.pairwise_cons.mp hl
    have hpa : ¬ a < p := not_lt.mpr (hp a List.mem_cons_self)
    simp [descentsAfter, hpa, ih hl a ha]

private theorem lastOr_double (p : ℕ) (l : List ℕ) :
    lastOr p (l.flatMap fun s => [s, s]) = lastOr p l := by
  induction l generalizing p with
  | nil => rfl
  | cons a l ih => simpa [lastOr] using ih a

private theorem descentsAfter_eq_sum (a : ℕ) (l : List ℕ) :
    descentsAfter a l =
      ∑ i : Fin l.length, if l.getD i 0 < (a :: l).getD i 0 then 1 else 0 := by
  induction l generalizing a with
  | nil => simp [descentsAfter]
  | cons b l ih =>
    rw [List.length_cons, Fin.sum_univ_succ]
    simp [descentsAfter, ih b]

private theorem wordRunStart_succ {m : ℕ} (w : Fin (m + 1) → ℕ) (i : Fin m) :
    wordRunStart w i.succ ↔ w i.succ < w i.castSucc := by
  constructor
  · rintro (h | ⟨j, hj, h⟩)
    · simp at h
    · obtain rfl : j = i.castSucc := Fin.ext (by simp at hj ⊢; omega)
      exact h
  · exact fun h => Or.inr ⟨i.castSucc, by simp, h⟩

private theorem wordRunCount_cons (a : ℕ) (l : List ℕ) :
    wordRunCount (fun i : Fin (l.length + 1) => (a :: l).getD i 0) = 1 + descentsAfter a l := by
  have h0 : wordRunStart (fun i : Fin (l.length + 1) => (a :: l).getD i 0) 0 := Or.inl rfl
  rw [wordRunCount, Finset.card_filter, Fin.sum_univ_succ, descentsAfter_eq_sum, ite_eq_left h0]
  refine congrArg (1 + ·) (Finset.sum_congr rfl fun i _ => ?_)
  simp only [wordRunStart_succ, Fin.val_succ, List.getD_cons_succ, Fin.val_castSucc]

-- The runs of the word of a list are its descents after a letter above its first letter.
private theorem wordRunCount_ofList {L : List ℕ} {m : ℕ} (hm : L.length = m) {p : ℕ}
    (hp : ∀ a ∈ L.head?, a < p) :
    wordRunCount (fun i : Fin m => L.getD i 0) = descentsAfter p L := by
  subst hm
  cases L with
  | nil => simp [wordRunCount, descentsAfter]
  | cons a l =>
    have ha : a < p := hp a rfl
    simp only [descentsAfter, ite_eq_left ha]
    exact wordRunCount_cons a l

-- The sorted list sums like the finite set.
private theorem sum_sort (s : Finset ℤ) (f : ℤ → ℕ) :
    ((s.sort (· ≤ ·)).map f).sum = ∑ p ∈ s, f p := by
  rw [← List.sum_toFinset f (Finset.sort_nodup s _), Finset.sort_toFinset]

-- Concatenating block words whose last letters weakly increase adds up their descents.
private theorem descentsAfter_flatMap (F : ℤ → List ℕ) (c : ℤ → ℕ) (key : ℤ → ℕ) :
    ∀ ps : List ℤ, ps.Pairwise (fun a b => key a ≤ key b) → ∀ q : ℕ, (∀ p ∈ ps, q ≤ key p) →
      (∀ p ∈ ps, ∀ q' : ℕ, q' ≤ key p →
        descentsAfter q' (F p) = c p ∧ lastOr q' (F p) = key p) →
      descentsAfter q (ps.flatMap F) = (ps.map c).sum
  | [], _, _, _, _ => by simp [descentsAfter]
  | p :: ps, hps, q, hq, hF => by
    obtain ⟨hp, hps⟩ := List.pairwise_cons.mp hps
    obtain ⟨h1, h2⟩ := hF p List.mem_cons_self q (hq p List.mem_cons_self)
    rw [List.flatMap_cons, descentsAfter_append, h1, h2, List.map_cons, List.sum_cons,
      descentsAfter_flatMap F c key ps hps (key p) hp
        (fun p' hp' => hF p' (List.mem_cons_of_mem _ hp'))]

/-! ### Doubled and wrapped words -/

-- A doubled word of letters at least `q` has no descent after `q`; it ends above `t` exactly
-- when it is nonempty.
private theorem doubled {N : Finset ℕ} {t q : ℕ} (hqt : q ≤ t) (hN : ∀ y ∈ N, t < y) :
    descentsAfter q (doubledWord N) = 0 ∧ (t < lastOr q (doubledWord N) ↔ N.Nonempty) := by
  refine ⟨descentsAfter_double _ (Finset.pairwise_sort N _) q fun y hy =>
    (hqt.trans (hN y ((Finset.mem_sort _).mp hy)).le), ?_⟩
  rw [doubledWord, lastOr_double]
  rcases N.eq_empty_or_nonempty with rfl | hne
  · simp [Finset.sort_empty, lastOr, hqt]
  · have hsort : N.sort (· ≤ ·) ≠ [] := by
      obtain ⟨y, hy⟩ := hne
      exact List.ne_nil_of_mem ((Finset.mem_sort _).mpr hy)
    simp only [hne, iff_true]
    exact hN _ ((Finset.mem_sort _).mp (lastOr_mem q hsort))

-- The wrapped word of a set with least element `t` starts and ends with `t`, and has one inner
-- descent exactly when the set has at least two elements.
private theorem wrapped {T : Finset ℕ} {t : ℕ} (ht : t ∈ T) (hmin : ∀ y ∈ T, t ≤ y) (q : ℕ) :
    descentsAfter q (wrappedWord T) = (if t < q then 1 else 0) + (if 2 ≤ T.card then 1 else 0) ∧
      lastOr q (wrappedWord T) = t ∧ (wrappedWord T).head? = some t := by
  obtain ⟨s, rest, hsr⟩ := List.exists_cons_of_ne_nil
    (List.ne_nil_of_mem ((Finset.mem_sort (s := T) (· ≤ ·)).mpr ht))
  have hpw := Finset.pairwise_sort T (· ≤ ·)
  have hnd := Finset.sort_nodup T (· ≤ ·)
  have hcard := Finset.length_sort (s := T) (· ≤ ·)
  have hmem : ∀ y, y ∈ s :: rest ↔ y ∈ T := fun y => by rw [← hsr, Finset.mem_sort]
  rw [hsr] at hpw hnd hcard
  obtain ⟨hs, hrest⟩ := List.pairwise_cons.mp hpw
  obtain ⟨hsn, -⟩ := List.nodup_cons.mp hnd
  have hst : s = t := by
    refine le_antisymm ?_ (hmin s ((hmem s).mp List.mem_cons_self))
    rcases List.mem_cons.mp ((hmem t).mpr ht) with h | h
    · exact h.ge
    · exact hs t h
  subst hst
  have hw : wrappedWord T = s :: (rest.flatMap (fun x => [x, x]) ++ [s]) := by
    simp [wrappedWord, hsr]
  rw [hw]
  refine ⟨?_, ?_, rfl⟩
  · simp only [descentsAfter, descentsAfter_append, descentsAfter_double rest hrest s hs,
      lastOr_double]
    rcases eq_or_ne rest [] with rfl | hne
    · simp_all [lastOr]
    · have hl := lastOr_mem s hne
      have hlt : s < lastOr s rest := lt_of_le_of_ne (hs _ hl) fun h => hsn (h ▸ hl)
      have h2 : 2 ≤ T.card := by
        have := List.length_pos_of_ne_nil hne
        simp only [List.length_cons] at hcard
        omega
      simp [hlt, h2]
  · simp [lastOr, lastOr_append]

/-! ### Type `B` set partitions and Adler labels -/

variable {n : ℕ} {P : Finpartition (Finset.Icc (-(n : ℤ)) n)}

private theorem mem_neg_image {s : Finset ℤ} {y : ℤ} : y ∈ s.image (fun x => -x) ↔ -y ∈ s := by
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    simpa using hx
  · intro h
    exact Finset.mem_image.mpr ⟨-y, h, neg_neg y⟩

private theorem zero_mem_Icc : (0 : ℤ) ∈ Finset.Icc (-(n : ℤ)) n := by simp

/-- In a type B set partition, the block containing the negative of an element of the
signed interval is the negation of its block. -/
public theorem part_neg (hP : IsTypeBSetPartition P) {x : ℤ}
    (hx : x ∈ Finset.Icc (-(n : ℤ)) n) : P.part (-x) = (P.part x).image (fun x => -x) :=
  P.part_eq_of_mem (hP.1 _ (P.part_mem.mpr hx)) (mem_neg_image.mpr (by simpa using P.mem_part hx))

/-- The zero block of a type B set partition is closed under negation. -/
public theorem neg_mem_part_zero (hP : IsTypeBSetPartition P) {x : ℤ} (hx : x ∈ P.part 0) :
    -x ∈ P.part 0 := by
  have h := part_neg hP (zero_mem_Icc (n := n))
  rw [neg_zero] at h
  rw [h, mem_neg_image, neg_neg]
  exact hx

-- A block containing an element and its negative is the zero block.
private theorem part_eq_part_zero (hP : IsTypeBSetPartition P) {x : ℤ}
    (hx : x ∈ Finset.Icc (-(n : ℤ)) n) (h : -x ∈ P.part x) : P.part x = P.part 0 := by
  have hself : (P.part x).image (fun x => -x) = P.part x := by
    rw [← part_neg hP hx]
    exact P.part_eq_of_mem (P.part_mem.mpr hx) h
  have hzero : (P.part 0).image (fun x => -x) = P.part 0 := by
    rw [← part_neg hP zero_mem_Icc, neg_zero]
  exact hP.2.unique ⟨P.part_mem.mpr hx, hself⟩ ⟨P.part_mem.mpr zero_mem_Icc, hzero⟩

/-- An Adler label is a positive element of the interval that is minimal among the
positive elements of its block and strictly smaller than the magnitudes of its negative elements. -/
public theorem mem_labels {p : ℤ} : p ∈ adlerBlockLabels P ↔
    p ∈ Finset.Icc 1 (n : ℤ) ∧ ∀ q ∈ P.part p, (0 < q → p ≤ q) ∧ (q < 0 → p < -q) :=
  Finset.mem_filter

/-- Every Adler label belongs to the signed interval being partitioned. -/
public theorem mem_Icc_of_label {p : ℤ} (hp : p ∈ adlerBlockLabels P) :
    p ∈ Finset.Icc (-(n : ℤ)) n := by
  have := Finset.mem_Icc.mp (mem_labels.mp hp).1
  simp only [Finset.mem_Icc]
  omega

/-- In a type B set partition, no Adler-labelled block contains zero. -/
public theorem zero_notMem_label (hP : IsTypeBSetPartition P) {p : ℤ}
    (hp : p ∈ adlerBlockLabels P) : (0 : ℤ) ∉ P.part p := by
  intro h0
  have hpI := mem_Icc_of_label hp
  have heq : P.part 0 = P.part p := (P.mem_part_iff_part_eq_part zero_mem_Icc hpI).mp h0
  have hp0 : p ∈ P.part 0 := by
    rw [heq]
    exact P.mem_part hpI
  have hneg : -p ∈ P.part p := by
    rw [← heq]
    exact neg_mem_part_zero hP hp0
  have := ((mem_labels.mp hp).2 _ hneg).2
  have := Finset.mem_Icc.mp (mem_labels.mp hp).1
  omega

private theorem natAbs_injOn (hP : IsTypeBSetPartition P) {p : ℤ}
    (hp : p ∈ adlerBlockLabels P) : Set.InjOn Int.natAbs (P.part p : Set ℤ) := by
  intro y hy z hz h
  rcases Int.natAbs_eq_natAbs_iff.mp h with h | h
  · exact h
  · exfalso
    have hpI := mem_Icc_of_label hp
    have hzI : z ∈ Finset.Icc (-(n : ℤ)) n := P.part_subset p hz
    have hz' : P.part z = P.part p := P.part_eq_of_mem (P.part_mem.mpr hpI) hz
    have hneg : -z ∈ P.part z := by
      rw [hz', ← h]
      exact hy
    have h0 := part_eq_part_zero hP hzI hneg
    apply zero_notMem_label hP hp
    rw [← hz', h0]
    exact P.mem_part zero_mem_Icc

private theorem natAbs_injOn_nonneg (S : Finset ℤ) :
    Set.InjOn Int.natAbs (S.filter (0 ≤ ·) : Set ℤ) := by
  intro x hx y hy h
  have hx' := (Finset.mem_filter.mp hx).2
  have hy' := (Finset.mem_filter.mp hy).2
  omega

private theorem card_typeBShift {S : Finset ℤ} (h : Set.InjOn Int.natAbs (S : Set ℤ)) :
    (typeBShift S).card = S.card :=
  Finset.card_image_of_injOn fun _ ha _ hb hab => h ha hb (Nat.add_right_cancel hab)

/-- Two Adler labels of the same partition that label the same block coincide. -/
public theorem label_eq_of_part_eq {p p' : ℤ} (hp : p ∈ adlerBlockLabels P)
    (hp' : p' ∈ adlerBlockLabels P) (h : P.part p = P.part p') : p = p' := by
  have hmem : p' ∈ P.part p := by
    rw [h]
    exact P.mem_part (mem_Icc_of_label hp')
  have hmem' : p ∈ P.part p' := by
    rw [← h]
    exact P.mem_part (mem_Icc_of_label hp)
  have h1 := Finset.mem_Icc.mp (mem_labels.mp hp).1
  have h2 := Finset.mem_Icc.mp (mem_labels.mp hp').1
  have := ((mem_labels.mp hp).2 p' hmem).1 (by omega)
  have := ((mem_labels.mp hp').2 p hmem').1 (by omega)
  omega

/-- Two Adler-labelled blocks of a partition are never negatives of one another. -/
public theorem part_ne_neg_part {p p' : ℤ} (hp : p ∈ adlerBlockLabels P)
    (hp' : p' ∈ adlerBlockLabels P) : P.part p' ≠ (P.part p).image (fun x => -x) := by
  intro h
  have h1 : -p' ∈ P.part p := by
    have := P.mem_part (mem_Icc_of_label hp')
    rw [h, mem_neg_image] at this
    exact this
  have h2 : -p ∈ P.part p' := by
    rw [h, mem_neg_image, neg_neg]
    exact P.mem_part (mem_Icc_of_label hp)
  have h3 := Finset.mem_Icc.mp (mem_labels.mp hp).1
  have h4 := Finset.mem_Icc.mp (mem_labels.mp hp').1
  have := ((mem_labels.mp hp).2 _ h1).2 (by omega)
  have := ((mem_labels.mp hp').2 _ h2).2 (by omega)
  omega

private theorem mem_labels_of {p : ℤ} (hp : p ∈ Finset.Icc 1 (n : ℤ))
    (hmin : ∀ q ∈ P.part p, p.natAbs ≤ q.natAbs) (hneg : -p ∉ P.part p) :
    p ∈ adlerBlockLabels P := by
  have hp' := Finset.mem_Icc.mp hp
  refine mem_labels.mpr ⟨hp, fun q hq => ⟨fun hq0 => ?_, fun hq0 => ?_⟩⟩
  · have := hmin q hq
    omega
  · have := hmin q hq
    have hne : q ≠ -p := fun h => hneg (h ▸ hq)
    omega

/-- An element of the signed interval outside the zero block of a type B set
partition belongs, up to negation, to an Adler-labelled block. -/
public theorem exists_label (hP : IsTypeBSetPartition P) {x : ℤ}
    (hx : x ∈ Finset.Icc (-(n : ℤ)) n) (hx0 : x ∉ P.part 0) :
    ∃ p ∈ adlerBlockLabels P, x ∈ P.part p ∨ -x ∈ P.part p := by
  obtain ⟨z, hz, hmin⟩ := Finset.exists_min_image (P.part x) Int.natAbs ⟨x, P.mem_part hx⟩
  have hzI : z ∈ Finset.Icc (-(n : ℤ)) n := P.part_subset x hz
  have hpz : P.part z = P.part x := P.part_eq_of_mem (P.part_mem.mpr hx) hz
  have hne : P.part x ≠ P.part 0 := by
    intro h
    apply hx0
    rw [← h]
    exact P.mem_part hx
  have hnz : -z ∉ P.part x := by
    intro h
    rw [← hpz] at h
    exact hne (hpz ▸ part_eq_part_zero hP hzI h)
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact hnz (by simpa using hz)
  have hzI' := Finset.mem_Icc.mp hzI
  rcases hz0.lt_or_gt with hneg | hpos
  · -- The labelled block of the pair is the negative of the block of `x`.
    refine ⟨-z, mem_labels_of (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) ?_ ?_, Or.inr ?_⟩
    · intro q hq
      rw [part_neg hP hzI, hpz, mem_neg_image] at hq
      have := hmin _ hq
      simpa only [Int.natAbs_neg] using this
    · rw [neg_neg, part_neg hP hzI, hpz, mem_neg_image]
      exact hnz
    · rw [part_neg hP hzI, hpz, mem_neg_image, neg_neg]
      exact P.mem_part hx
  · refine ⟨z, mem_labels_of (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) ?_ ?_, Or.inl ?_⟩
    · intro q hq
      rw [hpz] at hq
      exact hmin q hq
    · rw [hpz]
      exact hnz
    · rw [hpz]
      exact P.mem_part hx

-- The absolute values of the zero block's nonnegative elements and of the labelled blocks
-- split `{0, …, n}`.
private theorem card_partition (hP : IsTypeBSetPartition P) :
    ((P.part 0).filter (0 ≤ ·)).card + ∑ p ∈ adlerBlockLabels P, (P.part p).card = n + 1 := by
  have hA : (((P.part 0).filter (0 ≤ ·)).image Int.natAbs ∪
      (adlerBlockLabels P).biUnion fun p => (P.part p).image Int.natAbs) =
        Finset.range (n + 1) := by
    ext y
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_biUnion, Finset.mem_range,
      Finset.mem_filter]
    constructor
    · rintro (⟨x, ⟨hx, -⟩, rfl⟩ | ⟨p, -, x, hx, rfl⟩)
      · have := Finset.mem_Icc.mp (P.part_subset 0 hx)
        omega
      · have := Finset.mem_Icc.mp (P.part_subset p hx)
        omega
    · intro hy
      have hyI : (y : ℤ) ∈ Finset.Icc (-(n : ℤ)) n := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      by_cases h0 : (y : ℤ) ∈ P.part 0
      · exact Or.inl ⟨y, ⟨h0, by omega⟩, by simp⟩
      · obtain ⟨p, hp, h | h⟩ := exists_label hP hyI h0
        · exact Or.inr ⟨p, hp, y, h, by simp⟩
        · exact Or.inr ⟨p, hp, -y, h, by simp⟩
  have hdisj : Disjoint (((P.part 0).filter (0 ≤ ·)).image Int.natAbs)
      ((adlerBlockLabels P).biUnion fun p => (P.part p).image Int.natAbs) := by
    rw [Finset.disjoint_biUnion_right]
    intro p hp
    rw [Finset.disjoint_left]
    intro y hy hy'
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp hy'
    have hx0 : x ∈ P.part 0 := (Finset.mem_filter.mp hx).1
    have hz0 : z ∈ P.part 0 := by
      rcases Int.natAbs_eq_natAbs_iff.mp hzx with rfl | rfl
      · exact hx0
      · exact neg_mem_part_zero hP hx0
    have hpz : P.part p = P.part 0 :=
      (P.part_eq_of_mem (P.part_mem.mpr (mem_Icc_of_label hp)) hz).symm.trans
        (P.part_eq_of_mem (P.part_mem.mpr zero_mem_Icc) hz0)
    apply zero_notMem_label hP hp
    rw [hpz]
    exact P.mem_part zero_mem_Icc
  have hpair : (adlerBlockLabels P : Set ℤ).PairwiseDisjoint
      fun p => (P.part p).image Int.natAbs := by
    intro p hp p' hp' hne
    change Disjoint ((P.part p).image Int.natAbs) ((P.part p').image Int.natAbs)
    rw [Finset.disjoint_left]
    intro y hy hy'
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨z', hz', hzz⟩ := Finset.mem_image.mp hy'
    have hzI : z ∈ Finset.Icc (-(n : ℤ)) n := P.part_subset p hz
    have hpz : P.part z = P.part p :=
      P.part_eq_of_mem (P.part_mem.mpr (mem_Icc_of_label hp)) hz
    have hpz' : P.part z' = P.part p' :=
      P.part_eq_of_mem (P.part_mem.mpr (mem_Icc_of_label hp')) hz'
    rcases Int.natAbs_eq_natAbs_iff.mp hzz with rfl | rfl
    · exact hne (label_eq_of_part_eq hp hp' (hpz.symm.trans hpz'))
    · exact part_ne_neg_part hp hp' (by rw [← hpz', part_neg hP hzI, hpz])
  have hcard := congrArg Finset.card hA
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_biUnion hpair, Finset.card_range,
    Finset.card_image_of_injOn (natAbs_injOn_nonneg _)] at hcard
  rw [← hcard]
  congr 1
  exact Finset.sum_congr rfl fun p hp => (Finset.card_image_of_injOn (natAbs_injOn hP hp)).symm

-- The negative and positive parts of a labelled block make up the whole block.
private theorem card_neg_add_card_pos (hP : IsTypeBSetPartition P) {p : ℤ}
    (hp : p ∈ adlerBlockLabels P) :
    ((P.part p).filter (· < 0)).card + ((P.part p).filter (0 < ·)).card = (P.part p).card := by
  have hfilter : (P.part p).filter (fun x => ¬ x < 0) = (P.part p).filter (0 < ·) :=
    Finset.filter_congr fun x hx => by
      have : x ≠ 0 := fun h => zero_notMem_label hP hp (h ▸ hx)
      omega
  rw [← hfilter]
  exact Finset.card_filter_add_card_filter_not _

/-- The word list of a type B partition of the integer interval `[-n, n]`
has length `2 * (n + 1)`. -/
public theorem length_list (hP : IsTypeBSetPartition P) :
    (typeBFlattenedWordList P).length = 2 * (n + 1) := by
  have hblock : ∀ p ∈ adlerBlockLabels P,
      (doubledWord (typeBShift ((P.part p).filter (· < 0))) ++
        wrappedWord (typeBShift ((P.part p).filter (0 < ·)))).length = 2 * (P.part p).card := by
    intro p hp
    have hinj := natAbs_injOn hP hp
    rw [List.length_append, length_doubledWord, length_wrappedWord,
      card_typeBShift (hinj.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))),
      card_typeBShift (hinj.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))),
      ← card_neg_add_card_pos hP hp]
    omega
  rw [typeBFlattenedWordList, List.length_append, length_wrappedWord, List.length_flatMap,
    sum_sort, card_typeBShift (natAbs_injOn_nonneg _), Finset.sum_congr rfl hblock,
    ← Finset.mul_sum]
  have := card_partition hP
  omega

-- A labelled block contributes a descent for a nonempty negative part and one for a positive
-- part with at least two elements, and its word ends with `|p| + 1`.
private theorem block (hP : IsTypeBSetPartition P) {p : ℤ} (hp : p ∈ adlerBlockLabels P)
    (q : ℕ) (hq : q ≤ p.natAbs + 1) :
    descentsAfter q (doubledWord (typeBShift ((P.part p).filter (· < 0))) ++
        wrappedWord (typeBShift ((P.part p).filter (0 < ·)))) =
      (if ((P.part p).filter (· < 0)).Nonempty then 1 else 0) +
        (if 2 ≤ ((P.part p).filter (0 < ·)).card then 1 else 0) ∧
    lastOr q (doubledWord (typeBShift ((P.part p).filter (· < 0))) ++
        wrappedWord (typeBShift ((P.part p).filter (0 < ·)))) = p.natAbs + 1 := by
  have hpI := mem_Icc_of_label hp
  obtain ⟨hp1, hcond⟩ := mem_labels.mp hp
  have hp1' := Finset.mem_Icc.mp hp1
  have hN : ∀ y ∈ typeBShift ((P.part p).filter (· < 0)), p.natAbs + 1 < y := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hx, hx0⟩ := Finset.mem_filter.mp hx
    have := (hcond x hx).2 hx0
    omega
  have htQ : p.natAbs + 1 ∈ typeBShift ((P.part p).filter (0 < ·)) :=
    Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨P.mem_part hpI, by omega⟩, rfl⟩
  have hQ : ∀ y ∈ typeBShift ((P.part p).filter (0 < ·)), p.natAbs + 1 ≤ y := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hx, hx0⟩ := Finset.mem_filter.mp hx
    have := (hcond x hx).1 hx0
    omega
  obtain ⟨hd, hlast⟩ := doubled hq hN
  obtain ⟨hw, hwl, -⟩ := wrapped htQ hQ
    (lastOr q (doubledWord (typeBShift ((P.part p).filter (· < 0)))))
  have hinj := natAbs_injOn hP hp
  rw [descentsAfter_append, lastOr_append, hd, hw, hwl,
    card_typeBShift (hinj.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)))]
  refine ⟨?_, rfl⟩
  have hne : (typeBShift ((P.part p).filter (· < 0))).Nonempty ↔
      ((P.part p).filter (· < 0)).Nonempty := Finset.image_nonempty
  simp only [hlast, hne, zero_add]

end wordRunCount_typeBFlattenedWord

open wordRunCount_typeBFlattenedWord in
/-- **Number of runs of the word of a type $B$ set partition.** Let $\pi$ be a type $B$ set
partition of $[-n, n]$ and let $\varphi(\pi)$ be the word of length $2(n + 1)$ that the map
$\varphi$ of Proposition 1 assigns to it. Write $P_0$ for the set of nonnegative elements of the
block of $\pi$ containing $0$. Let $\beta_1, \dots, \beta_m$ be the blocks kept by Adler's
labelling, exactly one from each pair $\{\beta, -\beta\}$ of distinct blocks, namely the block
containing the smallest magnitude of the pair as a positive element; write $N_i$ and $P_i$ for
the sets of negative and positive elements of $\beta_i$. Then the number of runs of
$\varphi(\pi)$ is
$$1 + |\{i \ge 1 : |N_i| \ge 1\}| + |\{i \ge 0 : |P_i| \ge 2\}|.$$

The paper states this for a flattened Stirling permutation $w$ of order $n + 1$ and the
partition $\varphi^{-1}(w)$; since $\varphi$ is a bijection from the type $B$ set partitions of
$[-n, n]$ onto these permutations (Theorem 3), this is the same as the statement for
$w = \varphi(\pi)$ over all $\pi$.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Lemma 4. -/
public theorem wordRunCount_typeBFlattenedWord {n : ℕ}
    (P : Finpartition (Finset.Icc (-(n : ℤ)) n)) (hP : IsTypeBSetPartition P) :
    wordRunCount (typeBFlattenedWord P) =
      1 + ((adlerBlockLabels P).filter fun p => ((P.part p).filter (· < 0)).Nonempty).card +
        ((insert 0 (adlerBlockLabels P)).filter fun p =>
          2 ≤ ((P.part p).filter (0 ≤ ·)).card).card := by
  -- The word of the zero block starts and ends with `1`.
  have ht0 : 1 ∈ typeBShift ((P.part 0).filter (0 ≤ ·)) :=
    Finset.mem_image.mpr ⟨0, Finset.mem_filter.mpr ⟨P.mem_part zero_mem_Icc, le_rfl⟩, rfl⟩
  have hmin0 : ∀ y ∈ typeBShift ((P.part 0).filter (0 ≤ ·)), 1 ≤ y := by
    intro y hy
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hy
    omega
  obtain ⟨hd0, hl0, hh0⟩ := wrapped ht0 hmin0 2
  have hrun : wordRunCount (typeBFlattenedWord P) =
      descentsAfter 2 (typeBFlattenedWordList P) := by
    refine wordRunCount_ofList (length_list hP) fun a ha => ?_
    rw [typeBFlattenedWordList, List.head?_append, hh0] at ha
    simp only [Option.some_or, Option.mem_def, Option.some.injEq] at ha
    omega
  have hpw : ((adlerBlockLabels P).sort (· ≤ ·)).Pairwise
      (fun a b => a.natAbs + 1 ≤ b.natAbs + 1) := by
    refine (Finset.pairwise_sort _ _).imp_of_mem fun ha hb hab => ?_
    have := Finset.mem_Icc.mp (mem_labels.mp ((Finset.mem_sort _).mp ha)).1
    have := Finset.mem_Icc.mp (mem_labels.mp ((Finset.mem_sort _).mp hb)).1
    omega
  rw [hrun, typeBFlattenedWordList, descentsAfter_append, hd0, hl0,
    descentsAfter_flatMap _ _ _ _ hpw 1 (fun _ _ => by omega)
      (fun p hp q hq => block hP ((Finset.mem_sort _).mp hp) q hq),
    sum_sort, Finset.sum_add_distrib, card_typeBShift (natAbs_injOn_nonneg _),
    ite_eq_left (show (1 : ℕ) < 2 by decide)]
  have hN : ((adlerBlockLabels P).filter fun p => ((P.part p).filter (· < 0)).Nonempty).card =
      ∑ p ∈ adlerBlockLabels P, if ((P.part p).filter (· < 0)).Nonempty then 1 else 0 :=
    Finset.card_filter _ _
  have h0 : (0 : ℤ) ∉ adlerBlockLabels P := fun h => by
    have := Finset.mem_Icc.mp (mem_labels.mp h).1
    omega
  have hQ : ((insert 0 (adlerBlockLabels P)).filter fun p =>
        2 ≤ ((P.part p).filter (0 ≤ ·)).card).card =
      (if 2 ≤ ((P.part 0).filter (0 ≤ ·)).card then 1 else 0) +
        ∑ p ∈ adlerBlockLabels P, if 2 ≤ ((P.part p).filter (0 < ·)).card then 1 else 0 := by
    rw [Finset.card_filter (fun p => 2 ≤ ((P.part p).filter (0 ≤ ·)).card)
      (insert 0 (adlerBlockLabels P)), Finset.sum_insert h0]
    congr 1
    refine Finset.sum_congr rfl fun p hp => ?_
    -- A labelled block does not contain `0`.
    have hf : (P.part p).filter (0 ≤ ·) = (P.part p).filter (0 < ·) :=
      Finset.filter_congr fun x hx => by
        have : x ≠ 0 := fun h => zero_notMem_label hP hp (h ▸ hx)
        omega
    rw [hf]
  rw [hN, hQ]
  omega

end MetaMathlibExt
