/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.FlattenedStirlingPermutations
import MathlibExt.Combinatorics.Enumerative.FlattenedStirlingTypeBRuns
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Infix

/-!
# The flattened Stirling word of a type B partition

The word of a type B partition is a Stirling permutation whose run leaders weakly increase.
The two occurrences of a letter are adjacent or enclose larger letters in one wrapped block.
Every descent returns to the shifted minimum of the current block.
-/

namespace MetaMathlibExt
namespace typeBFlattenedWord_mem_flattenedStirling

/-! ### The two positions of each letter -/

-- A contiguous factor witnesses the Stirling condition for a pair of occurrences.
private def Paired (v : ℕ) (l : List ℕ) : Prop :=
  ∃ middle : List ℕ, (∀ x ∈ middle, v < x) ∧ (v :: (middle ++ [v])) <:+: l

private theorem Paired.infix {v : ℕ} {l r : List ℕ} (h : Paired v l) (hl : l <:+: r) :
    Paired v r := by
  obtain ⟨m, hm, hf⟩ := h
  exact ⟨m, hm, hf.trans hl⟩

private theorem paired_double {v : ℕ} {xs : List ℕ} (hv : v ∈ xs) :
    Paired v (xs.flatMap fun x => [x, x]) :=
  ⟨[], by simp, List.infix_flatMap_of_mem hv (fun x => [x, x])⟩

private theorem paired_wrap {v : ℕ} {S : Finset ℕ} (hv : v ∈ S) : Paired v (wrappedWord S) := by
  have hmem := (Finset.mem_sort (· ≤ ·)).mpr hv
  have hsort := S.sortedLT_sort.pairwise
  cases hs : S.sort (· ≤ ·) with
  | nil => simp [hs] at hmem
  | cons a xs =>
    rw [hs] at hmem hsort
    simp only [wrappedWord, hs]
    rcases List.mem_cons.mp hmem with rfl | hv'
    · refine ⟨xs.flatMap (fun x => [x, x]), ?_, List.infix_rfl⟩
      intro y hy
      obtain ⟨x, hx, hy⟩ := List.mem_flatMap.mp hy
      have heq : y = x := by simpa using hy
      exact heq ▸ (List.pairwise_cons.mp hsort).1 x hx
    · exact (paired_double hv').infix
        (List.infix_append_left.trans (List.suffix_cons _ _).isInfix)

variable {n : ℕ} {P : Finpartition (Finset.Icc (-(n : ℤ)) n)}

private abbrev blockWord (P : Finpartition (Finset.Icc (-(n : ℤ)) n)) (p : ℤ) : List ℕ :=
  doubledWord (typeBShift ((P.part p).filter (· < 0))) ++
    wrappedWord (typeBShift ((P.part p).filter (0 < ·)))

private theorem paired_list (hP : IsTypeBSetPartition P) {v : ℕ} (hv : v ∈ Finset.Icc 1 (n + 1)) :
    Paired v (typeBFlattenedWordList P) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show v ≠ 0 by
    have := Finset.mem_Icc.mp hv
    omega)
  have hk := Finset.mem_Icc.mp hv
  have hkI : (k : ℤ) ∈ Finset.Icc (-(n : ℤ)) n := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  change Paired (k + 1) (wrappedWord (typeBShift ((P.part 0).filter (0 ≤ ·))) ++
    ((adlerBlockLabels P).sort (· ≤ ·)).flatMap (blockWord P))
  by_cases h0 : (k : ℤ) ∈ P.part 0
  · apply Paired.infix _ List.infix_append_left
    apply paired_wrap
    exact Finset.mem_image.mpr ⟨(k : ℤ), Finset.mem_filter.mpr ⟨h0, by omega⟩, rfl⟩
  · have hk0 : k ≠ 0 := by
      rintro rfl
      exact h0 (P.mem_part (by simp))
    obtain ⟨p, hp, hsign⟩ := hP.exists_mem_adlerBlockLabels hkI h0
    apply Paired.infix _ List.infix_append_right
    have hlabel := (List.singleton_infix_iff _ _).mpr ((Finset.mem_sort (· ≤ ·)).mpr hp)
    apply Paired.infix (l := blockWord P p) _ (by simpa using hlabel.flatMap (blockWord P))
    rcases hsign with hpos | hneg
    · apply Paired.infix _ List.infix_append_right
      apply paired_wrap
      exact Finset.mem_image.mpr ⟨(k : ℤ), Finset.mem_filter.mpr ⟨hpos, by omega⟩, rfl⟩
    · apply Paired.infix _ List.infix_append_left
      apply paired_double
      exact (Finset.mem_sort _).mpr (Finset.mem_image.mpr
        ⟨-(k : ℤ), Finset.mem_filter.mpr ⟨hneg, by omega⟩, by simp⟩)

-- Read the endpoints and the interior of the factor in the indexed word.
private theorem positions {v m : ℕ} {l : List ℕ} (hm : l.length = m) (h : Paired v l) :
    ∃ a c : Fin m, a < c ∧ l.getD a 0 = v ∧ l.getD c 0 = v ∧
      ∀ b : Fin m, a < b → b < c → v < l.getD b 0 := by
  obtain ⟨middle, hmid, before, after, rfl⟩ := h
  simp only [List.length_append, List.length_cons, List.length_nil] at hm
  let a : Fin m := ⟨before.length, by omega⟩
  let c : Fin m := ⟨before.length + 1 + middle.length, by omega⟩
  have read (i : ℕ) (hi : i < middle.length + 2) :
      (before ++ (v :: (middle ++ [v])) ++ after).getD (before.length + i) 0 =
        (v :: (middle ++ [v])).getD i 0 := by
    rw [List.getD_append _ _ _ _ (by simp; omega),
      List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]
  refine ⟨a, c, by simp [a, c, Fin.lt_def]; omega, ?_, ?_, ?_⟩
  · simp [a]
  · simp [c, Nat.add_assoc, Nat.add_comm 1 middle.length]
  · intro b hab hbc
    change before.length < b.val at hab
    change b.val < before.length + 1 + middle.length at hbc
    let j := b.val - (before.length + 1)
    have hj : j < middle.length := by dsimp [j]; omega
    have heq : b.val = before.length + (j + 1) := by dsimp [j]; omega
    rw [heq, read _ (by omega), List.getD_cons_succ, List.getD_append _ _ _ _ hj,
      List.getD_eq_getElem _ _ hj]
    exact hmid _ (List.getElem_mem hj)

-- The pairs already account for all 2m positions, so they are the complete fibers.
private theorem stirling_of_pairs {m : ℕ} {w : Fin (2 * m) → ℕ}
    (pairs : ∀ v ∈ Finset.Icc 1 m, ∃ a c, a < c ∧ w a = v ∧ w c = v ∧
      ∀ b, a < b → b < c → v < w b) : IsStirlingPermutation m w := by
  let fiber (v : ℕ) := Finset.univ.filter fun i => w i = v
  have subset_pair {v : ℕ} {a c : Fin (2 * m)} (ha : w a = v) (hc : w c = v) :
      {a, c} ⊆ fiber v := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · simpa [fiber] using ha
    · simpa [fiber, Finset.mem_singleton.mp hi] using hc
  have lower (v) (hv : v ∈ Finset.Icc 1 m) : 2 ≤ (fiber v).card := by
    obtain ⟨a, c, hac, ha, hc, -⟩ := pairs v hv
    simpa [Finset.card_pair hac.ne] using Finset.card_le_card (subset_pair ha hc)
  have total : ∑ v ∈ Finset.Icc 1 m, (fiber v).card ≤ 2 * m := by
    rw [show (∑ v ∈ Finset.Icc 1 m, (fiber v).card) =
      (Finset.univ.filter (fun i => w i ∈ Finset.Icc 1 m)).card from
      Finset.sum_card_fiberwise_eq_card_filter _ _ _]
    simpa using Finset.card_le_univ (Finset.univ.filter (fun i => w i ∈ Finset.Icc 1 m))
  have size : ∑ _v ∈ Finset.Icc 1 m, 2 = 2 * m := by simp [Nat.card_Icc, Nat.mul_comm]
  have counts (v) (hv : v ∈ Finset.Icc 1 m) : (fiber v).card = 2 := by
    by_contra! h
    have hlt := Finset.sum_lt_sum lower ⟨v, hv, lt_of_le_of_ne (lower v hv) (Ne.symm h)⟩
    omega
  have all_letters : Finset.univ.filter (fun i => w i ∈ Finset.Icc 1 m) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
    rw [← Finset.sum_card_fiberwise_eq_card_filter, Finset.sum_congr rfl counts]
    simpa using size.ge
  refine ⟨fun i => Finset.filter_eq_self.mp all_letters i (Finset.mem_univ _), counts, ?_⟩
  intro v hv i j k hij hjk hi hk
  obtain ⟨a, c, hac, ha, hc, hbetween⟩ := pairs v hv
  have eq_fiber := Finset.eq_of_subset_of_card_le (subset_pair ha hc)
    (by rw [counts v hv, Finset.card_pair hac.ne])
  have endpoint (t : Fin (2 * m)) (ht : w t = v) : t = a ∨ t = c := by
    have hmem : t ∈ fiber v := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩
    simpa [← eq_fiber] using hmem
  rcases endpoint i hi with rfl | rfl <;> rcases endpoint k hk with rfl | rfl
  all_goals first | exact hbetween j hij hjk | omega

/-! ### The order of the run leaders -/

-- Include a possible descent from the preceding letter to the first letter of this suffix.
private def DropAt (prev : ℕ) (l : List ℕ) (i : ℕ) : Prop :=
  l.getD i 0 < (prev :: l).getD i 0

private structure OrderedFrom (lower prev : ℕ) (l : List ℕ) : Prop where
  bound : ∀ i < l.length, DropAt prev l i → lower ≤ l.getD i 0
  ordered : ∀ i j, i < j → j < l.length → DropAt prev l i → DropAt prev l j →
    l.getD i 0 ≤ l.getD j 0

-- On a descent the new lower bound is the letter at the bottom of that descent.
private theorem ordered_cons {lo next prev x : ℕ} {l : List ℕ} (h : OrderedFrom next x l)
    (hle : lo ≤ next) (hdrop : x < prev → lo ≤ x ∧ x ≤ next) : OrderedFrom lo prev (x :: l) := by
  constructor
  · intro i hi hd
    cases i with
    | zero => exact (hdrop hd).1
    | succ i => exact hle.trans (h.bound i (by simpa using hi) hd)
  · intro i j hij hj hi hd
    cases j with
    | zero => omega
    | succ j =>
      cases i with
      | zero => exact (hdrop hi).2.trans (h.bound j (by simpa using hj) hd)
      | succ i => exact h.ordered i j (by omega) (by simpa using hj) hi hd

-- A sorted, doubled prefix adds no descent when all its letters are at least the previous one.
private theorem ordered_double {lo : ℕ} {tail : List ℕ} (htail : ∀ q, OrderedFrom lo q tail)
    (xs : List ℕ) (hs : xs.Pairwise (· ≤ ·)) (prev : ℕ) (hp : ∀ x ∈ xs, prev ≤ x) :
    OrderedFrom lo prev ((xs.flatMap fun x => [x, x]) ++ tail) := by
  induction xs generalizing prev with
  | nil => exact htail prev
  | cons x xs ih =>
    obtain ⟨hx, hs⟩ := List.pairwise_cons.mp hs
    apply ordered_cons (next := lo) _ le_rfl (fun h => (h.not_ge (hp x List.mem_cons_self)).elim)
    exact ordered_cons (ih hs x hx) le_rfl (fun h => (lt_irrefl _ h).elim)

-- Both possible descents into a wrapped word land on its least letter.
private theorem ordered_wrap {S : Finset ℕ} {t lo : ℕ} {tail : List ℕ} (ht : t ∈ S)
    (hmin : ∀ x ∈ S, t ≤ x) (hle : lo ≤ t) (htail : OrderedFrom t t tail) (prev : ℕ) :
    OrderedFrom lo prev (wrappedWord S ++ tail) := by
  let xs := (S.erase t).sort (· ≤ ·)
  have hxs : ∀ x ∈ xs, t ≤ x := fun x hx =>
    hmin x (Finset.mem_of_mem_erase ((Finset.mem_sort _).mp hx))
  have hsort := Finset.sort_insert (s := S.erase t) (· ≤ ·)
    (fun x hx => hmin x (Finset.mem_of_mem_erase hx)) (by simp)
  rw [Finset.insert_erase ht] at hsort
  simp only [wrappedWord_eq_of_sort_eq hsort, List.cons_append, List.append_assoc]
  apply ordered_cons (next := t) _ hle (fun _ => ⟨hle, le_rfl⟩)
  apply ordered_double _ xs (Finset.pairwise_sort _ _) t hxs
  intro q
  exact ordered_cons htail le_rfl (fun _ => ⟨le_rfl, le_rfl⟩)

private theorem ordered_block {p : ℤ} (hp : p ∈ adlerBlockLabels P) {lo : ℕ} {tail : List ℕ}
    (hle : lo ≤ p.natAbs + 1) (htail : OrderedFrom (p.natAbs + 1) (p.natAbs + 1) tail) :
    OrderedFrom lo lo (blockWord P p ++ tail) := by
  obtain ⟨hpI, hcond⟩ := mem_adlerBlockLabels.mp hp
  have hp' := Finset.mem_Icc.mp hpI
  have ht : p.natAbs + 1 ∈ typeBShift ((P.part p).filter (0 < ·)) :=
    mem_typeBShift.mpr ⟨p, Finset.mem_filter.mpr
      ⟨P.mem_part (mem_Icc_of_mem_adlerBlockLabels hp), by omega⟩, rfl⟩
  rw [blockWord, List.append_assoc]
  apply ordered_double _ _ (Finset.pairwise_sort _ _) lo
  · intro x hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ((Finset.mem_sort _).mp hx)
    obtain ⟨hq, hn⟩ := Finset.mem_filter.mp hq
    have := (hcond q hq).2 hn
    omega
  · apply ordered_wrap ht _ hle htail
    intro x hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hq, hpos⟩ := Finset.mem_filter.mp hq
    have := (hcond q hq).1 hpos
    omega

private theorem ordered_blocks (ps : List ℤ) (hmem : ∀ p ∈ ps, p ∈ adlerBlockLabels P)
    (hs : ps.Pairwise (· ≤ ·)) (lo : ℕ) (hlo : ∀ p ∈ ps, lo ≤ p.natAbs + 1) :
    OrderedFrom lo lo (ps.flatMap (blockWord P)) := by
  induction ps generalizing lo with
  | nil => exact ⟨by simp, by simp⟩
  | cons p ps ih =>
    obtain ⟨hp, hs⟩ := List.pairwise_cons.mp hs
    have hp' := Finset.mem_Icc.mp (mem_adlerBlockLabels.mp (hmem p List.mem_cons_self)).1
    apply ordered_block (hmem p List.mem_cons_self) (hlo p List.mem_cons_self)
    apply ih (fun q hq => hmem q (List.mem_cons_of_mem _ hq)) hs
    intro q hq
    have := hp q hq
    omega

private theorem flattened_list (hP : IsTypeBSetPartition P) :
    IsFlattenedWord (typeBFlattenedWord P) := by
  let l := typeBFlattenedWordList P
  have h : OrderedFrom 1 (l.getD 0 0 + 1) l := by
    apply ordered_wrap (t := 1) _ _ le_rfl
    · apply ordered_blocks _ (fun _ => (Finset.mem_sort _).mp) (Finset.pairwise_sort _ _)
      simp
    · exact Finset.mem_image.mpr
        ⟨0, Finset.mem_filter.mpr ⟨P.mem_part (by simp), le_rfl⟩, rfl⟩
    · intro x hx
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hx
      omega
  have drop (i : Fin (2 * (n + 1))) (hi : wordRunStart (typeBFlattenedWord P) i) :
      DropAt (l.getD 0 0 + 1) l i := by
    rcases hi with hi | ⟨j, hj, hd⟩
    · simp [DropAt, hi]
    · change l.getD i 0 < l.getD j 0 at hd
      simpa [DropAt, ← hj] using hd
  intro i j hij hi hj
  exact h.ordered i j hij
    (by rw [show l.length = _ from hP.length_typeBFlattenedWordList]; exact j.isLt)
    (drop i hi) (drop j hj)

end typeBFlattenedWord_mem_flattenedStirling

open typeBFlattenedWord_mem_flattenedStirling in
/-- **The word of a type $B$ set partition is a flattened Stirling permutation.** For every
natural number $n$ and every type $B$ set partition $P$ of $[-n, n] = \{-n, \dots, n\}$, the word
$\varphi(P) = w_1 w_2 \cdots w_{2(n+1)}$ of $P$ is a Stirling permutation of order $n + 1$ and is
flattened.

Source: arXiv:2306.13034, Proposition 3.6; the INTEGERS record is truncated after
"let `π_i = N_i P_i` be as in", and the statement is completed from the arXiv text.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Proposition 1. -/
public theorem typeBFlattenedWord_mem_flattenedStirling {n : ℕ}
    (P : Finpartition (Finset.Icc (-(n : ℤ)) n)) (hP : IsTypeBSetPartition P) :
    IsStirlingPermutation (n + 1) (typeBFlattenedWord P) ∧
      IsFlattenedWord (typeBFlattenedWord P) := by
  exact ⟨stirling_of_pairs (fun v hv =>
    positions hP.length_typeBFlattenedWordList (paired_list hP hv)), flattened_list hP⟩

end MetaMathlibExt
