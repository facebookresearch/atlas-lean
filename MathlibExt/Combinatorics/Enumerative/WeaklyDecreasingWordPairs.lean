/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Sym.Card

/-!
# Non-intersecting pairs of weakly decreasing words

A weakly decreasing word is determined by the multiset of its letters, and the set of letters it
uses is the support of that multiset. Splitting pairs of multisets with disjoint supports by the
support of the first one and counting each part by stars and bars gives the number of pairs of
weakly decreasing words of equal length with no common letter
(`weaklyDecreasingNonIntersectingPairs_sameLength_card`).
-/

namespace MetaMathlibExt

namespace WeaklyDecreasingWordPairs

open Finset

section Sorting

variable {α : Type*} {n : ℕ}

/-- The multiset of letters of a word. -/
private def toSym (u : Fin n → α) : Sym α n :=
  Sym.mk ↑(List.ofFn u) (by simp)

private theorem coe_toSym (u : Fin n → α) : (toSym u : Multiset α) = ↑(List.ofFn u) :=
  rfl

private theorem toFinset_toSym [DecidableEq α] (u : Fin n → α) :
    (toSym u : Multiset α).toFinset = univ.image u := by
  rw [coe_toSym, ← Fin.univ_val_map]
  rfl

variable [LinearOrder α]

private theorem length_sort (A : Sym α n) : ((A : Multiset α).sort (· ≥ ·)).length = n := by
  rw [Multiset.length_sort, Sym.card_coe]

/-- The weakly decreasing word listing the letters of a multiset. -/
private def ofSym (A : Sym α n) : Fin n → α :=
  fun i => ((A : Multiset α).sort (· ≥ ·)).get (Fin.cast (length_sort A).symm i)

private theorem ofFn_ofSym (A : Sym α n) :
    List.ofFn (ofSym A) = (A : Multiset α).sort (· ≥ ·) :=
  (List.ofFn_congr (length_sort A) _).symm.trans (List.ofFn_get _)

private theorem sortedGE_sort (A : Sym α n) : ((A : Multiset α).sort (· ≥ ·)).SortedGE :=
  List.sortedGE_iff_pairwise.2 (Multiset.pairwise_sort _ _)

private theorem antitone_ofSym (A : Sym α n) : Antitone (ofSym A) := by
  rw [← List.sortedGE_ofFn_iff, ofFn_ofSym]
  exact sortedGE_sort A

private theorem toSym_ofSym (A : Sym α n) : toSym (ofSym A) = A := by
  apply Sym.ext
  rw [coe_toSym, ofFn_ofSym, Multiset.sort_eq]

private theorem ofSym_toSym {u : Fin n → α} (hu : Antitone u) : ofSym (toSym u) = u := by
  apply List.ofFn_injective
  rw [ofFn_ofSym]
  refine List.Perm.eq_of_sortedGE (sortedGE_sort _) hu.sortedGE_ofFn ?_
  rw [← Multiset.coe_eq_coe, Multiset.sort_eq, coe_toSym]

end Sorting

section Counting

/-- Pairs of weakly decreasing words correspond to pairs of multisets of letters. -/
private theorem card_words_eq_card_sym (k n r : ℕ) :
    ((univ : Finset ((Fin n → Fin k) × (Fin r → Fin k))).filter fun p => Antitone p.1 ∧
        Antitone p.2 ∧ Disjoint (univ.image p.1) (univ.image p.2)).card =
      ((univ : Finset (Sym (Fin k) n × Sym (Fin k) r)).filter
        fun q : Sym (Fin k) n × Sym (Fin k) r =>
          Disjoint (q.1 : Multiset (Fin k)).toFinset (q.2 : Multiset (Fin k)).toFinset).card := by
  refine card_nbij' (fun p => (toSym p.1, toSym p.2)) (fun q => (ofSym q.1, ofSym q.2))
    ?_ ?_ ?_ ?_
  · rintro ⟨u, v⟩ h
    simp only [mem_coe, mem_filter, mem_univ, true_and] at h ⊢
    rw [toFinset_toSym, toFinset_toSym]
    exact h.2.2
  · rintro ⟨A, B⟩ h
    simp only [mem_coe, mem_filter, mem_univ, true_and] at h ⊢
    refine ⟨antitone_ofSym A, antitone_ofSym B, ?_⟩
    rw [← toFinset_toSym, ← toFinset_toSym, toSym_ofSym, toSym_ofSym]
    exact h
  · rintro ⟨u, v⟩ h
    simp only [mem_coe, mem_filter, mem_univ, true_and] at h
    simp only [ofSym_toSym h.1, ofSym_toSym h.2.1]
  · rintro ⟨A, B⟩ _
    simp only [toSym_ofSym]

/-- Split the pairs of multisets with disjoint supports by the support of the first one. -/
private theorem card_sym_eq_sum (k n r : ℕ) :
    ((univ : Finset (Sym (Fin k) n × Sym (Fin k) r)).filter
        fun q : Sym (Fin k) n × Sym (Fin k) r =>
          Disjoint (q.1 : Multiset (Fin k)).toFinset (q.2 : Multiset (Fin k)).toFinset).card =
      ∑ S ∈ (univ : Finset (Fin k)).powerset,
        ((univ : Finset (Sym (Fin k) n)).filter fun A : Sym (Fin k) n =>
          (A : Multiset (Fin k)).toFinset = S).card * (Sᶜ.sym r).card := by
  rw [card_eq_sum_card_fiberwise (f := fun q => (q.1 : Multiset (Fin k)).toFinset)
    (t := (univ : Finset (Fin k)).powerset) (fun _ _ => mem_powerset.2 (subset_univ _))]
  refine sum_congr rfl fun S _ => ?_
  rw [← card_product]
  congr 1
  ext ⟨A, B⟩
  simp only [mem_filter, mem_univ, true_and, mem_product, mem_sym_iff, mem_compl]
  constructor
  · rintro ⟨hd, rfl⟩
    exact ⟨rfl, fun a ha haS => disjoint_left.1 hd haS (Multiset.mem_toFinset.2 ha)⟩
  · rintro ⟨rfl, h⟩
    exact ⟨disjoint_left.2 fun a ha hb => h a (Multiset.mem_toFinset.1 hb) ha, rfl⟩

/-- Stars and bars inside a set of letters. -/
private theorem card_sym_finset {k : ℕ} (T : Finset (Fin k)) (m : ℕ) :
    (T.sym m).card = T.card.multichoose m := by
  calc (T.sym m).card = ((T.attach.map (Function.Embedding.subtype (· ∈ T))).sym m).card := by
        rw [attach_map_val]
    _ = (T.attach.sym m).card := by rw [sym_map, card_map]
    _ = Fintype.card (Sym T m) := by rw [← univ_eq_attach, sym_univ, card_univ]
    _ = T.card.multichoose m := by rw [Sym.card_sym_eq_multichoose, Fintype.card_coe]

/-- A multiset of size `n ≥ 1` has a nonempty support. -/
private theorem card_toFinset_eq_empty (k n : ℕ) (hn : 1 ≤ n) :
    ((univ : Finset (Sym (Fin k) n)).filter fun A : Sym (Fin k) n =>
      (A : Multiset (Fin k)).toFinset = ∅).card = 0 := by
  rw [card_eq_zero, filter_eq_empty_iff]
  intro A _ hA
  have hcard := Sym.card_coe (s := A)
  rw [Multiset.toFinset_eq_empty.1 hA, Multiset.card_zero] at hcard
  omega

/-- Removing one copy of each letter of the support leaves a multiset of size `n - #S` on `S`. -/
private theorem card_toFinset_eq (k n : ℕ) (hn : 1 ≤ n) (S : Finset (Fin k)) (hS : S.Nonempty) :
    ((univ : Finset (Sym (Fin k) n)).filter fun A : Sym (Fin k) n =>
      (A : Multiset (Fin k)).toFinset = S).card = (n - 1).choose (S.card - 1) := by
  have hpos : 0 < S.card := hS.card_pos
  rcases le_or_gt S.card n with hle | hlt
  · have hcard (C : Sym (Fin k) (n - S.card)) :
        Multiset.card ((C : Multiset (Fin k)) + S.val) = n := by
      rw [Multiset.card_add, Sym.card_coe, card_val]
      omega
    have key : (S.sym (n - S.card)).card = ((univ : Finset (Sym (Fin k) n)).filter
        fun A : Sym (Fin k) n => (A : Multiset (Fin k)).toFinset = S).card := by
      refine card_bij (fun C _ => Sym.mk ((C : Multiset (Fin k)) + S.val) (hcard C)) ?_ ?_ ?_
      · intro C hC
        rw [mem_sym_iff] at hC
        rw [mem_filter, Sym.coe_mk]
        refine ⟨mem_univ _, ?_⟩
        ext a
        rw [Multiset.mem_toFinset, Multiset.mem_add, Sym.mem_coe, mem_val]
        exact ⟨fun h => h.elim (hC a) id, Or.inr⟩
      · intro C _ C' _ h
        rw [← Sym.coe_inj, Sym.coe_mk, Sym.coe_mk] at h
        exact Sym.ext (add_right_cancel h)
      · intro A hA
        rw [mem_filter] at hA
        have hle : S.val ≤ (A : Multiset (Fin k)) :=
          (Multiset.le_iff_subset S.nodup).2 fun a ha => by
            rw [← hA.2] at ha
            exact Multiset.mem_toFinset.1 ha
        refine ⟨Sym.mk ((A : Multiset (Fin k)) - S.val)
          (by rw [Multiset.card_sub hle, Sym.card_coe, card_val]), ?_, ?_⟩
        · rw [mem_sym_iff]
          intro a ha
          rw [← Sym.mem_coe, Sym.coe_mk] at ha
          rw [← hA.2]
          exact Multiset.mem_toFinset.2 (Multiset.mem_of_le (Multiset.sub_le_self _ _) ha)
        · apply Sym.ext
          rw [Sym.coe_mk, Sym.coe_mk]
          exact tsub_add_cancel_of_le hle
    rw [← key, card_sym_finset, Nat.multichoose_eq,
      show S.card + (n - S.card) - 1 = n - 1 by omega]
    exact Nat.choose_symm_of_eq_add (show n - 1 = (n - S.card) + (S.card - 1) by omega)
  · rw [Nat.choose_eq_zero_of_lt (show n - 1 < S.card - 1 by omega), card_eq_zero,
      filter_eq_empty_iff]
    intro A _ hA
    have h := Multiset.toFinset_card_le (A : Multiset (Fin k))
    rw [hA, Sym.card_coe] at h
    omega

/-- The number of pairs of weakly decreasing words of lengths `n ≥ 1` and `r ≥ 1` over `k`
letters with no common letter. -/
private theorem card_eq_sum (k n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) :
    ((univ : Finset ((Fin n → Fin k) × (Fin r → Fin k))).filter fun p => Antitone p.1 ∧
        Antitone p.2 ∧ Disjoint (univ.image p.1) (univ.image p.2)).card =
      ∑ j ∈ Icc 1 (k - 1), k.choose j * (n - 1).choose (j - 1) * (r + k - j - 1).choose r := by
  let f : ℕ → ℕ := fun j => (if j = 0 then 0 else (n - 1).choose (j - 1)) * (k - j).multichoose r
  have hterm : ∀ S ∈ (univ : Finset (Fin k)).powerset,
      ((univ : Finset (Sym (Fin k) n)).filter fun A : Sym (Fin k) n =>
        (A : Multiset (Fin k)).toFinset = S).card * (Sᶜ.sym r).card = f S.card := by
    intro S _
    rcases S.eq_empty_or_nonempty with rfl | hS
    · rw [card_toFinset_eq_empty k n hn]
      simp [f]
    · rw [card_toFinset_eq k n hn S hS, card_sym_finset, card_compl, Fintype.card_fin]
      simp [f, hS.card_pos.ne']
  have hrange : ∑ j ∈ Icc 1 (k - 1), k.choose j * (n - 1).choose (j - 1) *
      (r + k - j - 1).choose r = ∑ j ∈ range (k + 1), k.choose j • f j := by
    rw [← sum_subset (s₁ := Icc 1 (k - 1)) (s₂ := range (k + 1))]
    · refine sum_congr rfl fun j hj => ?_
      simp only [mem_Icc] at hj
      simp only [f, smul_eq_mul, ite_eq_right (show j ≠ 0 by omega), Nat.multichoose_eq,
        show k - j + r - 1 = r + k - j - 1 by omega, mul_assoc]
    · intro j hj
      simp only [mem_Icc, mem_range] at hj ⊢
      omega
    · intro j hj hj'
      simp only [mem_Icc, mem_range] at hj hj'
      rcases (show j = 0 ∨ j = k by omega) with rfl | rfl
      · simp [f]
      · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le' hr
        simp [f, Nat.multichoose_zero_succ]
  rw [card_words_eq_card_sym, card_sym_eq_sum, sum_congr rfl hterm, sum_powerset_apply_card,
    card_univ, Fintype.card_fin, hrange]

end Counting

end WeaklyDecreasingWordPairs

/-- **Non-intersecting pairs of weakly decreasing words of equal length.** For natural numbers $k$
and $n \ge 1$, the number of pairs $(u, v)$ of weakly decreasing words of length $n$ over an
ordered alphabet of $k$ letters such that no letter occurs in both is
$\sum_{j=1}^{k-1} \binom{k}{j} \binom{n-1}{j-1} \binom{n+k-j-1}{n}$.

Source: Aubrey Blecher and Arnold Knopfmacher, *Intersections in Pairs of Words*, INTEGERS 24
(2024), Article A107, Corollary 5 (`integers-2024-A107-cor-5`). -/
public theorem weaklyDecreasingNonIntersectingPairs_sameLength_card (k n : ℕ) (hn : 1 ≤ n) :
    ((Finset.univ : Finset ((Fin n → Fin k) × (Fin n → Fin k))).filter fun p => Antitone p.1 ∧
        Antitone p.2 ∧ Disjoint (Finset.univ.image p.1) (Finset.univ.image p.2)).card =
      ∑ j ∈ Finset.Icc 1 (k - 1), k.choose j * (n - 1).choose (j - 1) * (n + k - j - 1).choose n :=
  WeaklyDecreasingWordPairs.card_eq_sum k n n hn hn

end MetaMathlibExt
