/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.AP.Basic
public import MathlibExt.Combinatorics.Additive.RestrictedSignedSumset
import Mathlib.Data.Finset.Sort

/-!
# Nathanson's inverse theorem for restricted sumsets

`MetaMathlibExt.nathanson_restrictedSumset_inverse` characterizes the equality case
of the bound `h * (k - h) + 1` for restricted sums of a `k`-element set of integers
when `k ≥ 5` and `2 ≤ h ≤ k - 2`.
-/

namespace MetaMathlibExt

open Finset

namespace nathanson_restrictedSumset_inverse

/-- A set of indices other than the initial segment admits a one-step move to the left. -/
private lemma exists_left_move {B : Finset ℕ} (hne : B ≠ range B.card) :
    ∃ i, i + 1 ∈ B ∧ i ∉ B := by
  by_contra! h
  have down {m n : ℕ} (hmn : m ≤ n) (hn : n ∈ B) : m ∈ B := by
    induction n, hmn using Nat.le_induction with
    | base => exact hn
    | succ n _ ih => exact ih (h n hn)
  apply hne
  apply eq_of_subset_of_card_le _ (by simp)
  intro n hn
  have hs : range (n + 1) ⊆ B := fun i hi => down (Nat.le_of_lt_succ (mem_range.mp hi)) hn
  simpa using card_le_card hs

/-- Moving an index one step to the right increases the sum of the selected values.
Any increasing natural-valued rank of these sums therefore bounds the number of steps
from the initial segment, namely the excess in the sum of the indices. -/
private lemma index_sum_le {k h : ℕ} {f : ℕ → ℤ} (hf : StrictMonoOn f (range k : Set ℕ))
    {S : Set ℤ} (hS : ∀ B ⊆ range k, B.card = h → B.sum f ∈ S)
    {r : ℤ → ℕ} (hr : StrictMonoOn r S) (B : Finset ℕ) (hB : B ⊆ range k) (hc : B.card = h) :
    B.sum id ≤ (range h).sum id + r (B.sum f) := by
  by_cases he : B = range B.card
  · rw [hc] at he
    simp [he]
  obtain ⟨i, hi, hni⟩ := exists_left_move he
  let C := B.erase (i + 1)
  have hiC : i ∉ C := fun h => hni (mem_of_mem_erase h)
  have hsC : C ⊆ range k := (erase_subset _ _).trans hB
  have hi' := mem_range.mp (hB hi)
  have hiB : i ∈ range k := mem_range.mpr (by omega)
  have hs : insert i C ⊆ range k := insert_subset hiB hsC
  have hcard : (insert i C).card = h := by
    rw [card_insert_of_notMem hiC, card_erase_of_mem hi]
    have := card_pos.mpr ⟨_, hi⟩
    omega
  have sumB {M : Type} [AddCommMonoid M] (g : ℕ → M) : B.sum g = g (i + 1) + C.sum g :=
    (add_sum_erase B g hi).symm
  have hlt : (insert i C).sum f < B.sum f := by
    rw [sum_insert hiC, sumB f]
    exact add_lt_add_left (hf hiB (hB hi) (Nat.lt_succ_self _)) _
  have hlt' := hr (hS _ hs hcard) (hS _ hB hc) hlt
  have ih := index_sum_le hf hS hr (insert i C) hs hcard
  rw [sum_insert hiC] at ih
  rw [sumB id]
  simp only [id_eq] at ih ⊢
  omega
termination_by B.sum id
decreasing_by
  rw [sum_insert hiC, sumB id]
  simp

/-- At the minimum cardinality, the rank of a sum is determined by its index sum.
The lower rank bound on the complementary selection gives the matching upper bound. -/
private lemma sum_eq_of_index_sum_eq {k h : ℕ} (hhk : h ≤ k) {f : ℕ → ℤ}
    (hf : StrictMonoOn f (range k : Set ℕ)) {S : Finset ℤ}
    (hS : ∀ B ⊆ range k, B.card = h → B.sum f ∈ S) (hsize : S.card = h * (k - h) + 1)
    {B C : Finset ℕ} (hB : B ⊆ range k) (hcB : B.card = h)
    (hC : C ⊆ range k) (hcC : C.card = h) (heq : B.sum id = C.sum id) :
    B.sum f = C.sum f := by
  let rank := S.sort.idxOf
  have rank_eq {x : ℤ} (hx : x ∈ S) :
      rank x = ((S.orderIsoOfFin rfl).symm ⟨x, hx⟩).val :=
    (S.orderIsoOfFin_symm_apply rfl ⟨x, hx⟩).symm
  have hr : StrictMonoOn rank (S : Set ℤ) := by
    intro x hx y hy hxy
    rw [rank_eq hx, rank_eq hy]
    exact (S.orderIsoOfFin rfl).symm.strictMono (show (⟨x, hx⟩ : S) < ⟨y, hy⟩ from hxy)
  have bounded {x : ℤ} (hx : x ∈ S) : rank x ≤ h * (k - h) := by
    have := ((S.orderIsoOfFin rfl).symm ⟨x, hx⟩).isLt
    rw [rank_eq hx]
    omega
  let total := (range k).sum f
  let dual (x : ℤ) := h * (k - h) - rank (total - x)
  have hd : StrictMonoOn dual {x | total - x ∈ S} := by
    intro x hx y hy hxy
    have hlt := hr hy hx (show total - y < total - x by omega)
    have := bounded hx
    dsimp only [dual]
    omega
  have hcomp (D : Finset ℕ) (hD : D ⊆ range k) (hcD : D.card = k - h) :
      total - D.sum f ∈ S := by
    rw [show total - D.sum f = ((range k) \ D).sum f from (sum_sdiff_eq_sub hD).symm]
    apply hS _ sdiff_subset
    rw [card_sdiff_of_subset hD, card_range, hcD]
    omega
  have triangle : (range k).sum id =
      (range h).sum id + (range (k - h)).sum id + h * (k - h) := by
    conv_lhs => rw [← Nat.sub_add_cancel hhk, sum_range_add]
    change (range (k - h)).sum id + (∑ x ∈ range h, ((k - h) + x)) = _
    rw [sum_add_distrib]
    simp [Nat.add_comm, Nat.add_left_comm]
  have exactRank (D : Finset ℕ) (hD : D ⊆ range k) (hcD : D.card = h) :
      D.sum id = (range h).sum id + rank (D.sum f) := by
    have lower := index_sum_le hf hS hr D hD hcD
    have hcc : ((range k) \ D).card = k - h := by simp [card_sdiff_of_subset hD, hcD]
    have upper := index_sum_le hf hcomp hd _ sdiff_subset hcc
    have hsum : ((range k) \ D).sum id + D.sum id = (range k).sum id := sum_sdiff hD
    have hb := bounded (hS _ hD hcD)
    simp only [dual, sum_sdiff_eq_sub hD, total, sub_sub_cancel] at upper
    change ((range k) \ D).sum id ≤ (range (k - h)).sum id + (_ - rank (D.sum f)) at upper
    omega
  apply hr.injOn (hS _ hB hcB) (hS _ hC hcC)
  have := exactRank B hB hcB
  have := exactRank C hC hcC
  omega

/-- Exchange the endpoints of two disjoint gaps, keeping the other indices fixed. -/
private lemma separated_gaps_eq {k h : ℕ} (hh : 2 ≤ h) (hhk : h + 2 ≤ k) {f : ℕ → ℤ}
    (hf : StrictMonoOn f (range k : Set ℕ)) {S : Finset ℤ}
    (hS : ∀ B ⊆ range k, B.card = h → B.sum f ∈ S) (hsize : S.card = h * (k - h) + 1)
    ⦃i j : ℕ⦄ (hij : i + 1 < j) (hj : j + 1 < k) :
    f (i + 1) - f i = f (j + 1) - f j := by
  let E : Finset ℕ := {i, i + 1, j, j + 1}
  have hsE : E ⊆ range k := by
    intro n hn
    simp only [E, mem_insert, mem_singleton] at hn
    exact mem_range.mpr (by omega)
  have room : h - 2 ≤ ((range k) \ E).card := by
    rw [card_sdiff_of_subset hsE, card_range]
    have : E.card ≤ 4 := card_le_four
    omega
  obtain ⟨P, hsP, hcP⟩ := exists_subset_card_eq room
  have outside {n : ℕ} (hn : n ∈ E) : n ∉ P := fun h => (mem_sdiff.mp (hsP h)).2 hn
  have pair {a b : ℕ} (ha : a ∈ E) (hb : b ∈ E) (hab : a ≠ b) :
      insert a (insert b P) ⊆ range k ∧ (insert a (insert b P)).card = h := by
    refine ⟨insert_subset (hsE ha) (insert_subset (hsE hb) (hsP.trans sdiff_subset)), ?_⟩
    rw [card_insert_of_notMem (by simp [hab, outside ha]), card_insert_of_notMem (outside hb)]
    omega
  have hi₀ : i ∈ E := by simp [E]
  have hi₁ : i + 1 ∈ E := by simp [E]
  have hj₀ : j ∈ E := by simp [E]
  have hj₁ : j + 1 ∈ E := by simp [E]
  have hij' : i ≠ j + 1 := by omega
  have left := pair hi₀ hj₁ hij'
  have right := pair hi₁ hj₀ hij.ne
  have e := sum_eq_of_index_sum_eq (by omega) hf hS hsize left.1 left.2 right.1 right.2
  simp [sum_insert, outside hi₀, outside hi₁, outside hj₀, outside hj₁, hij', hij.ne] at e
  omega

end nathanson_restrictedSumset_inverse

open nathanson_restrictedSumset_inverse

/-- **Nathanson's inverse theorem for restricted sumsets.** Let $A$ be a finite set of integers
with $k = |A| \ge 5$ elements and let $h$ be an integer with $2 \le h \le k - 2$. Write
$h^{\wedge} A$ for the restricted sumset of $A$, the set of sums of $h$ distinct elements of
$A$. If $|h^{\wedge} A| = hk - h^2 + 1$, then $A$ is an arithmetic progression of length $k$.

Source: Jagannath Bhanja, *Sumsets with a Minimum Number of Distinct Terms*, INTEGERS 25 (2025),
Article A12, Theorem 4 (Nathanson) (`integers-2025-A12-thm-4`). -/
public theorem nathanson_restrictedSumset_inverse (A : Finset ℤ) (hk : 5 ≤ A.card)
    (h : ℕ) (hh : 2 ≤ h) (hhk : h ≤ A.card - 2)
    (hcard : (restrictedSumset h A).card = h * A.card - h ^ 2 + 1) :
    (A : Set ℤ).IsAPOfLength A.card := by
  let f (i : ℕ) := if hi : i < A.card then A.orderEmbOfFin rfl ⟨i, hi⟩ else 0
  have enum (i : ℕ) (hi : i < A.card) : f i = A.orderEmbOfFin rfl ⟨i, hi⟩ := by simp [f, hi]
  have mono : StrictMonoOn f (range A.card : Set ℕ) := by
    intro i hi j hj hij
    rw [enum i (mem_range.mp hi), enum j (mem_range.mp hj)]
    exact (A.orderEmbOfFin rfl).strictMono hij
  have memS (B : Finset ℕ) (hB : B ⊆ range A.card) (hc : B.card = h) :
      B.sum f ∈ restrictedSumset h A := by
    have inj := mono.injOn.mono (show (B : Set ℕ) ⊆ range A.card from hB)
    refine mem_image.mpr ⟨B.image f, mem_powersetCard.mpr ⟨?_, (card_image_of_injOn inj).trans hc⟩,
      sum_image inj⟩
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    rw [enum i (mem_range.mp (hB hi))]
    exact orderEmbOfFin_mem ..
  have size : (restrictedSumset h A).card = h * (A.card - h) + 1 := by
    simpa [Nat.mul_sub, pow_two] using hcard
  have separated := separated_gaps_eq hh (by omega) mono memS size
  let d := f 1 - f 0
  have gap (i : ℕ) (hi : i + 1 < A.card) : f (i + 1) - f i = d := by
    rcases i with _ | i
    · rfl
    rcases i with _ | i
    · exact (separated (i := 1) (j := 3) (by decide) (by omega)).trans
        (separated (i := 0) (j := 3) (by decide) (by omega)).symm
    · exact (separated (i := 0) (by omega) hi).symm
  have term (i : ℕ) (hi : i < A.card) : f i = f 0 + i • d := by
    induction i with
    | zero => simp
    | succ i ih =>
      rw [succ_nsmul, ← add_assoc, ← ih (by omega)]
      have := gap i hi
      omega
  refine ⟨f 0, d, by simp, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨i, rfl⟩ : x ∈ Set.range (A.orderEmbOfFin rfl) := by simpa using hx
    exact ⟨i.val, by exact_mod_cast i.isLt, (term i i.isLt).symm.trans (enum i i.isLt)⟩
  · rintro ⟨i, hi, rfl⟩
    have hi' : i < A.card := by exact_mod_cast hi
    rw [← term i hi', enum i hi']
    exact orderEmbOfFin_mem ..

end MetaMathlibExt
