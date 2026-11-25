/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# Zero subset sums in cyclic groups

We prove the Erdős–Heilbronn square-root bound for nonempty zero-sum subsets in cyclic groups.

The proof works in finite abelian groups. Induction on the group order ensures that a large
reserve of unused elements generates the group. Translating the current set of subset sums
by a suitable reserve element then gives enough growth to construct two disjoint blocks
whose subset sums contain nonzero elements that cancel.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.ZeroSubsetSumSqrtErdosProblem540Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #540, https://www.erdosproblems.com/540 (status PROVED
(LEAN)). UnsolvedMath record UM-30006923 (`EP-540`), dataset ulamai/UnsolvedMath v1.8.0.

`≫ N ^ (1/2)` is `|A| ≥ C √N` for one absolute `C`. Compared with the formal-conjectures statement
`ErdosProblems/540.lean` (equivalent; no code imported).
-/

/-- **The Erdős–Heilbronn zero subset sum statement (Erdős Problem 540).** This is the statement
that there is a real number $C > 0$ such that for every integer $N \ge 1$, every set
$A \subseteq \mathbb{Z}/N\mathbb{Z}$ with $|A| \ge C\sqrt{N}$ has a nonempty subset $S \subseteq A$
whose elements sum to $0$ in $\mathbb{Z}/N\mathbb{Z}$. -/
def sqrtSizeHasZeroSubsetSum : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N → ∀ A : Finset (ZMod N), C * Real.sqrt N ≤ A.card →
    ∃ S ⊆ A, S.Nonempty ∧ ∑ x ∈ S, x = 0

open Finset
open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

private lemma mem_translate {a x : G} {S : Finset G} :
    x ∈ {a} + S ↔ x - a ∈ S := by
  simp only [mem_add, mem_singleton, exists_eq_left]
  exact ⟨fun ⟨y, hy, he⟩ => (eq_sub_of_add_eq (add_comm y a |>.trans he)) ▸ hy,
    fun h => ⟨x - a, h, (add_comm a (x - a)).trans (sub_add_cancel x a)⟩⟩

/-- The number of new points contributed by a translate. -/
private def growth (S : Finset G) (a : G) : ℕ :=
  #(({a} + S) \ S)

private lemma growth_neg (S : Finset G) (a : G) : growth S (-a) = growth S a := by
  have h : {a} + (({-a} + S) \ S) = S \ ({a} + S) := by
    ext x
    simp [mem_translate, sub_neg_eq_add]
  unfold growth
  rw [card_sdiff_comm (card_singleton_add a S), ← h, card_singleton_add]

private lemma growth_add_le (S : Finset G) (a b : G) :
    growth S (a + b) ≤ growth S a + growth S b := by
  calc
    _ ≤ #((({a} + S) \ S) ∪ ({a} + (({b} + S) \ S))) := by
      apply card_le_card
      intro x hx
      simp only [mem_sdiff, mem_translate] at hx ⊢
      by_cases h : x - a ∈ S
      · exact mem_union_left _ (mem_sdiff.mpr ⟨mem_translate.mpr h, hx.2⟩)
      · apply mem_union_right
        simpa [mem_translate, h, sub_sub] using hx.1
    _ ≤ _ := by simpa [growth, card_singleton_add] using
      card_union_le (s := ({a} + S) \ S) (t := {a} + (({b} + S) \ S))

/-- A collection of at least twice as many shifts as points includes one with small overlap. -/
private lemma exists_growth_ge_half {S D : Finset G} (hS : S.Nonempty)
    (hD : 2 * #S ≤ #D) : ∃ a ∈ D, #S ≤ 2 * growth S a := by
  have hcount : (∑ a ∈ D, #(S ∩ ({a} + S))) ≤ #S * #S := by
    rw [← card_sigma, ← card_product]
    apply card_le_card_of_injOn (fun p : (_ : G) × G => (p.2 - p.1, p.2))
    · intro p hp
      have hp' := (mem_inter.mp (mem_sigma.mp hp).2)
      exact mem_product.mpr ⟨mem_translate.mp hp'.2, hp'.1⟩
    · intro p _ q _ he
      have hy := congrArg Prod.snd he
      have hx := congrArg Prod.fst he
      change p.2 - p.1 = q.2 - q.1 at hx
      change p.2 = q.2 at hy
      rw [hy] at hx
      exact Sigma.ext (sub_right_injective hx) (heq_of_eq hy)
  by_contra! h
  have hD' : D.Nonempty := card_pos.mp (by have := hS.card_pos; omega)
  have hlt : #D * #S < 2 * ∑ a ∈ D, #(S ∩ ({a} + S)) := by
    rw [mul_sum, ← sum_const_nat (s := D) (fun _ _ => rfl : ∀ a ∈ D, #S = #S)]
    apply sum_lt_sum_of_nonempty hD'
    intro a ha
    have hc := card_sdiff_add_card_inter ({a} + S) S
    rw [card_singleton_add, inter_comm] at hc
    have := h a ha
    unfold growth at this
    omega
  have hle := Nat.mul_le_mul_right #S hD
  rw [Nat.mul_assoc] at hle
  exact hle.not_gt (hlt.trans_le (Nat.mul_le_mul_left 2 hcount))

section

variable [Fintype G]

/-- In a generating symmetric set, a ball gains a disjoint translate of the radius-one ball
every three steps, until it reaches the whole group. -/
private lemma card_nsmul_ge (B : Finset G) (h0 : 0 ∈ B) (hneg : -B ⊆ B)
    (hgen : AddSubgroup.closure (B : Set G) = ⊤) (k : ℕ) :
    min (Fintype.card G) ((k + 1) * #B) ≤ #((3 * k + 1) • B) := by
  have hmono : Monotone (fun j : ℕ => j • B) := by
    apply monotone_nat_of_le_succ
    intro j x hx
    rw [succ_nsmul B]
    simpa using add_mem_add hx h0
  have hstep (j : ℕ) (hj : j • B ≠ univ) : j • B ⊂ (j + 1) • B := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hmono (Nat.le_succ j), fun he => hj ?_⟩
    have hfixed (m : ℕ) : m • B ⊆ j • B := by
      induction m with
      | zero => exact hmono (Nat.zero_le j)
      | succ m ih =>
        rw [succ_nsmul B, he, succ_nsmul B]
        exact add_subset_add ih Subset.rfl
    let M : AddSubmonoid G :=
      { carrier := (j • B : Finset G)
        zero_mem' := hfixed 0 (by simp)
        add_mem' := fun {x y} hx hy => hfixed (j + j) (by
          rw [add_nsmul]
          exact add_mem_add hx hy) }
    have hB : (B : Set G) ⊆ M := fun x hx => hfixed 1 (by simpa using hx)
    have htop : (⊤ : AddSubmonoid G) ≤ M := by
      change (⊤ : AddSubgroup G).toAddSubmonoid ≤ M
      rw [← hgen, AddSubgroup.closure_toAddSubmonoid,
        AddSubmonoid.closure_le]
      exact Set.union_subset hB (fun x hx => hB (hneg (by simpa using hx)))
    exact eq_univ_iff_forall.mpr fun x => htop (AddSubmonoid.mem_top x)
  induction k with
  | zero => simp
  | succ k ih =>
    let j := 3 * k + 1
    change min (Fintype.card G) ((k + 1 + 1) * #B) ≤ #((j + 3) • B)
    by_cases hfull : (j + 3) • B = univ
    · simp [hfull]
    have hproper (i : ℕ) (hi : i ≤ j + 3) : i • B ≠ univ := by
      intro he
      apply hfull
      rw [← univ_subset_iff, ← he]
      exact hmono hi
    obtain ⟨x, hx, hx'⟩ := (ssubset_iff_of_subset (hmono (Nat.le_succ (j + 1)))).mp
      (hstep (j + 1) (hproper (j + 1) (by omega)))
    change x ∉ (j + 1) • B at hx'
    have hdisj : Disjoint (j • B) ({x} + B) := by
      refine disjoint_left.mpr fun y hy hy' => hx' ?_
      have hyB := mem_translate.mp hy'
      have hxy : x = y + -(y - x) := by abel
      rw [hxy, succ_nsmul B]
      exact add_mem_add hy (hneg (neg_mem_neg hyB))
    have hsub : (j • B) ∪ ({x} + B) ⊆ (j + 3) • B := by
      refine union_subset (hmono (by omega)) ?_
      rw [show j + 3 = (j + 1 + 1) + 1 by omega, succ_nsmul B]
      exact add_subset_add (singleton_subset_iff.mpr hx) Subset.rfl
    have hcard := card_le_card hsub
    rw [card_union_of_disjoint hdisj, card_singleton_add] at hcard
    have hjcard : #(j • B) < Fintype.card G := by
      rw [← card_univ]
      exact card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨subset_univ _, hproper _ (by omega)⟩)
    have ih' : (k + 1) * #B ≤ #(j • B) := by
      exact (min_le_iff.mp ih).resolve_left (not_le_of_gt hjcard)
    rw [Nat.add_mul, one_mul]
    exact (min_le_right _ _).trans ((Nat.add_le_add_right ih' _).trans hcard)

private lemma exists_large_growth (S R : Finset G) (hS : S.Nonempty) (hR : R.Nonempty)
    (hsize : 2 * #S ≤ Fintype.card G) (hgen : AddSubgroup.closure (R : Set G) = ⊤) :
    ∃ a ∈ R, min #S #R ≤ 14 * growth S a := by
  obtain ⟨a, ha, hmax⟩ := exists_max_image R (growth S) hR
  let B : Finset G := insert 0 (R ∪ -R)
  have hRB : R ⊆ B := fun _ hx => mem_insert_of_mem (mem_union_left _ hx)
  have hB : ∀ x ∈ B, growth S x ≤ growth S a := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · simp [growth, show ({0} : Finset G) = 0 from rfl]
    rcases mem_union.mp hx with hx | hx
    · exact hmax x hx
    · rw [← growth_neg S x]
      exact hmax (-x) (mem_neg'.mp hx)
  have hbound (j : ℕ) : ∀ x ∈ j • B, growth S x ≤ j * growth S a := by
    induction j with
    | zero => simp [growth, show ({0} : Finset G) = 0 from rfl]
    | succ j ih =>
      intro x hx
      rw [succ_nsmul B] at hx
      obtain ⟨y, hy, z, hz, rfl⟩ := mem_add.mp hx
      rw [Nat.add_mul, one_mul]
      exact (growth_add_le S y z).trans (Nat.add_le_add (ih y hy) (hB z hz))
  have hneg : -B ⊆ B := by
    intro x hx
    simp only [B, mem_neg', mem_insert, mem_union, neg_eq_zero, neg_neg] at hx ⊢
    exact hx.imp id Or.symm
  have hBgen : AddSubgroup.closure (B : Set G) = ⊤ := by
    apply top_unique
    rw [← hgen]
    exact AddSubgroup.closure_mono hRB
  let k := (2 * #S) / #R
  have hD := card_nsmul_ge B (mem_insert_self _ _) hneg hBgen k
  have hsize' : 2 * #S ≤ #((3 * k + 1) • B) := by
    refine (le_min hsize ?_).trans hD
    exact (Nat.lt_mul_div_succ (2 * #S) hR.card_pos).le.trans
      (by rw [mul_comm]; exact Nat.mul_le_mul_left _ (card_le_card hRB))
  obtain ⟨x, hx, hlarge⟩ := exists_growth_ge_half hS hsize'
  have hmul : (3 * k + 1) * min #S #R ≤ 7 * #S := by
    rcases le_total #S #R with h | h
    · rw [min_eq_left h]
      have hk : k ≤ 2 := Nat.div_le_of_le_mul (by omega)
      exact Nat.mul_le_mul_right _ (by omega)
    · rw [min_eq_right h, Nat.add_mul, one_mul, Nat.mul_assoc]
      have hk : k * #R ≤ 2 * #S := Nat.div_mul_le_self _ _
      have := Nat.mul_le_mul_left 3 hk
      omega
  refine ⟨a, ha, Nat.le_of_mul_le_mul_left ?_ (by omega : 0 < 3 * k + 1)⟩
  have hx' := hbound _ x hx
  nlinarith only [hmul, hlarge, hx']

end

/-- All subset sums, including the sum of the empty subset. -/
private def subsetSums (B : Finset G) : Finset G :=
  B.powerset.image fun T => ∑ x ∈ T, x

private lemma mem_subsetSums {B : Finset G} {x : G} :
    x ∈ subsetSums B ↔ ∃ T ⊆ B, ∑ y ∈ T, y = x := by
  simp only [subsetSums, mem_image, mem_powerset]

private lemma zero_mem_subsetSums (B : Finset G) : 0 ∈ subsetSums B :=
  mem_subsetSums.mpr ⟨∅, empty_subset _, sum_empty⟩

private lemma card_le_subsetSums (B : Finset G) : #B ≤ #(subsetSums B) := by
  apply card_le_card
  intro x hx
  exact mem_subsetSums.mpr ⟨{x}, singleton_subset_iff.mpr hx, sum_singleton _ _⟩

private lemma subsetSums_insert {B : Finset G} {a : G} (ha : a ∉ B) :
    subsetSums (insert a B) = ({a} + subsetSums B) ∪ subsetSums B := by
  ext x
  simp only [subsetSums, powerset_insert, image_union, image_image, mem_union, mem_image,
    mem_powerset, mem_add, mem_singleton, exists_eq_left, Function.comp_apply]
  constructor
  · rintro (h | ⟨T, hT, rfl⟩)
    · exact Or.inr h
    · exact Or.inl ⟨_, ⟨T, hT, rfl⟩, (sum_insert (f := fun x : G => x) (fun hx => ha (hT hx))).symm⟩
  · rintro (⟨_, ⟨T, hT, rfl⟩, rfl⟩ | h)
    · exact Or.inr ⟨T, hT, sum_insert (fun hx => ha (hT hx))⟩
    · exact Or.inl h

private lemma card_subsetSums_insert {B : Finset G} {a : G} (ha : a ∉ B) :
    #(subsetSums (insert a B)) = growth (subsetSums B) a + #(subsetSums B) := by
  rw [subsetSums_insert ha, growth, card_sdiff_add_card]

/-- A set whose only zero-sum subset is the empty one. -/
private def ZeroSumFree (A : Finset G) : Prop :=
  ∀ ⦃T : Finset G⦄, T ⊆ A → T.Nonempty → ∑ x ∈ T, x ≠ 0

private lemma growth_pos_of_zeroSumFree {A B : Finset G} {a : G}
    (hfree : ZeroSumFree A) (hBA : B ⊆ A) (ha : a ∈ A) (hna : a ∉ B) :
    0 < growth (subsetSums B) a := by
  have hnot : 0 ∉ {a} + subsetSums B := by
    rw [mem_translate, zero_sub]
    intro h
    obtain ⟨T, hT, hsum⟩ := mem_subsetSums.mp h
    apply hfree (insert_subset ha (hT.trans hBA)) (insert_nonempty _ _)
    rw [sum_insert (fun hx => hna (hT hx)), hsum, add_neg_cancel]
  rw [growth, card_sdiff_comm (card_singleton_add a _)]
  exact (show (subsetSums B \ ({a} + subsetSums B)).Nonempty from
    ⟨0, mem_sdiff.mpr ⟨zero_mem_subsetSums B, hnot⟩⟩).card_pos

private lemma not_zeroSumFree_of_large_subsetSums [Fintype G] {A B C : Finset G}
    (hB : B ⊆ A) (hC : C ⊆ A) (hBC : Disjoint B C)
    (hcard : Fintype.card G + 1 < #(subsetSums B) + #(subsetSums C)) :
    ¬ZeroSumFree A := by
  intro hfree
  have hinter : 1 < #(subsetSums B ∩ -subsetSums C) := by
    have h := card_union_add_card_inter (subsetSums B) (-subsetSums C)
    rw [card_neg] at h
    have := card_le_univ (s := subsetSums B ∪ -subsetSums C)
    omega
  obtain ⟨x, hx, hx0⟩ : ∃ x ∈ subsetSums B ∩ -subsetSums C, x ≠ (0 : G) := by
    by_contra! h
    have hc := card_le_card (t := ({0} : Finset G)) fun x hx => mem_singleton.mpr (h x hx)
    simpa using not_le_of_gt hinter hc
  obtain ⟨T, hT, hsumT⟩ := mem_subsetSums.mp (mem_inter.mp hx).1
  obtain ⟨U, hU, hsumU⟩ := mem_subsetSums.mp (mem_neg'.mp (mem_inter.mp hx).2)
  have hne : T.Nonempty := by
    rw [nonempty_iff_ne_empty]
    rintro rfl
    exact hx0 (hsumT.symm.trans sum_empty)
  apply hfree (union_subset (hT.trans hB) (hU.trans hC)) (hne.mono subset_union_left)
  rw [sum_union (hBC.mono hT hU), hsumT, hsumU, add_neg_cancel]

/-- Add at most `k` elements to a seed of size `k` so its subset sums exceed half the group,
then add one more element to ensure two such blocks have a nonzero pair of opposite sums. -/
private lemma exists_large_block [Fintype G] {A U : Finset G} {k : ℕ}
    (hfree : ZeroSumFree A) (hU : U ⊆ A) (huCard : #U ≤ 2 * k + 1)
    (hk : 0 < k) (hkA : 24 * k ≤ #A) (hkG : 14 * Fintype.card G ≤ k * k)
    (hgen : ∀ R ⊆ A, 3 * #A ≤ 4 * #R → AddSubgroup.closure (R : Set G) = ⊤) :
    ∃ B ⊆ A \ U, #B ≤ 2 * k + 1 ∧ Fintype.card G + 1 < 2 * #(subsetSums B) := by
  have hreserve (B : Finset G) (hB : B ⊆ A \ U) (hBc : #B ≤ 2 * k) :
      3 * #A ≤ 4 * #((A \ U) \ B) := by
    rw [card_sdiff_of_subset hB, card_sdiff_of_subset hU]
    omega
  have hnonempty (B : Finset G) (hB : B ⊆ A \ U) (hBc : #B ≤ 2 * k) :
      ((A \ U) \ B).Nonempty :=
    card_pos.mp (by have := hreserve B hB hBc; omega)
  have hbuild (j : ℕ) (hj : j ≤ k) :
      ∃ B ⊆ A \ U, k ≤ #B ∧ #B ≤ k + j ∧
        (Fintype.card G < 2 * #(subsetSums B) ∨ j * k ≤ 14 * #(subsetSums B)) := by
    induction j with
    | zero =>
      have hc : k ≤ #(A \ U) := by rw [card_sdiff_of_subset hU]; omega
      obtain ⟨B, hB, rfl⟩ := exists_subset_card_eq hc
      exact ⟨B, hB, le_rfl, by simp, Or.inr (by simp)⟩
    | succ j ih =>
      obtain ⟨B, hB, hBk, hBc, hlarge | hprogress⟩ := ih (by omega)
      · exact ⟨B, hB, hBk, by omega, Or.inl hlarge⟩
      have hBc' : #B ≤ 2 * k := by omega
      let R := (A \ U) \ B
      have hrCard := hreserve B hB hBc'
      have hR := hnonempty B hB hBc'
      by_cases hlarge : Fintype.card G < 2 * #(subsetSums B)
      · exact ⟨B, hB, hBk, by omega, Or.inl hlarge⟩
      obtain ⟨a, ha, hgrowth⟩ := exists_large_growth (subsetSums B) R
        ⟨0, zero_mem_subsetSums B⟩ hR (by omega)
        (hgen R (sdiff_subset.trans sdiff_subset) hrCard)
      obtain ⟨haU, haB⟩ := mem_sdiff.mp ha
      have hsmall : k ≤ min #(subsetSums B) #R :=
        le_min (hBk.trans (card_le_subsetSums B)) (by change 3 * #A ≤ 4 * #R at hrCard; omega)
      refine ⟨insert a B, insert_subset haU hB, ?_, ?_, Or.inr ?_⟩
      · rw [card_insert_of_notMem haB]; omega
      · rw [card_insert_of_notMem haB]; omega
      · rw [card_subsetSums_insert haB, Nat.succ_mul]
        have := hsmall.trans hgrowth
        omega
  obtain ⟨B, hB, _, hBc, hlarge⟩ := hbuild k le_rfl
  have hlarge' : Fintype.card G < 2 * #(subsetSums B) := by
    have hn : 0 < Fintype.card G := Fintype.card_pos
    exact hlarge.elim id (fun h => by omega)
  obtain ⟨a, ha⟩ := hnonempty B hB (by omega)
  obtain ⟨haU, haB⟩ := mem_sdiff.mp ha
  refine ⟨insert a B, insert_subset haU hB, ?_, ?_⟩
  · rw [card_insert_of_notMem haB]; omega
  · rw [card_subsetSums_insert haB]
    have := growth_pos_of_zeroSumFree hfree (hB.trans sdiff_subset) (mem_sdiff.mp haU).1 haB
    omega

universe u

/-- A finite abelian group of order `n` has no zero-sum-free set with squared cardinality
at least `40000 * n`. The induction forces every reserve of at least three quarters of such a
set to generate the group. -/
private lemma not_zeroSumFree_of_card_sq (n : ℕ) :
    ∀ (G : Type u) [AddCommGroup G] [Fintype G],
      Fintype.card G = n → ∀ A : Finset G, 40000 * n ≤ #A * #A → ¬ZeroSumFree A := by
  classical
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro G _ _ hn A hA hfree
    have hnpos : 0 < n := hn ▸ Fintype.card_pos
    have hAn : #A ≤ n := hn ▸ card_le_univ A
    have hApos : 0 < #A := by
      by_contra! h
      have he : #A = 0 := by omega
      simp [he] at hA
      omega
    have hgen (R : Finset G) (hRA : R ⊆ A) (hR : 3 * #A ≤ 4 * #R) :
        AddSubgroup.closure (R : Set G) = ⊤ := by
      let H := AddSubgroup.closure (R : Set G)
      change H = ⊤
      by_contra hproper
      let : Fintype H := Fintype.ofFinite H
      have hindex : H.index * Fintype.card H = n := by
        simpa only [Nat.card_eq_fintype_card, hn] using H.index_mul_card
      have hhalf : 2 * Fintype.card H ≤ n := hindex ▸
        Nat.mul_le_mul_right (Fintype.card H) (AddSubgroup.one_lt_index_of_ne_top hproper)
      have hHlt : Fintype.card H < n := by omega
      let e : R ↪ H := Subtype.impEmbedding _ _ fun _ hx => AddSubgroup.subset_closure hx
      let R' := R.attach.map e
      have hR' : #R' = #R := by simp [R']
      let v : H ↪ G := Function.Embedding.subtype _
      have hmap : R'.map v = R := by
        rw [show R' = R.attach.map e from rfl, map_map]
        exact attach_map_val
      have hbound : 40000 * Fintype.card H ≤ #R' * #R' := by
        rw [hR']
        nlinarith only [Nat.mul_le_mul hR hR, hA, hhalf]
      apply ih (Fintype.card H) hHlt H rfl R' hbound
      intro S hS hne hsum
      have hsub : S.map v ⊆ A := (map_subset_map.mpr hS).trans (hmap ▸ hRA)
      apply hfree hsub hne.map
      rw [sum_map]
      change (∑ x ∈ S, H.subtype x) = 0
      rw [← map_sum, hsum, map_zero]
    have hAlarge : 40000 ≤ #A := Nat.le_of_mul_le_mul_right
      ((Nat.mul_le_mul_left 40000 hAn).trans hA) hApos
    let k := #A / 24
    have hkA : 24 * k ≤ #A := Nat.mul_div_le _ _
    have hkA' : #A < 24 * (k + 1) := Nat.lt_mul_div_succ _ (by decide)
    have hk : 0 < k := by omega
    have hm : #A ≤ 25 * k := by omega
    have hkG : 14 * Fintype.card G ≤ k * k := by
      rw [hn]
      nlinarith only [Nat.mul_le_mul hm hm, hA, hnpos]
    obtain ⟨B, hB, hBc, hBlarge⟩ := exists_large_block (U := ∅) hfree
      (empty_subset A) (by simp) hk hkA hkG hgen
    rw [sdiff_empty] at hB
    obtain ⟨C, hC, _, hClarge⟩ := exists_large_block hfree hB hBc hk hkA hkG hgen
    exact not_zeroSumFree_of_large_subsetSums hB (hC.trans sdiff_subset)
      (disjoint_sdiff.mono_right hC) (by omega) hfree

/--
**Zero subset sums of large sets in $\mathbb{Z}/N\mathbb{Z}$ (Erdős Problem 540).** There is a real
number $C > 0$ such that for every integer $N \ge 1$, every set $A \subseteq \mathbb{Z}/N\mathbb{Z}$
with $|A| \ge C\sqrt{N}$ has a nonempty subset $S \subseteq A$ whose elements sum to $0$ in
$\mathbb{Z}/N\mathbb{Z}$.

Resolved true: Olson proved it for prime $N$ and Szemerédi for all $N$ (in every finite abelian
group); Hamidoune and Zémor showed $(1 + o(1))\sqrt{2N}$ suffices.

Source: T. F. Bloom, Erdős Problems,
Problem #540, https://www.erdosproblems.com/540 (status PROVED (LEAN)); resolution: E. Szemerédi, On
a conjecture of Erdős and Heilbronn, Acta Arith. (1970), 227-229, erdosproblems.com/540: yes; Olson
for N prime, Szemerédi for all N (indeed for all finite abelian groups),
https://www.erdosproblems.com/540.
-/
public theorem sqrtSizeHasZeroSubsetSum_holds : sqrtSizeHasZeroSubsetSum := by
  refine ⟨200, by norm_num, ?_⟩
  intro N hn A hA
  let : NeZero N := ⟨Nat.ne_of_gt hn⟩
  have hsq : (200 : ℝ) ^ 2 * (N : ℝ) ≤ (A.card : ℝ) ^ 2 := by
    rw [← Real.sq_sqrt (Nat.cast_nonneg N), ← mul_pow]
    exact (sq_le_sq₀ (by positivity) (Nat.cast_nonneg _)).mpr hA
  have hsq' : 40000 * N ≤ A.card * A.card := by
    have h : (40000 : ℝ) * (N : ℝ) ≤ (A.card : ℝ) * (A.card : ℝ) := by
      norm_num [pow_two] at hsq ⊢
      exact hsq
    exact_mod_cast h
  by_contra! h
  exact not_zeroSumFree_of_card_sq N (ZMod N) (ZMod.card N) A hsq' h

end MathlibExt.Combinatorics.ZeroSubsetSumSqrtErdosProblem540Wanted
