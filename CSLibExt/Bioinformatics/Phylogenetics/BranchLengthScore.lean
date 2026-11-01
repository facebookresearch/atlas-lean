/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith

/-!
# The Branch Length Score of a conserved motif instance

Kheradpour, Stark, Roy and Kellis (2007) score the conservation of a motif instance in an
alignment of many genomes by its **Branch Length Score** (BLS): the total branch length of the
subtree of the species phylogeny connecting the species `S` in which the instance is present,
as a fraction of the total branch length of the tree.

A rooted binary tree with branch lengths is a `Tree L`; `node a l b r` has the edge of length `a`
to its left subtree `l` and the edge of length `b` to its right subtree `r`. An edge of a tree is
in the smallest subtree connecting the leaves `S` iff `S` has leaves on both sides of the edge
(below it, and in the rest of the tree). We take this characterization as the definition:
`bls S t` sums, over all edges of `t`, the edge length times the indicator that `S` meets both the
leaves below the edge and the other leaves (`blsWithin`). The two edges at the root then count
together, as the single edge of the unrooted tree.

## Main results

* `blsAlg_eq_bls`: the one-pass post-order algorithm `blsAlg` (each subtree returns its number of
  marked leaves and its partial score; an edge counts iff the number of marked leaves below it is
  strictly between `0` and the total) computes the BLS, for trees with distinct leaf labels.
* `bls_mono`: with nonnegative branch lengths the BLS is monotone in `S`.
* `bls_empty`, `bls_singleton`: the BLS of zero or one species is `0`.
* `bls_leaves`: the BLS of all species is the total branch length.
* `bls_union_le`: for overlapping `S`, `S'` (with `S` among the leaves),
  `bls (S ∪ S') ≤ bls S + bls S'`.
* `blsFrac_nonneg`, `blsFrac_le_one`: the normalized score lies in `[0, 1]`.

## Cost model

`blsGo` visits every node once and does a constant number of additions and comparisons per node,
so `blsAlg` runs in time linear in the size of the tree (plus the cost of the membership tests
`l ∈ S` at the leaves).

## References

* P. Kheradpour, A. Stark, S. Roy, M. Kellis, *Reliable prediction of regulator targets using
  12 Drosophila genomes*, Genome Res. 17 (2007), 1919–1931.
* C. Semple and M. Steel, *Phylogenetics*, Oxford University Press, 2003, chapter 3 (edges and
  splits of a tree).
-/

@[expose] public section

namespace Cslib.Bioinformatics.Phylogenetics.BranchLengthScore

/-- A rooted binary tree with leaf labels `L` and real branch lengths: `node a l b r` has the
edge of length `a` to `l` and the edge of length `b` to `r`. -/
inductive Tree (L : Type*) where
  /-- A leaf (a species). -/
  | leaf : L → Tree L
  /-- An internal node with branch lengths `a` and `b` to its subtrees `l` and `r`. -/
  | node : ℝ → Tree L → ℝ → Tree L → Tree L

variable {L : Type*} [DecidableEq L]

namespace Tree

/-- The set of leaf labels. -/
def leaves : Tree L → Finset L
  | leaf x => {x}
  | node _ l _ r => leaves l ∪ leaves r

/-- Distinct leaf labels: the two subtrees of every node have disjoint leaf sets. -/
def WellLabeled : Tree L → Prop
  | leaf _ => True
  | node _ l _ r => WellLabeled l ∧ WellLabeled r ∧ Disjoint (leaves l) (leaves r)

/-- Every branch length is nonnegative. -/
def NonnegLengths : Tree L → Prop
  | leaf _ => True
  | node a l b r => 0 ≤ a ∧ 0 ≤ b ∧ NonnegLengths l ∧ NonnegLengths r

/-- The total branch length. -/
def totalLength : Tree L → ℝ
  | leaf _ => 0
  | node a l b r => a + b + totalLength l + totalLength r

/-- Every tree has a leaf. -/
theorem leaves_nonempty : ∀ t : Tree L, t.leaves.Nonempty
  | leaf x => Finset.singleton_nonempty x
  | node _ l _ _ => (leaves_nonempty l).mono Finset.subset_union_left

end Tree

open _root_.Cslib.Bioinformatics.Phylogenetics.BranchLengthScore.Tree

/-- Whether the leaf set `S` meets both sides of an edge with leaf set `B` below it, inside a tree
with leaf set `U`: `S ∩ B` and `S ∩ (U \ B)` are nonempty. -/
def Separates (U S B : Finset L) : Prop := (S ∩ B).Nonempty ∧ (S ∩ (U \ B)).Nonempty

/-- `Separates` is decidable. -/
instance (U S B : Finset L) : Decidable (Separates U S B) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The total length of the edges of `t` whose two sides (inside a tree with leaf set `U`) both
meet `S`. -/
noncomputable def blsWithin (U S : Finset L) : Tree L → ℝ
  | leaf _ => 0
  | node a l b r =>
    (if Separates U S l.leaves then a else 0) + (if Separates U S r.leaves then b else 0) +
      blsWithin U S l + blsWithin U S r

/-- **The Branch Length Score** (unnormalized): the total branch length of the smallest subtree
of `t` connecting the leaves `S`. -/
noncomputable def bls (S : Finset L) (t : Tree L) : ℝ := blsWithin t.leaves S t

/-- The normalized Branch Length Score, `bls S t / totalLength t`, as reported by Kheradpour et
al. (a fraction of the total branch length). -/
noncomputable def blsFrac (S : Finset L) (t : Tree L) : ℝ := bls S t / t.totalLength

/-- One post-order pass with the total number `k` of marked leaves known: returns the number of
leaves of `S` in the subtree and the subtree's partial score. -/
noncomputable def blsGo (S : Finset L) (k : ℕ) : Tree L → ℕ × ℝ
  | leaf x => (if x ∈ S then 1 else 0, 0)
  | node a l b r =>
    let pl := blsGo S k l
    let pr := blsGo S k r
    (pl.1 + pr.1, (if 0 < pl.1 ∧ pl.1 < k then a else 0) +
      (if 0 < pr.1 ∧ pr.1 < k then b else 0) + pl.2 + pr.2)

/-- The number of leaves of `S` in `t`, by one pass. -/
def markedCount (S : Finset L) : Tree L → ℕ
  | leaf x => if x ∈ S then 1 else 0
  | node _ l _ r => markedCount S l + markedCount S r

/-- **The linear-time BLS algorithm**: count the marked leaves, then one post-order pass. -/
noncomputable def blsAlg (S : Finset L) (t : Tree L) : ℝ := (blsGo S (markedCount S t) t).2

/-- The first component of `blsGo` is the marked-leaf count. -/
theorem blsGo_fst (S : Finset L) (k : ℕ) : ∀ t : Tree L, (blsGo S k t).1 = markedCount S t
  | leaf _ => rfl
  | node _ l _ r => by simp [blsGo, markedCount, blsGo_fst S k l, blsGo_fst S k r]

/-- With distinct labels, `markedCount S t` is the number of leaves of `t` in `S`. -/
theorem markedCount_eq_card (S : Finset L) :
    ∀ t : Tree L, t.WellLabeled → markedCount S t = (S ∩ t.leaves).card
  | leaf x, _ => by
      by_cases hx : x ∈ S <;> simp [markedCount, leaves, hx, Finset.inter_singleton_of_mem,
        Finset.inter_singleton_of_notMem]
  | node _ l _ r, ⟨hl, hr, hd⟩ => by
      rw [markedCount, markedCount_eq_card S l hl, markedCount_eq_card S r hr, leaves,
        Finset.inter_union_distrib_left, Finset.card_union_of_disjoint
          (Finset.disjoint_of_subset_left Finset.inter_subset_right
            (Finset.disjoint_of_subset_right Finset.inter_subset_right hd))]

private theorem separates_iff_card {U S B : Finset L} (hB : B ⊆ U) :
    Separates U S B ↔ 0 < (S ∩ B).card ∧ (S ∩ B).card < (S ∩ U).card := by
  unfold Separates
  rw [Finset.card_pos]
  refine and_congr Iff.rfl ?_
  have hsub : S ∩ B ⊆ S ∩ U := Finset.inter_subset_inter_left hB
  have hdiff : S ∩ (U \ B) = (S ∩ U) \ (S ∩ B) := by
    ext x; simp only [Finset.mem_inter, Finset.mem_sdiff]; tauto
  rw [hdiff, Finset.sdiff_nonempty]
  constructor
  · intro h; exact lt_of_le_of_ne (Finset.card_le_card hsub) fun he =>
      h (Finset.eq_of_subset_of_card_le hsub he.ge).symm.subset
  · intro h hsub'; exact absurd (Finset.card_le_card hsub') (not_le.2 h)

private theorem blsGo_snd (S U : Finset L) :
    ∀ t : Tree L, t.WellLabeled → t.leaves ⊆ U →
      (blsGo S (S ∩ U).card t).2 = blsWithin U S t
  | leaf _, _, _ => rfl
  | node a l b r, ⟨hl, hr, hd⟩, hU => by
      have hlU : l.leaves ⊆ U := fun x hx => hU (Finset.mem_union_left _ hx)
      have hrU : r.leaves ⊆ U := fun x hx => hU (Finset.mem_union_right _ hx)
      simp only [blsGo, blsWithin, blsGo_fst, markedCount_eq_card S l hl,
        markedCount_eq_card S r hr, blsGo_snd S U l hl hlU, blsGo_snd S U r hr hrU,
        separates_iff_card hlU, separates_iff_card hrU]

/-- **The post-order algorithm computes the Branch Length Score** on trees with distinct leaf
labels. -/
theorem blsAlg_eq_bls (S : Finset L) {t : Tree L} (ht : t.WellLabeled) :
    blsAlg S t = bls S t := by
  rw [blsAlg, markedCount_eq_card S t ht, bls, blsGo_snd S t.leaves t ht subset_rfl]

private theorem separates_mono {U S S' B : Finset L} (h : S ⊆ S') :
    Separates U S B → Separates U S' B := fun ⟨h1, h2⟩ =>
  ⟨h1.mono (Finset.inter_subset_inter_right h), h2.mono (Finset.inter_subset_inter_right h)⟩

private theorem ite_le_ite {p q : Prop} [Decidable p] [Decidable q] {a : ℝ} (ha : 0 ≤ a)
    (h : p → q) : (if p then a else 0) ≤ if q then a else 0 := by
  by_cases hp : p
  · simp [hp, h hp]
  · simp only [hp, ite_false]; split_ifs <;> linarith

private theorem blsWithin_mono (U : Finset L) {S S' : Finset L} (h : S ⊆ S') :
    ∀ t : Tree L, t.NonnegLengths → blsWithin U S t ≤ blsWithin U S' t
  | leaf _, _ => le_rfl
  | node _ l _ r, ⟨ha, hb, hl, hr⟩ => by
      simp only [blsWithin]
      have := ite_le_ite ha (separates_mono (U := U) (B := l.leaves) h)
      have := ite_le_ite hb (separates_mono (U := U) (B := r.leaves) h)
      have := blsWithin_mono U h l hl
      have := blsWithin_mono U h r hr
      linarith

/-- **Monotonicity**: with nonnegative branch lengths, more conserving species never lower the
BLS. -/
theorem bls_mono {S S' : Finset L} (h : S ⊆ S') {t : Tree L} (ht : t.NonnegLengths) :
    bls S t ≤ bls S' t :=
  blsWithin_mono _ h t ht

private theorem blsWithin_of_not (U S : Finset L) (hS : ∀ B, ¬ Separates U S B) :
    ∀ t : Tree L, blsWithin U S t = 0
  | leaf _ => rfl
  | node _ l _ r => by
      simp [blsWithin, hS, blsWithin_of_not U S hS l, blsWithin_of_not U S hS r]

/-- The BLS of the empty set is `0`. -/
theorem bls_empty (t : Tree L) : bls ∅ t = 0 :=
  blsWithin_of_not _ _ (fun B h => by simp [Separates] at h) t

/-- **A single species has BLS `0`** (a motif present in one genome is not conserved). -/
theorem bls_singleton (x : L) (t : Tree L) : bls {x} t = 0 := by
  refine blsWithin_of_not _ _ (fun B ⟨⟨y, hy⟩, ⟨z, hz⟩⟩ => ?_) t
  simp only [Finset.mem_inter, Finset.mem_singleton, Finset.mem_sdiff] at hy hz
  exact hz.2.2 (hz.1 ▸ hy.1 ▸ hy.2)

private theorem blsWithin_leaves (U : Finset L) :
    ∀ t : Tree L, t.WellLabeled → t.leaves ⊆ U → (∀ B, B ⊆ t.leaves → B ≠ t.leaves →
      B.Nonempty → Separates U U B) → blsWithin U U t = t.totalLength
  | leaf _, _, _, _ => rfl
  | node a l b r, ⟨hl, hr, hd⟩, hU, hsep => by
      have hlU : l.leaves ⊆ (node a l b r).leaves := Finset.subset_union_left
      have hrU : r.leaves ⊆ (node a l b r).leaves := Finset.subset_union_right
      have hlne : l.leaves ≠ (node a l b r).leaves := fun he => by
        obtain ⟨y, hy⟩ := leaves_nonempty r
        exact Finset.disjoint_left.1 hd ((he ▸ hrU) hy) hy
      have hrne : r.leaves ≠ (node a l b r).leaves := fun he => by
        obtain ⟨y, hy⟩ := leaves_nonempty l
        exact Finset.disjoint_left.1 hd hy ((he ▸ hlU) hy)
      have hl' : ∀ B, B ⊆ l.leaves → B ≠ l.leaves → B.Nonempty → Separates U U B :=
        fun B hB _ hne => hsep B (hB.trans hlU) (fun he => hlne (Finset.Subset.antisymm
          (hlU) (he ▸ hB))) hne
      have hr' : ∀ B, B ⊆ r.leaves → B ≠ r.leaves → B.Nonempty → Separates U U B :=
        fun B hB _ hne => hsep B (hB.trans hrU) (fun he => hrne (Finset.Subset.antisymm
          (hrU) (he ▸ hB))) hne
      simp only [blsWithin, totalLength,
        hsep _ hlU hlne (leaves_nonempty l), hsep _ hrU hrne (leaves_nonempty r), ite_true,
        blsWithin_leaves U l hl (hlU.trans hU) hl', blsWithin_leaves U r hr (hrU.trans hU) hr']

/-- **All species give the whole tree**: with distinct leaf labels, the BLS of the set of all
leaves is the total branch length. -/
theorem bls_leaves {t : Tree L} (ht : t.WellLabeled) : bls t.leaves t = t.totalLength := by
  refine blsWithin_leaves t.leaves t ht subset_rfl fun B hB hne hBne => ⟨?_, ?_⟩
  · rwa [Finset.inter_eq_right.2 hB]
  · rw [Finset.inter_eq_right.2 Finset.sdiff_subset, Finset.sdiff_nonempty]
    exact fun h => hne (Finset.Subset.antisymm hB h)

private theorem separates_union {U S S' B : Finset L} (hSS : (S ∩ S').Nonempty)
    (h : Separates U (S ∪ S') B) (hS : S ⊆ U) :
    Separates U S B ∨ Separates U S' B := by
  obtain ⟨x, hx⟩ := hSS
  rw [Finset.mem_inter] at hx
  obtain ⟨⟨y, hy⟩, ⟨z, hz⟩⟩ := h
  simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff] at hy hz
  by_cases hxB : x ∈ B
  · rcases hz.1 with hzS | hzS
    · exact Or.inl ⟨⟨x, Finset.mem_inter.2 ⟨hx.1, hxB⟩⟩, ⟨z, by simp [hzS, hz.2]⟩⟩
    · exact Or.inr ⟨⟨x, Finset.mem_inter.2 ⟨hx.2, hxB⟩⟩, ⟨z, by simp [hzS, hz.2]⟩⟩
  · have hxU : x ∈ U \ B := Finset.mem_sdiff.2 ⟨hS hx.1, hxB⟩
    rcases hy.1 with hyS | hyS
    · exact Or.inl ⟨⟨y, by simp [hyS, hy.2]⟩, ⟨x, Finset.mem_inter.2 ⟨hx.1, hxU⟩⟩⟩
    · exact Or.inr ⟨⟨y, by simp [hyS, hy.2]⟩, ⟨x, Finset.mem_inter.2 ⟨hx.2, hxU⟩⟩⟩

private theorem ite_or_le {p q r : Prop} [Decidable p] [Decidable q] [Decidable r] {a : ℝ}
    (ha : 0 ≤ a) (h : p → q ∨ r) :
    (if p then a else 0) ≤ (if q then a else 0) + if r then a else 0 := by
  by_cases hp : p
  · rcases h hp with hq | hr
    · simp only [hp, hq, ite_true]; split_ifs <;> linarith
    · simp only [hp, hr, ite_true]; split_ifs <;> linarith
  · simp only [hp, ite_false]; split_ifs <;> linarith

private theorem blsWithin_union (U : Finset L) {S S' : Finset L} (hSS : (S ∩ S').Nonempty)
    (hS : S ⊆ U) :
    ∀ t : Tree L, t.NonnegLengths → blsWithin U (S ∪ S') t ≤ blsWithin U S t + blsWithin U S' t
  | leaf _, _ => by simp [blsWithin]
  | node _ l _ r, ⟨ha, hb, hl, hr⟩ => by
      simp only [blsWithin]
      have := ite_or_le ha fun h => separates_union (B := l.leaves) hSS h hS
      have := ite_or_le hb fun h => separates_union (B := r.leaves) hSS h hS
      have := blsWithin_union U hSS hS l hl
      have := blsWithin_union U hSS hS r hr
      linarith

/-- **Subadditivity**: for sets of species `S`, `S'` that share a species, with `S` among the
leaves of the tree, the subtree connecting `S ∪ S'` is at most as long as the two subtrees
together. -/
theorem bls_union_le {S S' : Finset L} {t : Tree L} (hSS : (S ∩ S').Nonempty)
    (hS : S ⊆ t.leaves) (ht : t.NonnegLengths) :
    bls (S ∪ S') t ≤ bls S t + bls S' t :=
  blsWithin_union _ hSS hS t ht

private theorem blsWithin_nonneg (U S : Finset L) :
    ∀ t : Tree L, t.NonnegLengths → 0 ≤ blsWithin U S t
  | leaf _, _ => le_rfl
  | node _ l _ r, ⟨ha, hb, hl, hr⟩ => by
      simp only [blsWithin]
      have := blsWithin_nonneg U S l hl
      have := blsWithin_nonneg U S r hr
      split_ifs <;> linarith

private theorem blsWithin_le_totalLength (U S : Finset L) :
    ∀ t : Tree L, t.NonnegLengths → blsWithin U S t ≤ t.totalLength
  | leaf _, _ => le_rfl
  | node _ l _ r, ⟨ha, hb, hl, hr⟩ => by
      simp only [blsWithin, totalLength]
      have := blsWithin_le_totalLength U S l hl
      have := blsWithin_le_totalLength U S r hr
      split_ifs <;> linarith

/-- The BLS is nonnegative for nonnegative branch lengths. -/
theorem bls_nonneg (S : Finset L) {t : Tree L} (ht : t.NonnegLengths) : 0 ≤ bls S t :=
  blsWithin_nonneg _ _ t ht

/-- The BLS is at most the total branch length. -/
theorem bls_le_totalLength (S : Finset L) {t : Tree L} (ht : t.NonnegLengths) :
    bls S t ≤ t.totalLength :=
  blsWithin_le_totalLength _ _ t ht

/-- The normalized BLS is nonnegative. -/
theorem blsFrac_nonneg (S : Finset L) {t : Tree L} (ht : t.NonnegLengths) :
    0 ≤ blsFrac S t :=
  div_nonneg (bls_nonneg S ht) ((bls_nonneg S ht).trans (bls_le_totalLength S ht))

/-- The normalized BLS is at most `1` when the tree has positive total length. -/
theorem blsFrac_le_one (S : Finset L) {t : Tree L} (ht : t.NonnegLengths)
    (hpos : 0 < t.totalLength) : blsFrac S t ≤ 1 :=
  (div_le_one hpos).2 (bls_le_totalLength S ht)

end Cslib.Bioinformatics.Phylogenetics.BranchLengthScore
