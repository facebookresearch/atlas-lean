/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Phylogenetics.TreeCount
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Counting unrooted binary phylogenetic trees

An *unrooted binary phylogenetic tree* on a set of taxa `X` is a finite tree whose leaves (the
vertices of degree one) are labeled bijectively by `X` and whose other vertices all have degree
three. Two such trees are the same when a graph isomorphism between them preserves the leaf
labels. For `n ≥ 3` taxa there are `(2 n - 5)‼` of them (`1, 3, 15, 105` for `n = 3, 4, 5, 6`).

We prove the count by rooting at the leaf of one taxon `a`. Seen from the leaf `a`, every vertex
`v` has a *cluster* (`cluster`): the taxa `x ≠ a` whose leaf lies beyond `v`, that is, `v` lies on
the path from the leaf `a` to the leaf `x` (in a tree, `dist a v + dist v x = dist a x`). The
clusters of a tree form a *binary hierarchy* on the remaining taxa (`IsBinaryHierarchy`: a family
of nonempty sets containing the whole set and every singleton, any two members nested or
disjoint, every member with two or more elements the disjoint union of two members), the
cluster set determines the tree up to label-preserving isomorphism, and every binary hierarchy
arises. Binary hierarchies on `S` are in bijection with the rooted binary phylogenetic trees on
`S` (the clusters of a planar drawing), which are counted in
`MathlibExt.Biology.Phylogenetics.TreeCount`. Hence the unrooted trees on `n` taxa are counted
by the rooted trees on `n - 1` taxa: `(2 (n - 1) - 3)‼ = (2 n - 5)‼`.

## Main results

* `nat_card_binaryHierarchy`: there are `(2 |S| - 3)‼` binary hierarchies on a nonempty `S`.
* `isBinaryHierarchy_clusterSet`, `clusterSet_eq_of_iso`, `iso_of_clusterSet_eq`,
  `exists_clusterSet_eq`: the cluster set seen from a leaf is a complete invariant of unrooted
  binary phylogenetic trees up to isomorphism, with exactly the binary hierarchies as values.
* `nat_card_unrootedBinaryTree`: there are `(2 n - 5)‼` unrooted binary phylogenetic trees on
  `n ≥ 3` labeled taxa.

## References

* C. Semple and M. Steel, *Phylogenetics*, Oxford University Press, 2003, Proposition 2.1.4
  (the count) and Section 3.1 (clusters and hierarchies).
* J. Felsenstein, *Inferring Phylogenies*, Sinauer, 2004, chapter 3.
-/

@[expose] public section

open scoped Nat

namespace MathlibExt.Biology.Phylogenetics.UnrootedTreeCount

open MathlibExt.Biology.Phylogenetics.TreeCount

universe u

/-- An **unrooted binary phylogenetic tree** on the taxa `X`: a finite tree `G` on a vertex
type `V` whose degree-one vertices are labeled bijectively by `X` (`label`) and whose other
vertices all have degree three. -/
structure UnrootedBinaryTree (X : Type) : Type 1 where
  /-- The vertex type. -/
  V : Type
  /-- The vertex type is finite. -/
  [fintype : Fintype V]
  /-- The tree. -/
  G : SimpleGraph V
  /-- Adjacency is decidable (so that degrees are defined). -/
  [decRel : DecidableRel G.Adj]
  /-- `G` is a tree. -/
  isTree : G.IsTree
  /-- The bijective labeling of the leaves by the taxa. -/
  label : X ≃ {v : V // G.degree v = 1}
  /-- Every vertex that is not a leaf has degree three. -/
  degree_eq_three : ∀ v, G.degree v ≠ 1 → G.degree v = 3

attribute [instance] UnrootedBinaryTree.fintype UnrootedBinaryTree.decRel

/-- Two unrooted binary phylogenetic trees are **isomorphic** when some graph isomorphism maps
the leaf with each label to the leaf with the same label. -/
def UnrootedBinaryTree.Iso {X : Type} (T T' : UnrootedBinaryTree X) : Prop :=
  ∃ e : T.G ≃g T'.G, ∀ x, e (T.label x) = T'.label x

/-! ### Binary hierarchies -/

/-- A **binary hierarchy** on a finite set `S`: a family of nonempty subsets of `S` containing
`S` and every singleton, any two members nested or disjoint, and every member with at least two
elements the disjoint union of two members. These are the cluster systems of the rooted binary
phylogenetic trees on `S` (Semple & Steel 2003, Section 3.1). -/
def IsBinaryHierarchy {α : Type*} [DecidableEq α] (S : Finset α) (H : Finset (Finset α)) :
    Prop :=
  S ∈ H ∧ (∀ C ∈ H, C.Nonempty ∧ C ⊆ S) ∧ (∀ x ∈ S, {x} ∈ H) ∧
    (∀ C ∈ H, ∀ D ∈ H, C ⊆ D ∨ D ⊆ C ∨ Disjoint C D) ∧
    ∀ C ∈ H, 1 < C.card → ∃ D₁ ∈ H, ∃ D₂ ∈ H, Disjoint D₁ D₂ ∧ D₁ ∪ D₂ = C

/-- The leaf set of a planar tree, as a finset. -/
private def leafSet {α : Type u} [DecidableEq α] (t : PlaneTree α) : Finset α :=
  t.leaves.toFinset

/-- The clusters of a planar tree (the leaf sets of its subtrees), as a finset. -/
private def clusterFinset {α : Type u} [DecidableEq α] : PlaneTree α → Finset (Finset α)
  | .leaf a => {{a}}
  | .node l r => insert (leafSet l ∪ leafSet r) (clusterFinset l ∪ clusterFinset r)

private theorem leafSet_node {α : Type u} [DecidableEq α] (l r : PlaneTree α) :
    leafSet (.node l r) = leafSet l ∪ leafSet r := by
  simp [leafSet, PlaneTree.leaves, Multiset.toFinset_add]

private theorem leafSet_nonempty {α : Type u} [DecidableEq α] (t : PlaneTree α) :
    (leafSet t).Nonempty := by
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero t.leaves_ne_zero
  exact ⟨a, Multiset.mem_toFinset.mpr ha⟩

private theorem swap_clusterFinset {α : Type u} [DecidableEq α] {s t : PlaneTree α}
    (h : PlaneTree.Swap s t) : clusterFinset s = clusterFinset t ∧ leafSet s = leafSet t := by
  induction h with
  | root l r =>
    simp only [clusterFinset, leafSet_node]
    exact ⟨by rw [Finset.union_comm (leafSet l), Finset.union_comm (clusterFinset l)],
      Finset.union_comm _ _⟩
  | left r h ih => simp [clusterFinset, leafSet_node, ih.1, ih.2]
  | right l h ih => simp [clusterFinset, leafSet_node, ih.1, ih.2]

private theorem equiv_clusterFinset {α : Type u} [DecidableEq α] {s t : PlaneTree α}
    (h : Relation.EqvGen PlaneTree.Swap s t) : clusterFinset s = clusterFinset t := by
  induction h with
  | rel s t h => exact (swap_clusterFinset h).1
  | refl => rfl
  | symm s t h ih => exact ih.symm
  | trans s t v h h' ih ih' => exact ih.trans ih'

/-- Swap-equivalent children give swap-equivalent trees. -/
private theorem equiv_node {α : Type u} {l l' r r' : PlaneTree α}
    (hl : Relation.EqvGen PlaneTree.Swap l l') (hr : Relation.EqvGen PlaneTree.Swap r r') :
    Relation.EqvGen PlaneTree.Swap (.node l r) (.node l' r') := by
  have left : Relation.EqvGen PlaneTree.Swap (.node l r) (.node l' r) := by
    induction hl with
    | rel s t h => exact .rel _ _ (.left r h)
    | refl => exact .refl _
    | symm s t h ih => exact .symm _ _ ih
    | trans s t v h h' ih ih' => exact .trans _ _ _ ih ih'
  have right : Relation.EqvGen PlaneTree.Swap (.node l' r) (.node l' r') := by
    clear left
    induction hr with
    | rel s t h => exact .rel _ _ (.right l' h)
    | refl => exact .refl _
    | symm s t h ih => exact .symm _ _ ih
    | trans s t v h h' ih ih' => exact .trans _ _ _ ih ih'
  exact .trans _ _ _ left right

private theorem mem_clusterFinset_sub {α : Type u} [DecidableEq α] (t : PlaneTree α) :
    ∀ C ∈ clusterFinset t, C.Nonempty ∧ C ⊆ leafSet t := by
  induction t with
  | leaf a => simp [clusterFinset, leafSet, PlaneTree.leaves]
  | node l r hl hr =>
    intro C hC
    simp only [clusterFinset, Finset.mem_insert, Finset.mem_union] at hC
    rw [leafSet_node]
    rcases hC with rfl | hC | hC
    · exact ⟨(leafSet_nonempty l).mono Finset.subset_union_left, le_rfl⟩
    · exact ⟨(hl C hC).1, (hl C hC).2.trans Finset.subset_union_left⟩
    · exact ⟨(hr C hC).1, (hr C hC).2.trans Finset.subset_union_right⟩

private theorem leafSet_mem {α : Type u} [DecidableEq α] (t : PlaneTree α) :
    leafSet t ∈ clusterFinset t := by
  cases t with
  | leaf a => simp [clusterFinset, leafSet, PlaneTree.leaves]
  | node l r => simp [clusterFinset, leafSet_node]

private theorem nodup_disjoint {α : Type u} [DecidableEq α] {l r : PlaneTree α}
    (h : (PlaneTree.node l r).leaves.Nodup) :
    l.leaves.Nodup ∧ r.leaves.Nodup ∧ Disjoint (leafSet l) (leafSet r) := by
  obtain ⟨h1, h2, h3⟩ := Multiset.nodup_add.mp h
  refine ⟨h1, h2, Finset.disjoint_left.mpr fun x hx hx' => ?_⟩
  exact Multiset.disjoint_left.mp h3 (Multiset.mem_toFinset.mp hx)
    (Multiset.mem_toFinset.mp hx')

private theorem isBinaryHierarchy_clusterFinset {α : Type u} [DecidableEq α]
    (t : PlaneTree α) (hn : t.leaves.Nodup) :
    IsBinaryHierarchy (leafSet t) (clusterFinset t) := by
  induction t with
  | leaf a =>
    refine ⟨by simp [clusterFinset, leafSet, PlaneTree.leaves], mem_clusterFinset_sub _, ?_,
      ?_, ?_⟩
    · intro x hx; simp_all [clusterFinset, leafSet, PlaneTree.leaves]
    · intro C hC D hD; simp_all [clusterFinset]
    · intro C hC h1; simp_all [clusterFinset]
  | node l r hl hr =>
    obtain ⟨hnl, hnr, hd⟩ := nodup_disjoint hn
    obtain ⟨-, hsl, hxl, hlaml, hspl⟩ := hl hnl
    obtain ⟨-, hsr, hxr, hlamr, hspr⟩ := hr hnr
    have hmem : ∀ C ∈ clusterFinset (.node l r), C = leafSet l ∪ leafSet r ∨
        C ∈ clusterFinset l ∨ C ∈ clusterFinset r := by
      intro C hC; simpa [clusterFinset] using hC
    refine ⟨leafSet_mem _, mem_clusterFinset_sub _, ?_, ?_, ?_⟩
    · intro x hx
      rw [leafSet_node, Finset.mem_union] at hx
      rcases hx with hx | hx
      · simp [clusterFinset, hxl x hx]
      · simp [clusterFinset, hxr x hx]
    · intro C hC D hD
      have hsub := (mem_clusterFinset_sub _ C hC).2
      have hsubD := (mem_clusterFinset_sub _ D hD).2
      rw [leafSet_node] at hsub hsubD
      rcases hmem C hC with rfl | hC | hC
      · exact Or.inr (Or.inl hsubD)
      · rcases hmem D hD with rfl | hD | hD
        · exact Or.inl hsub
        · exact hlaml C hC D hD
        · exact Or.inr (Or.inr (hd.mono (hsl C hC).2 (hsr D hD).2))
      · rcases hmem D hD with rfl | hD | hD
        · exact Or.inl hsub
        · exact Or.inr (Or.inr (hd.symm.mono (hsr C hC).2 (hsl D hD).2))
        · exact hlamr C hC D hD
    · intro C hC hc
      rcases hmem C hC with rfl | hC | hC
      · exact ⟨leafSet l, by simp [clusterFinset, leafSet_mem], leafSet r,
          by simp [clusterFinset, leafSet_mem], hd, rfl⟩
      · obtain ⟨D₁, h₁, D₂, h₂, hd', hu⟩ := hspl C hC hc
        exact ⟨D₁, by simp [clusterFinset, h₁], D₂, by simp [clusterFinset, h₂], hd', hu⟩
      · obtain ⟨D₁, h₁, D₂, h₂, hd', hu⟩ := hspr C hC hc
        exact ⟨D₁, by simp [clusterFinset, h₁], D₂, by simp [clusterFinset, h₂], hd', hu⟩

/-- The members of the cluster set of `node l r` inside the leaf set of `l` are the clusters
of `l`. -/
private theorem filter_clusterFinset_left {α : Type u} [DecidableEq α] (l r : PlaneTree α)
    (hn : (PlaneTree.node l r).leaves.Nodup) :
    (clusterFinset (.node l r)).filter (· ⊆ leafSet l) = clusterFinset l := by
  obtain ⟨-, -, hd⟩ := nodup_disjoint hn
  ext C
  simp only [clusterFinset, Finset.mem_filter, Finset.mem_insert, Finset.mem_union]
  constructor
  · rintro ⟨rfl | hC | hC, hsub⟩
    · obtain ⟨x, hx⟩ := leafSet_nonempty r
      exact absurd (hsub (Finset.mem_union_right _ hx)) (Finset.disjoint_right.mp hd hx)
    · exact hC
    · obtain ⟨hne, hsr⟩ := mem_clusterFinset_sub r C hC
      obtain ⟨x, hx⟩ := hne
      exact absurd (hsub hx) (Finset.disjoint_right.mp hd (hsr hx))
  · intro hC
    exact ⟨Or.inr (Or.inl hC), (mem_clusterFinset_sub l C hC).2⟩

private theorem filter_clusterFinset_right {α : Type u} [DecidableEq α] (l r : PlaneTree α)
    (hn : (PlaneTree.node l r).leaves.Nodup) :
    (clusterFinset (.node l r)).filter (· ⊆ leafSet r) = clusterFinset r := by
  have hn' : (PlaneTree.node r l).leaves.Nodup := by
    simpa [PlaneTree.leaves, add_comm] using hn
  have := filter_clusterFinset_left r l hn'
  rwa [(swap_clusterFinset (.root r l)).1] at this

private theorem leafSet_eq_of_clusterFinset_eq {α : Type u} [DecidableEq α]
    {s t : PlaneTree α} (h : clusterFinset s = clusterFinset t) : leafSet s = leafSet t := by
  apply le_antisymm
  · exact (mem_clusterFinset_sub t _ (h ▸ leafSet_mem s)).2
  · exact (mem_clusterFinset_sub s _ (h.symm ▸ leafSet_mem t)).2

private theorem eq_leaf_of_leafSet {α : Type u} [DecidableEq α] (t : PlaneTree α) (a : α)
    (hn : t.leaves.Nodup) (h : leafSet t = {a}) : t = .leaf a := by
  cases t with
  | leaf b => simpa [leafSet, PlaneTree.leaves] using h
  | node l r =>
    obtain ⟨-, -, hd⟩ := nodup_disjoint hn
    rw [leafSet_node] at h
    obtain ⟨x, hx⟩ := leafSet_nonempty l
    obtain ⟨y, hy⟩ := leafSet_nonempty r
    have hx' : x = a := by simpa [h] using Finset.mem_union_left (leafSet r) hx
    have hy' : y = a := by simpa [h] using Finset.mem_union_right (leafSet l) hy
    subst hx' hy'
    exact absurd hy (Finset.disjoint_left.mp hd hx)

private theorem not_leafSet_singleton_node {α : Type u} [DecidableEq α] (l r : PlaneTree α)
    (hn : (PlaneTree.node l r).leaves.Nodup) (a : α) :
    leafSet (.node l r) ≠ {a} := fun h => by
  cases eq_leaf_of_leafSet _ a hn h

/-- Equal cluster sets give swap-equivalent drawings. -/
private theorem equiv_of_clusterFinset_eq {α : Type u} [DecidableEq α] (s : PlaneTree α) :
    ∀ t : PlaneTree α, s.leaves.Nodup → t.leaves.Nodup →
      clusterFinset s = clusterFinset t → Relation.EqvGen PlaneTree.Swap s t := by
  induction s with
  | leaf a =>
    intro t _ hnt h
    have hl := leafSet_eq_of_clusterFinset_eq h
    rw [eq_leaf_of_leafSet t a hnt (by simpa [leafSet, PlaneTree.leaves] using hl.symm)]
    exact .refl _
  | node l r ihl ihr =>
    intro t hns hnt h
    cases t with
    | leaf b =>
      exact absurd (leafSet_eq_of_clusterFinset_eq h)
        (by simpa [leafSet, PlaneTree.leaves] using not_leafSet_singleton_node l r hns b)
    | node l' r' =>
      obtain ⟨hnl, hnr, hd⟩ := nodup_disjoint hns
      obtain ⟨hnl', hnr', hd'⟩ := nodup_disjoint hnt
      have hroot := leafSet_eq_of_clusterFinset_eq h
      rw [leafSet_node, leafSet_node] at hroot
      -- each child leaf set of `s` is a child leaf set of `t`
      have key : ∀ (l r l' r' : PlaneTree α), (PlaneTree.node l r).leaves.Nodup →
          (PlaneTree.node l' r').leaves.Nodup →
          clusterFinset (.node l r) = clusterFinset (.node l' r') →
          leafSet l = leafSet l' ∨ leafSet l = leafSet r' := by
        intro l r l' r' hns hnt h
        obtain ⟨-, -, hd⟩ := nodup_disjoint hns
        obtain ⟨-, -, hd'⟩ := nodup_disjoint hnt
        have hroot := leafSet_eq_of_clusterFinset_eq h
        rw [leafSet_node, leafSet_node] at hroot
        have hlm : leafSet l ∈ clusterFinset (.node l' r') := by
          rw [← h]; simp [clusterFinset, leafSet_mem]
        have hne : leafSet l ≠ leafSet l ∪ leafSet r := by
          intro he
          obtain ⟨y, hy⟩ := leafSet_nonempty r
          have : y ∈ leafSet l := he ▸ Finset.mem_union_right _ hy
          exact Finset.disjoint_left.mp hd this hy
        -- every cluster of `s` other than its leaf set lies below `l` or `r`
        have hback : ∀ C ∈ clusterFinset (.node l r), C ≠ leafSet l ∪ leafSet r →
            C ⊆ leafSet l ∨ C ⊆ leafSet r := by
          intro C hC hCne
          simp only [clusterFinset, Finset.mem_insert, Finset.mem_union] at hC
          rcases hC with hC | hC | hC
          · exact absurd hC hCne
          · exact Or.inl (mem_clusterFinset_sub l C hC).2
          · exact Or.inr (mem_clusterFinset_sub r C hC).2
        have hl'm : leafSet l' ∈ clusterFinset (.node l r) := by
          rw [h]; simp [clusterFinset, leafSet_mem]
        have hr'm : leafSet r' ∈ clusterFinset (.node l r) := by
          rw [h]; simp [clusterFinset, leafSet_mem]
        have hne' : ∀ (p q : PlaneTree α), Disjoint (leafSet p) (leafSet q) →
            leafSet p ≠ leafSet p ∪ leafSet q := by
          intro p q hpq he
          obtain ⟨y, hy⟩ := leafSet_nonempty q
          exact Finset.disjoint_left.mp hpq (he ▸ Finset.mem_union_right _ hy) hy
        have hne'' : ∀ (p q : PlaneTree α), Disjoint (leafSet p) (leafSet q) →
            leafSet q ≠ leafSet p ∪ leafSet q := by
          intro p q hpq he
          obtain ⟨y, hy⟩ := leafSet_nonempty p
          exact Finset.disjoint_left.mp hpq hy (he ▸ Finset.mem_union_left _ hy)
        simp only [clusterFinset, Finset.mem_insert, Finset.mem_union] at hlm
        rcases hlm with hlm | hlm | hlm
        · exact absurd (hlm.trans hroot.symm) hne
        · have h1 := (mem_clusterFinset_sub l' _ hlm).2
          rcases hback _ hl'm (hroot ▸ hne' l' r' hd') with h2 | h2
          · exact Or.inl (le_antisymm h1 h2)
          · obtain ⟨x, hx⟩ := leafSet_nonempty l
            exact absurd (h2 (h1 hx)) (Finset.disjoint_left.mp hd hx)
        · have h1 := (mem_clusterFinset_sub r' _ hlm).2
          rcases hback _ hr'm (hroot ▸ hne'' l' r' hd') with h2 | h2
          · exact Or.inr (le_antisymm h1 h2)
          · obtain ⟨x, hx⟩ := leafSet_nonempty l
            exact absurd (h2 (h1 hx)) (Finset.disjoint_left.mp hd hx)
      have hcompl : ∀ {A B A' B' : Finset α}, Disjoint A B → Disjoint A' B' →
          A ∪ B = A' ∪ B' → A = A' → B = B' := by
        intro A B A' B' h1 h2 h3 h4
        subst h4
        rw [← Finset.union_sdiff_cancel_left h1, h3, Finset.union_sdiff_cancel_left h2]
      rcases key l r l' r' hns hnt h with he | he
      · have he' : leafSet r = leafSet r' := hcompl hd hd' hroot he
        have hcl : clusterFinset l = clusterFinset l' := by
          rw [← filter_clusterFinset_left l r hns, ← filter_clusterFinset_left l' r' hnt, h, he]
        have hcr : clusterFinset r = clusterFinset r' := by
          rw [← filter_clusterFinset_right l r hns, ← filter_clusterFinset_right l' r' hnt, h,
            he']
        exact equiv_node (ihl l' hnl hnl' hcl) (ihr r' hnr hnr' hcr)
      · have he' : leafSet r = leafSet l' :=
          hcompl hd hd'.symm (hroot.trans (Finset.union_comm _ _)) he
        have hcl : clusterFinset l = clusterFinset r' := by
          rw [← filter_clusterFinset_left l r hns, ← filter_clusterFinset_right l' r' hnt, h,
            he]
        have hcr : clusterFinset r = clusterFinset l' := by
          rw [← filter_clusterFinset_right l r hns, ← filter_clusterFinset_left l' r' hnt, h,
            he']
        exact .trans _ _ _ (equiv_node (ihl r' hnl hnr' hcl) (ihr l' hnr hnl' hcr))
          (.rel _ _ (.root _ _))

/-- The members of a binary hierarchy below a member form a binary hierarchy. -/
private theorem isBinaryHierarchy_filter {α : Type u} [DecidableEq α] {S D : Finset α}
    {H : Finset (Finset α)} (hH : IsBinaryHierarchy S H) (hD : D ∈ H) :
    IsBinaryHierarchy D (H.filter (· ⊆ D)) := by
  obtain ⟨-, hsub, hsing, hlam, hsplit⟩ := hH
  refine ⟨Finset.mem_filter.mpr ⟨hD, le_rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro C hC
    rw [Finset.mem_filter] at hC
    exact ⟨(hsub C hC.1).1, hC.2⟩
  · intro x hx
    exact Finset.mem_filter.mpr ⟨hsing x ((hsub D hD).2 hx), Finset.singleton_subset_iff.mpr hx⟩
  · intro C hC E hE
    exact hlam C (Finset.mem_filter.mp hC).1 E (Finset.mem_filter.mp hE).1
  · intro C hC hc
    rw [Finset.mem_filter] at hC
    obtain ⟨D₁, h₁, D₂, h₂, hd, hu⟩ := hsplit C hC.1 hc
    refine ⟨D₁, Finset.mem_filter.mpr ⟨h₁, ?_⟩, D₂, Finset.mem_filter.mpr ⟨h₂, ?_⟩, hd, hu⟩
    · exact (hu ▸ Finset.subset_union_left).trans hC.2
    · exact (hu ▸ Finset.subset_union_right).trans hC.2

/-- Every binary hierarchy is the cluster set of a drawing. -/
private theorem exists_drawing {α : Type u} [DecidableEq α] (n : ℕ) :
    ∀ (S : Finset α) (H : Finset (Finset α)), S.card = n → IsBinaryHierarchy S H →
      ∃ t : PlaneTree α, t.leaves = S.val ∧ clusterFinset t = H := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S H hn hH
  obtain ⟨hS, hsub, hsing, hlam, hsplit⟩ := hH
  have hSne := (hsub S hS).1
  by_cases h1 : 1 < S.card
  · obtain ⟨D₁, h₁, D₂, h₂, hd, hu⟩ := hsplit S hS h1
    have hne₁ := (hsub D₁ h₁).1
    have hne₂ := (hsub D₂ h₂).1
    have hc₁ : D₁.card < n := by
      rw [← hn, ← hu, Finset.card_union_of_disjoint hd]
      have := hne₂.card_pos; omega
    have hc₂ : D₂.card < n := by
      rw [← hn, ← hu, Finset.card_union_of_disjoint hd]
      have := hne₁.card_pos; omega
    have hH : IsBinaryHierarchy S H := ⟨hS, hsub, hsing, hlam, hsplit⟩
    obtain ⟨t₁, ht₁, hc₁'⟩ := ih _ hc₁ D₁ _ rfl (isBinaryHierarchy_filter hH h₁)
    obtain ⟨t₂, ht₂, hc₂'⟩ := ih _ hc₂ D₂ _ rfl (isBinaryHierarchy_filter hH h₂)
    have hl₁ : leafSet t₁ = D₁ := by simp [leafSet, ht₁]
    have hl₂ : leafSet t₂ = D₂ := by simp [leafSet, ht₂]
    have hleft : ∀ {C A B : Finset α}, C ⊆ A ∪ B → Disjoint C B → C ⊆ A := fun hC hd y hy =>
      (Finset.mem_union.mp (hC hy)).resolve_right (Finset.disjoint_left.mp hd hy)
    refine ⟨.node t₁ t₂, ?_, ?_⟩
    · simp only [PlaneTree.leaves, ht₁, ht₂]
      rw [← hu, ← Finset.disjUnion_eq_union D₁ D₂ hd]
      rfl
    · simp only [clusterFinset, hl₁, hl₂, hc₁', hc₂', hu]
      ext C
      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (rfl | h | h)
        · exact hS
        · exact h.1
        · exact h.1
      · intro hC
        have hCS : C ⊆ D₁ ∪ D₂ := hu ▸ (hsub C hC).2
        obtain ⟨x, hx⟩ := (hsub C hC).1
        rcases hlam C hC D₁ h₁ with hc | hc | hc
        · exact Or.inr (Or.inl ⟨hC, hc⟩)
        · rcases hlam C hC D₂ h₂ with hc' | hc' | hc'
          · obtain ⟨y, hy⟩ := hne₁
            exact absurd (hc' (hc hy)) (Finset.disjoint_left.mp hd hy)
          · exact Or.inl (le_antisymm (hu ▸ hCS) (hu ▸ Finset.union_subset hc hc'))
          · exact Or.inr (Or.inl ⟨hC, hleft hCS hc'⟩)
        · rcases hlam C hC D₂ h₂ with hc' | hc' | hc'
          · exact Or.inr (Or.inr ⟨hC, hc'⟩)
          · exact Or.inr (Or.inr ⟨hC, hleft (Finset.union_comm D₁ D₂ ▸ hCS) hc⟩)
          · rcases Finset.mem_union.mp (hCS hx) with hx' | hx'
            · exact absurd hx' (Finset.disjoint_left.mp hc hx)
            · exact absurd hx' (Finset.disjoint_left.mp hc' hx)
  · obtain ⟨a, rfl⟩ : ∃ a, S = {a} := by
      rw [← Finset.card_eq_one]
      have := hSne.card_pos; omega
    refine ⟨.leaf a, rfl, ?_⟩
    ext C
    simp only [clusterFinset, Finset.mem_singleton]
    constructor
    · rintro rfl; exact hS
    · intro hC
      obtain ⟨hne, hCa⟩ := hsub C hC
      exact (Finset.Nonempty.subset_singleton_iff hne).mp hCa

/-- Rooted binary phylogenetic trees on `S` correspond to binary hierarchies on `S`. -/
private noncomputable def rootedEquivHierarchy {α : Type u} [DecidableEq α] (S : Finset α) :
    RootedBinaryTree S ≃ {H : Finset (Finset α) // IsBinaryHierarchy S H} := by
  have hS : ∀ t : PlaneTree.On S, leafSet t.1 = S := fun t => by simp [leafSet, t.2]
  have hn : ∀ t : PlaneTree.On S, t.1.leaves.Nodup := fun t => by rw [t.2]; exact S.nodup
  refine Equiv.ofBijective (Quotient.lift (fun t : PlaneTree.On S => ⟨clusterFinset t.1,
      by simpa only [hS t] using isBinaryHierarchy_clusterFinset t.1 (hn t)⟩)
    fun s t h => Subtype.ext (equiv_clusterFinset h)) ⟨?_, ?_⟩
  · intro p q hpq
    induction p using Quotient.ind with
    | _ s =>
    induction q using Quotient.ind with
    | _ t =>
    exact Quotient.sound (equiv_of_clusterFinset_eq s.1 t.1 (hn s) (hn t)
      (congrArg Subtype.val hpq))
  · rintro ⟨H, hH⟩
    obtain ⟨t, ht, hc⟩ := exists_drawing _ S H rfl hH
    exact ⟨⟦⟨t, ht⟩⟧, Subtype.ext hc⟩

/-- **The number of binary hierarchies.** On a nonempty finite set `S` there are
`(2 |S| - 3)‼` binary hierarchies, as many as rooted binary phylogenetic trees on `S`: a tree
corresponds to the leaf sets of its subtrees. -/
theorem nat_card_binaryHierarchy {α : Type u} [DecidableEq α] (S : Finset α)
    (hS : S.Nonempty) :
    Nat.card {H : Finset (Finset α) // IsBinaryHierarchy S H} = (2 * S.card - 3)‼ := by
  rw [← Nat.card_congr (rootedEquivHierarchy S), nat_card_rootedBinaryTree S hS]

/-! ### Distances in a tree seen from a root -/

/-- `w` lies **beyond** `v` seen from `s`: `v` is on a shortest walk from `s` to `w`. In a tree
this says that `v` lies on the path from `s` to `w`. -/
private def Beyond {V : Type} (G : SimpleGraph V) (s v w : V) : Prop :=
  G.dist s v + G.dist v w = G.dist s w

private theorem beyond_self {V : Type} (G : SimpleGraph V) (s v : V) : Beyond G s v v := by
  simp [Beyond]

private theorem beyond_trans {V : Type} {G : SimpleGraph V} (hG : G.Connected) {s u v w : V}
    (h₁ : Beyond G s u v) (h₂ : Beyond G s v w) : Beyond G s u w := by
  unfold Beyond at *
  have := hG.dist_triangle (u := u) (v := v) (w := w)
  have := hG.dist_triangle (u := s) (v := u) (w := w)
  omega

private theorem exists_parent {V : Type} {G : SimpleGraph V} (hG : G.Connected) {s v : V}
    (hv : v ≠ s) : ∃ p, G.Adj v p ∧ G.dist s p + 1 = G.dist s v := by
  obtain ⟨q, hq⟩ := hG.exists_walk_length_eq_dist v s
  cases q with
  | nil => exact absurd rfl hv
  | @cons _ c _ h q' =>
    refine ⟨c, h, ?_⟩
    have h1 := SimpleGraph.dist_le q'
    have h2 := (SimpleGraph.dist_eq_one_iff_adj.mpr h)
    have h3 := hG.dist_triangle (u := v) (v := c) (w := s)
    simp only [SimpleGraph.Walk.length_cons] at hq
    rw [SimpleGraph.dist_comm (u := s), SimpleGraph.dist_comm (u := s)]
    omega

private theorem parent_unique {V : Type} {G : SimpleGraph V} (hG : G.IsTree) {s v p₁ p₂ : V}
    (h₁ : G.Adj v p₁) (h₂ : G.Adj v p₂) (hd₁ : G.dist s p₁ + 1 = G.dist s v)
    (hd₂ : G.dist s p₂ + 1 = G.dist s v) : p₁ = p₂ := by
  classical
  obtain ⟨q, hq, hql⟩ := hG.connected.exists_path_of_dist s v
  have key : ∀ p, G.Adj v p → G.dist s p + 1 = G.dist s v → p = q.penultimate := by
    intro p hp hd
    obtain ⟨r, hr, hrl⟩ := hG.connected.exists_path_of_dist s p
    have hv : v ∉ r.support := by
      intro hm
      have := SimpleGraph.dist_le (r.takeUntil v hm)
      have := r.length_takeUntil_le_length hm
      omega
    exact hG.isAcyclic.eq_penultimate_of_adj_end hq hp
      (hG.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath hq hr hp hv)
  rw [key _ h₁ hd₁, key _ h₂ hd₂]

private theorem exists_child_toward {V : Type} {G : SimpleGraph V} (hG : G.Connected)
    {s v w : V} (h : Beyond G s v w) (hne : v ≠ w) :
    ∃ c, G.Adj v c ∧ G.dist s c = G.dist s v + 1 ∧ Beyond G s c w := by
  obtain ⟨q, hq⟩ := hG.exists_walk_length_eq_dist v w
  cases q with
  | nil => exact absurd rfl hne
  | @cons _ c _ hc q' =>
    refine ⟨c, hc, ?_⟩
    unfold Beyond at *
    have h1 := SimpleGraph.dist_le q'
    have h2 := SimpleGraph.dist_eq_one_iff_adj.mpr hc
    have h3 := hG.dist_triangle (u := s) (v := v) (w := c)
    have h4 := hG.dist_triangle (u := s) (v := c) (w := w)
    simp only [SimpleGraph.Walk.length_cons] at hq
    omega

private theorem beyond_of_child {V : Type} {G : SimpleGraph V} (hG : G.Connected)
    {s v c w : V} (hc : G.Adj v c) (hd : G.dist s c = G.dist s v + 1) (h : Beyond G s c w) :
    Beyond G s v w := by
  unfold Beyond at *
  have h2 := SimpleGraph.dist_eq_one_iff_adj.mpr hc
  have h3 := hG.dist_triangle (u := v) (v := c) (w := w)
  have h4 := hG.dist_triangle (u := s) (v := v) (w := w)
  omega

private theorem ancestor_unique {V : Type} {G : SimpleGraph V} (hG : G.IsTree) {s w : V} :
    ∀ n x y, G.dist x w = n → Beyond G s x w → Beyond G s y w →
      G.dist s x = G.dist s y → x = y := by
  intro n
  induction n with
  | zero =>
    intro x y hn hx hy hd
    have hxw : x = w := (hG.connected.dist_eq_zero_iff).mp hn
    subst hxw
    unfold Beyond at hy
    have : G.dist y x = 0 := by omega
    exact ((hG.connected.dist_eq_zero_iff).mp this).symm
  | succ n ih =>
    intro x y hn hx hy hd
    have hxw : x ≠ w := fun h => by subst h; simp at hn
    have hyw : y ≠ w := by
      intro h; subst h
      unfold Beyond at hx
      omega
    obtain ⟨cx, hax, hdx, hbx⟩ := exists_child_toward hG.connected hx hxw
    obtain ⟨cy, hay, hdy, hby⟩ := exists_child_toward hG.connected hy hyw
    have hcxn : G.dist cx w = n := by unfold Beyond at hx hbx; omega
    have hc : cx = cy := ih cx cy hcxn hbx hby (by omega)
    subst hc
    exact parent_unique (s := s) hG hax.symm hay.symm (by omega) (by omega)

private theorem exists_ancestor {V : Type} {G : SimpleGraph V} (hG : G.Connected) (s : V) :
    ∀ n y, G.dist s y = n → ∀ k ≤ n, ∃ z, G.dist s z = k ∧ Beyond G s z y := by
  intro n
  induction n with
  | zero => intro y hy k hk; exact ⟨y, by omega, beyond_self G s y⟩
  | succ n ih =>
    intro y hy k hk
    rcases Nat.lt_or_ge k (n + 1) with hk' | hk'
    · have hys : y ≠ s := by rintro rfl; simp at hy
      obtain ⟨p, hp, hdp⟩ := exists_parent hG hys
      obtain ⟨z, hz, hzb⟩ := ih p (by omega) k (by omega)
      refine ⟨z, hz, beyond_trans hG hzb ?_⟩
      unfold Beyond
      rw [SimpleGraph.dist_comm (u := p), SimpleGraph.dist_eq_one_iff_adj.mpr hp]
      omega
    · exact ⟨y, by omega, beyond_self G s y⟩

private theorem beyond_chain {V : Type} {G : SimpleGraph V} (hG : G.IsTree) {s x y w : V}
    (hx : Beyond G s x w) (hy : Beyond G s y w) (hd : G.dist s x ≤ G.dist s y) :
    Beyond G s x y := by
  obtain ⟨z, hz, hzy⟩ := exists_ancestor hG.connected s _ y rfl _ hd
  have := ancestor_unique hG _ z x rfl (beyond_trans hG.connected hzy hy) hx hz
  subst this
  exact hzy

/-! ### Clusters of an unrooted tree seen from a leaf -/

/-- The **cluster** of a vertex `v` seen from the leaf labeled `a`: the taxa `x ≠ a` whose leaf
lies beyond `v`, i.e. `v` is on the path from the leaf `a` to the leaf `x`. -/
noncomputable def cluster {X : Type} [Fintype X] [DecidableEq X] (T : UnrootedBinaryTree X)
    (a : X) (v : T.V) : Finset X :=
  Finset.univ.filter fun x => x ≠ a ∧
    T.G.dist (T.label a) v + T.G.dist v (T.label x) = T.G.dist (T.label a) (T.label x)

/-- The clusters of all vertices seen from the leaf labeled `a`. (The cluster of the leaf `a`
itself is the set of all other taxa, which is also the cluster of its neighbor.) -/
noncomputable def clusterSet {X : Type} [Fintype X] [DecidableEq X] (T : UnrootedBinaryTree X)
    (a : X) : Finset (Finset X) :=
  Finset.univ.image (cluster T a)

private theorem dist_iso {V W : Type} {G : SimpleGraph V} {G' : SimpleGraph W}
    (hG : G.Connected) (e : G ≃g G') (u v : V) : G'.dist (e u) (e v) = G.dist u v := by
  have hG' : G'.Connected := (e.connected_iff).mp hG
  apply le_antisymm
  · obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist u v
    exact (SimpleGraph.dist_le (p.map e.toHom)).trans (by simp [hp])
  · obtain ⟨p, hp⟩ := hG'.exists_walk_length_eq_dist (e u) (e v)
    have := SimpleGraph.dist_le (p.map e.symm.toHom)
    simp only [SimpleGraph.Walk.length_map] at this
    simpa [hp] using this

/-- Isomorphic trees have the same clusters. -/
theorem clusterSet_eq_of_iso {X : Type} [Fintype X] [DecidableEq X]
    {T T' : UnrootedBinaryTree X} (h : T.Iso T') (a : X) :
    clusterSet T a = clusterSet T' a := by
  obtain ⟨e, he⟩ := h
  have hc : ∀ v, cluster T' a (e v) = cluster T a v := by
    intro v
    ext x
    simp only [cluster, Finset.mem_filter, Finset.mem_univ, true_and, ← he,
      dist_iso T.isTree.connected e]
  unfold clusterSet
  ext C
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨v, rfl⟩; exact ⟨e v, hc v⟩
  · rintro ⟨w, rfl⟩; exact ⟨e.symm w, by rw [← hc, e.apply_symm_apply]⟩



private theorem cluster_mem {X : Type} [Fintype X] [DecidableEq X] (T : UnrootedBinaryTree X)
    (a : X) (v : T.V) (x : X) :
    x ∈ cluster T a v ↔ x ≠ a ∧ Beyond T.G (T.label a) v (T.label x) := by
  simp [cluster, Beyond]

private theorem degree_label {X : Type} (T : UnrootedBinaryTree X) (x : X) :
    T.G.degree (T.label x) = 1 := (T.label x).2

private theorem adj_unique_of_degree_one {V : Type} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {v u w : V} (hv : G.degree v = 1) (hu : G.Adj v u) (hw : G.Adj v w) :
    u = w := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_one] at hv
  obtain ⟨z, hz⟩ := hv
  have hu' : u ∈ G.neighborFinset v := (G.mem_neighborFinset v u).mpr hu
  have hw' : w ∈ G.neighborFinset v := (G.mem_neighborFinset v w).mpr hw
  rw [hz, Finset.mem_singleton] at hu' hw'
  rw [hu', hw']

/-- A leaf other than the root has no child. -/
private theorem no_child_of_leaf {V : Type} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (hG : G.IsTree) {s v c : V} (hv : G.degree v = 1) (hvs : v ≠ s)
    (hc : G.Adj v c) (hd : G.dist s c = G.dist s v + 1) : False := by
  obtain ⟨p, hp, hdp⟩ := exists_parent hG.connected hvs
  have := adj_unique_of_degree_one hv hc hp
  subst this
  omega

/-- A vertex of degree three other than the root has two distinct children, and every child
is one of them. -/
private theorem two_children {V : Type} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (hG : G.IsTree) {s v : V} (hv : G.degree v = 3) (hvs : v ≠ s) :
    ∃ c₁ c₂, c₁ ≠ c₂ ∧ G.Adj v c₁ ∧ G.Adj v c₂ ∧ G.dist s c₁ = G.dist s v + 1 ∧
      G.dist s c₂ = G.dist s v + 1 ∧
      ∀ c, G.Adj v c → G.dist s c = G.dist s v + 1 → c = c₁ ∨ c = c₂ := by
  classical
  obtain ⟨p, hp, hdp⟩ := exists_parent hG.connected hvs
  have hpm : p ∈ G.neighborFinset v := (G.mem_neighborFinset v p).mpr hp
  have hcard : ((G.neighborFinset v).erase p).card = 2 := by
    rw [Finset.card_erase_of_mem hpm, SimpleGraph.card_neighborFinset_eq_degree, hv]
  obtain ⟨c₁, c₂, hne, hcs⟩ := Finset.card_eq_two.mp hcard
  have hchild : ∀ c ∈ (G.neighborFinset v).erase p,
      G.Adj v c ∧ G.dist s c = G.dist s v + 1 := by
    intro c hc
    rw [Finset.mem_erase, SimpleGraph.mem_neighborFinset] at hc
    refine ⟨hc.2, ?_⟩
    rcases hG.dist_eq_dist_add_one_of_adj s hc.2 with h | h
    · exact absurd (parent_unique hG hc.2 hp h.symm hdp) hc.1
    · exact h
  have h₁ := hchild c₁ (by rw [hcs]; simp)
  have h₂ := hchild c₂ (by rw [hcs]; simp)
  refine ⟨c₁, c₂, hne, h₁.1, h₂.1, h₁.2, h₂.2, fun c hc hdc => ?_⟩
  have : c ∈ (G.neighborFinset v).erase p := by
    rw [Finset.mem_erase, SimpleGraph.mem_neighborFinset]
    exact ⟨fun h => by subst h; omega, hc⟩
  rw [hcs] at this
  simpa using this

private theorem cluster_root {X : Type} [Fintype X] [DecidableEq X] (T : UnrootedBinaryTree X)
    (a : X) : cluster T a (T.label a) = Finset.univ.erase a := by
  ext x
  simp [cluster_mem, Beyond]

/-- Beyond every vertex lies a leaf other than the root. -/
private theorem exists_leaf_beyond {V : Type} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (hG : G.IsTree) (hdeg : ∀ v, G.degree v ≠ 1 → G.degree v = 3)
    {s v : V} (hvs : v ≠ s) : ∃ w, G.degree w = 1 ∧ w ≠ s ∧ Beyond G s v w := by
  classical
  obtain ⟨w, hw, hmax⟩ := Finset.exists_max_image (Finset.univ.filter (Beyond G s v))
    (G.dist s) ⟨v, by simp [beyond_self]⟩
  rw [Finset.mem_filter] at hw
  have hds : 0 < G.dist s v := hG.connected.pos_dist_of_ne (Ne.symm hvs)
  have hws : w ≠ s := by
    rintro rfl
    have h := hw.2
    unfold Beyond at h
    simp only [SimpleGraph.dist_self] at h
    omega
  refine ⟨w, ?_, hws, hw.2⟩
  by_contra h1
  obtain ⟨c₁, c₂, hne, ha₁, -, hd₁, -, -⟩ := two_children hG (hdeg w h1) hws
  have := hmax c₁ (by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, beyond_trans hG.connected hw.2 ?_⟩
    unfold Beyond
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr ha₁]
    omega)
  omega


private theorem label_ne_root {X : Type} (T : UnrootedBinaryTree X) {a x : X} (hx : x ≠ a) :
    (T.label x : T.V) ≠ T.label a := fun h => hx (T.label.injective (Subtype.ext h))

private theorem exists_label {X : Type} (T : UnrootedBinaryTree X) {w : T.V}
    (hw : T.G.degree w = 1) : ∃ x, (T.label x : T.V) = w :=
  ⟨T.label.symm ⟨w, hw⟩, by simp⟩

private theorem cluster_label {X : Type} [Fintype X] [DecidableEq X] (T : UnrootedBinaryTree X)
    {a x : X} (hx : x ≠ a) : cluster T a (T.label x) = {x} := by
  ext y
  rw [cluster_mem, Finset.mem_singleton]
  constructor
  · rintro ⟨hy, hb⟩
    by_contra hyx
    have hne : (T.label x : T.V) ≠ T.label y := fun h =>
      hyx (T.label.injective (Subtype.ext h)).symm
    obtain ⟨c, hc, hdc, -⟩ := exists_child_toward T.isTree.connected hb hne
    exact no_child_of_leaf T.isTree (degree_label T x) (label_ne_root T hx) hc hdc
  · rintro rfl
    exact ⟨hx, beyond_self _ _ _⟩

/-- The neighbor of the root leaf has the full cluster. -/
private theorem exists_root_nbr {X : Type} [Fintype X] [DecidableEq X]
    (T : UnrootedBinaryTree X) (a : X) :
    ∃ r, T.G.Adj (T.label a) r ∧ cluster T a r = Finset.univ.erase a := by
  have hdeg := degree_label T a
  rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_one] at hdeg
  obtain ⟨r, hr⟩ := hdeg
  have hra : T.G.Adj (T.label a) r := by
    rw [← SimpleGraph.mem_neighborFinset, hr]; exact Finset.mem_singleton_self r
  refine ⟨r, hra, ?_⟩
  ext x
  rw [cluster_mem, Finset.mem_erase]
  simp only [Finset.mem_univ, and_true]
  constructor
  · exact fun h => h.1
  · intro hx
    refine ⟨hx, ?_⟩
    have hpos := T.isTree.connected.pos_dist_of_ne (label_ne_root T hx).symm
    obtain ⟨z, hz, hzb⟩ := exists_ancestor T.isTree.connected (T.label a) _ _ rfl 1 hpos
    have hza : T.G.Adj (T.label a) z := SimpleGraph.dist_eq_one_iff_adj.mp hz
    have : z = r := by
      have := (T.G.mem_neighborFinset _ z).mpr hza
      rw [hr, Finset.mem_singleton] at this
      exact this
    exact this ▸ hzb

/-- The clusters of a tree seen from a leaf form a binary hierarchy on the other taxa
(Semple & Steel 2003, Section 3.1). -/
theorem isBinaryHierarchy_clusterSet {X : Type} [Fintype X] [DecidableEq X]
    (T : UnrootedBinaryTree X) (a : X) :
    IsBinaryHierarchy (Finset.univ.erase a) (clusterSet T a) := by
  have hG := T.isTree
  set s : T.V := (T.label a : T.V)
  obtain ⟨r, hra, hr⟩ := exists_root_nbr T a
  have hrs : r ≠ s := hra.ne.symm
  have hmem : ∀ C, C ∈ clusterSet T a ↔ ∃ v, cluster T a v = C := by
    intro C; simp [clusterSet]
  have hsub : ∀ v, cluster T a v ⊆ Finset.univ.erase a := by
    intro v x hx
    rw [cluster_mem] at hx
    exact Finset.mem_erase.mpr ⟨hx.1, Finset.mem_univ _⟩
  -- every cluster is the cluster of a vertex other than the root
  have hnr : ∀ v, ∃ w, w ≠ s ∧ cluster T a w = cluster T a v := by
    intro v
    by_cases hv : v = s
    · exact ⟨r, hrs, by rw [hr, hv, cluster_root]⟩
    · exact ⟨v, hv, rfl⟩
  refine ⟨(hmem _).mpr ⟨r, hr⟩, ?_, ?_, ?_, ?_⟩
  · intro C hC
    obtain ⟨v, rfl⟩ := (hmem C).mp hC
    obtain ⟨w, hws, hw⟩ := hnr v
    rw [← hw]
    refine ⟨?_, hsub w⟩
    obtain ⟨u, hu1, hus, hub⟩ := exists_leaf_beyond hG T.degree_eq_three hws
    obtain ⟨x, rfl⟩ := exists_label T hu1
    exact ⟨x, (cluster_mem T a w x).mpr ⟨fun h => hus (by rw [h]), hub⟩⟩
  · intro x hx
    exact (hmem _).mpr ⟨_, cluster_label T (Finset.ne_of_mem_erase hx)⟩
  · intro C hC D hD
    obtain ⟨u, rfl⟩ := (hmem C).mp hC
    obtain ⟨v, rfl⟩ := (hmem D).mp hD
    by_cases hcommon : ∃ x, x ∈ cluster T a u ∧ x ∈ cluster T a v
    · obtain ⟨x, hxu, hxv⟩ := hcommon
      rw [cluster_mem] at hxu hxv
      rcases le_total (T.G.dist s u) (T.G.dist s v) with hd | hd
      · have huv := beyond_chain hG hxu.2 hxv.2 hd
        right; left
        intro y hy
        rw [cluster_mem] at hy ⊢
        exact ⟨hy.1, beyond_trans hG.connected huv hy.2⟩
      · have hvu := beyond_chain hG hxv.2 hxu.2 hd
        left
        intro y hy
        rw [cluster_mem] at hy ⊢
        exact ⟨hy.1, beyond_trans hG.connected hvu hy.2⟩
    · right; right
      rw [Finset.disjoint_left]
      exact fun x hxu hxv => hcommon ⟨x, hxu, hxv⟩
  · intro C hC hcard
    obtain ⟨v₀, rfl⟩ := (hmem C).mp hC
    obtain ⟨v, hvs, hv⟩ := hnr v₀
    rw [← hv] at hcard ⊢
    have hv3 : T.G.degree v = 3 := by
      apply T.degree_eq_three
      intro h1
      obtain ⟨x, rfl⟩ := exists_label T h1
      have hxa : x ≠ a := fun h => hvs (by rw [h])
      rw [cluster_label T hxa] at hcard
      simp at hcard
    obtain ⟨c₁, c₂, hne, ha₁, ha₂, hd₁, hd₂, hall⟩ := two_children hG hv3 hvs
    refine ⟨cluster T a c₁, (hmem _).mpr ⟨c₁, rfl⟩, cluster T a c₂, (hmem _).mpr ⟨c₂, rfl⟩,
      ?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro x hx₁ hx₂
      rw [cluster_mem] at hx₁ hx₂
      exact hne (ancestor_unique hG _ c₁ c₂ rfl hx₁.2 hx₂.2 (hd₁.trans hd₂.symm))
    · ext x
      rw [Finset.mem_union, cluster_mem, cluster_mem, cluster_mem]
      constructor
      · rintro (⟨hx, hb⟩ | ⟨hx, hb⟩)
        · exact ⟨hx, beyond_of_child hG.connected ha₁ hd₁ hb⟩
        · exact ⟨hx, beyond_of_child hG.connected ha₂ hd₂ hb⟩
      · rintro ⟨hx, hb⟩
        have hne' : v ≠ T.label x := by
          intro h
          have := degree_label T x
          rw [← h, hv3] at this
          omega
        obtain ⟨c, hc, hdc, hcb⟩ := exists_child_toward hG.connected hb hne'
        rcases hall c hc hdc with rfl | rfl
        · exact Or.inl ⟨hx, hcb⟩
        · exact Or.inr ⟨hx, hcb⟩



private theorem cluster_nonempty {X : Type} [Fintype X] [DecidableEq X]
    (T : UnrootedBinaryTree X) (a : X) {v : T.V} (hv : v ≠ T.label a) :
    (cluster T a v).Nonempty := by
  obtain ⟨u, hu1, hus, hub⟩ := exists_leaf_beyond T.isTree T.degree_eq_three hv
  obtain ⟨x, rfl⟩ := exists_label T hu1
  exact ⟨x, (cluster_mem T a v x).mpr ⟨fun h => hus (by rw [h]), hub⟩⟩

private theorem cluster_mono {X : Type} [Fintype X] [DecidableEq X]
    (T : UnrootedBinaryTree X) (a : X) {u v : T.V} (h : Beyond T.G (T.label a) u v) :
    cluster T a v ⊆ cluster T a u := by
  intro y hy
  rw [cluster_mem] at hy ⊢
  exact ⟨hy.1, beyond_trans T.isTree.connected h hy.2⟩

/-- Two vertices whose clusters meet are comparable. -/
private theorem beyond_of_meet {X : Type} [Fintype X] [DecidableEq X]
    (T : UnrootedBinaryTree X) (a : X) {u v : T.V} {x : X} (hu : x ∈ cluster T a u)
    (hv : x ∈ cluster T a v) (hd : T.G.dist (T.label a) u ≤ T.G.dist (T.label a) v) :
    Beyond T.G (T.label a) u v := by
  rw [cluster_mem] at hu hv
  exact beyond_chain T.isTree hu.2 hv.2 hd

/-- The cluster of a child is a proper subset of the cluster of its parent. -/
private theorem cluster_child_ne {X : Type} [Fintype X] [DecidableEq X]
    (T : UnrootedBinaryTree X) (a : X) {u c : T.V} (hus : u ≠ T.label a)
    (hc : T.G.Adj u c) (hd : T.G.dist (T.label a) c = T.G.dist (T.label a) u + 1) :
    cluster T a c ≠ cluster T a u := by
  have hG := T.isTree
  have hu3 : T.G.degree u = 3 := T.degree_eq_three u fun h1 =>
    no_child_of_leaf hG h1 hus hc hd
  obtain ⟨c₁, c₂, hne, ha₁, ha₂, hd₁, hd₂, hall⟩ := two_children hG hu3 hus
  have hcs : ∀ {w}, T.G.dist (T.label a) w = T.G.dist (T.label a) u + 1 → w ≠ T.label a := by
    intro w hw h; rw [h, SimpleGraph.dist_self] at hw; omega
  -- the other child
  obtain ⟨c', hc'ne, ha', hd'⟩ : ∃ c', c' ≠ c ∧ T.G.Adj u c' ∧
      T.G.dist (T.label a) c' = T.G.dist (T.label a) u + 1 := by
    rcases hall c hc hd with rfl | rfl
    · exact ⟨c₂, Ne.symm hne, ha₂, hd₂⟩
    · exact ⟨c₁, hne, ha₁, hd₁⟩
  intro heq
  obtain ⟨x, hx⟩ := cluster_nonempty T a (hcs hd')
  have hxu : x ∈ cluster T a u :=
    cluster_mono T a (by unfold Beyond; rw [SimpleGraph.dist_eq_one_iff_adj.mpr ha']; omega) hx
  rw [← heq] at hxu
  rw [cluster_mem] at hx hxu
  exact hc'ne (ancestor_unique hG _ c' c rfl hx.2 hxu.2 (hd'.trans hd.symm))

/-- On the vertices other than the root, the cluster determines the vertex. -/
private theorem cluster_injective {X : Type} [Fintype X] [DecidableEq X]
    (T : UnrootedBinaryTree X) (a : X) {u v : T.V} (hu : u ≠ T.label a) (hv : v ≠ T.label a)
    (h : cluster T a u = cluster T a v) : u = v := by
  wlog hd : T.G.dist (T.label a) u ≤ T.G.dist (T.label a) v generalizing u v
  · exact (this hv hu h.symm (by omega)).symm
  obtain ⟨x, hx⟩ := cluster_nonempty T a hu
  have huv := beyond_of_meet T a hx (h ▸ hx) hd
  by_contra hne
  obtain ⟨c, hc, hdc, hcb⟩ := exists_child_toward T.isTree.connected huv hne
  have h1 := cluster_mono T a hcb
  have h2 := cluster_mono T a
    (by unfold Beyond; rw [SimpleGraph.dist_eq_one_iff_adj.mpr hc]; omega :
      Beyond T.G (T.label a) u c)
  exact cluster_child_ne T a hu hc hdc (le_antisymm h2 (h ▸ h1))

private theorem exists_cluster_ne_root {X : Type} [Fintype X] [DecidableEq X]
    (T : UnrootedBinaryTree X) (a : X) (v : T.V) :
    ∃ w : T.V, w ≠ T.label a ∧ cluster T a w = cluster T a v := by
  obtain ⟨r, hra, hr⟩ := exists_root_nbr T a
  by_cases hv : v = T.label a
  · exact ⟨r, hra.ne.symm, by rw [hr, hv, cluster_root]⟩
  · exact ⟨v, hv, rfl⟩

/-- No cluster lies strictly between the clusters of a parent and a child. -/
private theorem no_cluster_between {X : Type} [Fintype X] [DecidableEq X]
    (T : UnrootedBinaryTree X) (a : X) {u v w : T.V} (hv : v ≠ T.label a)
    (hd : T.G.dist (T.label a) v = T.G.dist (T.label a) u + 1)
    (h₁ : cluster T a v ⊆ cluster T a w) (h₂ : cluster T a w ⊆ cluster T a u)
    (h₁' : cluster T a v ≠ cluster T a w) (h₂' : cluster T a w ≠ cluster T a u) : False := by
  obtain ⟨x, hx⟩ := cluster_nonempty T a hv
  rcases Nat.lt_or_ge (T.G.dist (T.label a) w) (T.G.dist (T.label a) v) with hvw | hvw
  · rcases Nat.lt_or_ge (T.G.dist (T.label a) u) (T.G.dist (T.label a) w) with hwu | hwu
    · omega
    · exact h₂' (le_antisymm h₂ (cluster_mono T a (beyond_of_meet T a (h₁ hx) (h₂ (h₁ hx)) hwu)))
  · exact h₁' (le_antisymm h₁ (cluster_mono T a (beyond_of_meet T a hx (h₁ hx) hvw)))

private theorem exists_match {X : Type} [Fintype X] [DecidableEq X]
    (T T' : UnrootedBinaryTree X) (a : X) (h : clusterSet T a = clusterSet T' a) (v : T.V) :
    ∃ w : T'.V, w ≠ T'.label a ∧ cluster T' a w = cluster T a v := by
  have : cluster T a v ∈ clusterSet T' a := h ▸ Finset.mem_image_of_mem _ (Finset.mem_univ v)
  obtain ⟨w₀, -, hw₀⟩ := Finset.mem_image.mp this
  obtain ⟨w, hw, hw'⟩ := exists_cluster_ne_root T' a w₀
  exact ⟨w, hw, hw'.trans hw₀⟩

/-- The vertex of `T'` with the same cluster as the vertex `v` of `T` (the root leaf goes to
the root leaf). -/
private noncomputable def matchVertex {X : Type} [Fintype X] [DecidableEq X]
    (T T' : UnrootedBinaryTree X) (a : X) (h : clusterSet T a = clusterSet T' a) (v : T.V) :
    T'.V := by
  classical
  exact if v = T.label a then T'.label a else Classical.choose (exists_match T T' a h v)

private theorem matchVertex_spec {X : Type} [Fintype X] [DecidableEq X]
    (T T' : UnrootedBinaryTree X) (a : X) (h : clusterSet T a = clusterSet T' a) (v : T.V) :
    cluster T' a (matchVertex T T' a h v) = cluster T a v ∧
      (matchVertex T T' a h v = T'.label a ↔ v = T.label a) := by
  classical
  unfold matchVertex
  by_cases hv : v = T.label a
  · simp [hv, cluster_root]
  · simp only [hv, ↓reduceIte, iff_false]
    have := Classical.choose_spec (exists_match T T' a h v)
    exact ⟨this.2, this.1⟩

private theorem matchVertex_matchVertex {X : Type} [Fintype X] [DecidableEq X]
    (T T' : UnrootedBinaryTree X) (a : X) (h : clusterSet T a = clusterSet T' a) (v : T.V) :
    matchVertex T' T a h.symm (matchVertex T T' a h v) = v := by
  obtain ⟨h1, h2⟩ := matchVertex_spec T T' a h v
  obtain ⟨h3, h4⟩ := matchVertex_spec T' T a h.symm (matchVertex T T' a h v)
  by_cases hv : v = T.label a
  · exact h4.mpr (h2.mpr hv) |>.trans hv.symm
  · exact cluster_injective T a (fun h' => hv (h2.mp (h4.mp h'))) hv (h3.trans h1)

private theorem matchVertex_adj {X : Type} [Fintype X] [DecidableEq X]
    (T T' : UnrootedBinaryTree X) (a : X) (h : clusterSet T a = clusterSet T' a) {u v : T.V}
    (huv : T.G.Adj u v) : T'.G.Adj (matchVertex T T' a h u) (matchVertex T T' a h v) := by
  have hG := T.isTree
  have hG' := T'.isTree
  -- adjacency to the root leaf
  have hroot : ∀ {v : T.V}, T.G.Adj (T.label a) v →
      T'.G.Adj (matchVertex T T' a h (T.label a)) (matchVertex T T' a h v) := by
    intro v hv
    obtain ⟨r, hra, hr⟩ := exists_root_nbr T a
    obtain ⟨r', hra', hr'⟩ := exists_root_nbr T' a
    have hvr : v = r := adj_unique_of_degree_one (degree_label T a) hv hra
    subst hvr
    obtain ⟨h1, h2⟩ := matchVertex_spec T T' a h (T.label a)
    obtain ⟨h3, h4⟩ := matchVertex_spec T T' a h v
    rw [h2.mpr rfl]
    have hvs : matchVertex T T' a h v ≠ T'.label a := fun e => hra.ne.symm (h4.mp e)
    rwa [cluster_injective T' a hvs hra'.ne.symm (h3.trans (hr.trans hr'.symm))]
  by_cases hu : u = T.label a
  · subst hu; exact hroot huv
  by_cases hv : v = T.label a
  · subst hv; exact (hroot huv.symm).symm
  wlog hd : T.G.dist (T.label a) v = T.G.dist (T.label a) u + 1 generalizing u v
  · have hd' : T.G.dist (T.label a) u = T.G.dist (T.label a) v + 1 := by
      rcases hG.dist_eq_dist_add_one_of_adj (T.label a) huv with h' | h'
      · exact h'
      · exact absurd h' hd
    exact (this huv.symm hv hu hd').symm
  obtain ⟨hcu, hu'⟩ := matchVertex_spec T T' a h u
  obtain ⟨hcv, hv'⟩ := matchVertex_spec T T' a h v
  set u' := matchVertex T T' a h u
  set v' := matchVertex T T' a h v
  have hu's : u' ≠ T'.label a := fun e => hu (hu'.mp e)
  have hv's : v' ≠ T'.label a := fun e => hv (hv'.mp e)
  have hsub : cluster T a v ⊆ cluster T a u :=
    cluster_mono T a (by unfold Beyond; rw [SimpleGraph.dist_eq_one_iff_adj.mpr huv]; omega)
  have hne : cluster T a v ≠ cluster T a u := cluster_child_ne T a hu huv hd
  obtain ⟨x, hx⟩ := cluster_nonempty T a hv
  have hb : Beyond T'.G (T'.label a) u' v' := by
    rcases le_total (T'.G.dist (T'.label a) u') (T'.G.dist (T'.label a) v') with h' | h'
    · exact beyond_of_meet T' a (hcu ▸ hsub hx) (hcv ▸ hx) h'
    · have := cluster_mono T' a (beyond_of_meet T' a (hcv ▸ hx) (hcu ▸ hsub hx) h')
      rw [hcu, hcv] at this
      exact absurd (le_antisymm hsub this) hne
  have hne' : u' ≠ v' := fun e => hne (by rw [← hcu, ← hcv, e])
  obtain ⟨c', hc', hdc', hcb'⟩ := exists_child_toward hG'.connected hb hne'
  by_cases hcv' : c' = v'
  · exact hcv' ▸ hc'
  exfalso
  have hc's : c' ≠ T'.label a := by
    intro e; rw [e, SimpleGraph.dist_self] at hdc'; omega
  have hmem : cluster T' a c' ∈ clusterSet T a := h ▸ Finset.mem_image_of_mem _ (Finset.mem_univ _)
  obtain ⟨w₀, -, hw₀⟩ := Finset.mem_image.mp hmem
  obtain ⟨w, hws, hw⟩ := exists_cluster_ne_root T a w₀
  rw [hw₀] at hw
  have h₁ : cluster T a v ⊆ cluster T a w := by rw [hw, ← hcv]; exact cluster_mono T' a hcb'
  have h₂ : cluster T a w ⊆ cluster T a u := by
    rw [hw, ← hcu]
    exact cluster_mono T' a (by unfold Beyond; rw [SimpleGraph.dist_eq_one_iff_adj.mpr hc']; omega)
  have h₁' : cluster T a v ≠ cluster T a w := by
    rw [hw, ← hcv]; exact fun e => hcv' (cluster_injective T' a hc's hv's e.symm)
  have h₂' : cluster T a w ≠ cluster T a u := by
    rw [hw, ← hcu]; exact cluster_child_ne T' a hu's hc' hdc'
  exact no_cluster_between T a hv hd h₁ h₂ h₁' h₂'

/-- Two trees with the same clusters seen from the leaf `a` are isomorphic: the clusters
determine the tree. -/
theorem iso_of_clusterSet_eq {X : Type} [Fintype X] [DecidableEq X]
    {T T' : UnrootedBinaryTree X} (a : X)
    (h : clusterSet T a = clusterSet T' a) : T.Iso T' := by
  refine ⟨⟨⟨matchVertex T T' a h, matchVertex T' T a h.symm,
    matchVertex_matchVertex T T' a h, matchVertex_matchVertex T' T a h.symm⟩, ?_⟩, ?_⟩
  · intro u v
    constructor
    · intro huv
      have := matchVertex_adj T' T a h.symm huv
      simpa only [Equiv.coe_fn_mk, matchVertex_matchVertex] using this
    · exact matchVertex_adj T T' a h
  · intro x
    change matchVertex T T' a h (T.label x) = T'.label x
    by_cases hx : x = a
    · rw [hx]; exact (matchVertex_spec T T' a h _).2.mpr rfl
    · obtain ⟨h1, h2⟩ := matchVertex_spec T T' a h (T.label x)
      refine cluster_injective T' a (fun e => label_ne_root T hx (h2.mp e))
        (label_ne_root T' hx) ?_
      rw [h1, cluster_label T hx, cluster_label T' hx]

/-- The graph of a parent function: `v` is joined to `par v` for every `v ≠ ρ`. -/
private def parGraph {V : Type} (ρ : V) (par : V → V) : SimpleGraph V :=
  SimpleGraph.fromRel fun u v => u ≠ ρ ∧ par u = v

private theorem parGraph_adj {V : Type} {ρ : V} {par : V → V} {depth : V → ℕ}
    (hpar : ∀ v, v ≠ ρ → depth (par v) + 1 = depth v) {u v : V} :
    (parGraph ρ par).Adj u v ↔ (u ≠ ρ ∧ par u = v) ∨ (v ≠ ρ ∧ par v = u) := by
  rw [parGraph, SimpleGraph.fromRel_adj]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    rintro rfl
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := hpar u h1; rw [h2] at this; omega
    · have := hpar u h1; rw [h2] at this; omega

private theorem parGraph_reachable {V : Type} {ρ : V} {par : V → V} {depth : V → ℕ}
    (hpar : ∀ v, v ≠ ρ → depth (par v) + 1 = depth v) :
    ∀ n v, depth v = n → (parGraph ρ par).Reachable ρ v := by
  intro n
  induction n with
  | zero =>
    intro v hv
    by_cases h : v = ρ
    · rw [h]
    · have := hpar v h; omega
  | succ n ih =>
    intro v hv
    by_cases h : v = ρ
    · rw [h]
    · have hp := hpar v h
      exact (ih (par v) (by omega)).trans
        (SimpleGraph.Adj.reachable ((parGraph_adj hpar).mpr (Or.inr ⟨h, rfl⟩)))

private theorem parGraph_connected {V : Type} {ρ : V} {par : V → V} {depth : V → ℕ}
    (hpar : ∀ v, v ≠ ρ → depth (par v) + 1 = depth v) : (parGraph ρ par).Connected := by
  have h := fun v => parGraph_reachable hpar _ v rfl
  have : Nonempty V := ⟨ρ⟩
  exact ⟨fun u v => (h u).symm.trans (h v)⟩

private theorem parGraph_dist {V : Type} {ρ : V} {par : V → V} {depth : V → ℕ}
    (h0 : depth ρ = 0) (hpar : ∀ v, v ≠ ρ → depth (par v) + 1 = depth v) (v : V) :
    (parGraph ρ par).dist ρ v = depth v := by
  have hlow : ∀ {u w : V} (p : (parGraph ρ par).Walk u w), depth w ≤ depth u + p.length := by
    intro u w p
    induction p with
    | nil => simp
    | @cons x y z hxy p ih =>
      simp only [SimpleGraph.Walk.length_cons]
      rcases (parGraph_adj hpar).mp hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have := hpar x h1; rw [h2] at this; omega
      · have := hpar y h1; rw [h2] at this; omega
  apply le_antisymm
  · -- upper bound: walk up along parents
    have : ∀ n v, depth v = n → (parGraph ρ par).dist ρ v ≤ n := by
      intro n
      induction n with
      | zero =>
        intro v hv
        by_cases h : v = ρ
        · rw [h]; simp
        · have := hpar v h; omega
      | succ n ih =>
        intro v hv
        by_cases h : v = ρ
        · rw [h]; simp
        · have hp := hpar v h
          have hadj : (parGraph ρ par).Adj (par v) v := (parGraph_adj hpar).mpr (Or.inr ⟨h, rfl⟩)
          have h1 := ih (par v) (by omega)
          have h2 := (parGraph_connected hpar).dist_triangle (u := ρ) (v := par v) (w := v)
          rw [SimpleGraph.dist_eq_one_iff_adj.mpr hadj] at h2
          omega
    exact this _ v rfl
  · obtain ⟨p, hp⟩ := (parGraph_connected hpar).exists_walk_length_eq_dist ρ v
    have := hlow p
    omega

private theorem parGraph_isTree {V : Type} [Finite V] {ρ : V} {par : V → V} {depth : V → ℕ}
    (hpar : ∀ v, v ≠ ρ → depth (par v) + 1 = depth v) : (parGraph ρ par).IsTree := by
  classical
  have := Fintype.ofFinite V
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨parGraph_connected hpar, ?_⟩
  let f : {v // v ≠ ρ} → (parGraph ρ par).edgeSet := fun v =>
    ⟨s(v.1, par v.1), (parGraph_adj hpar).mpr (Or.inl ⟨v.2, rfl⟩)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨v, hv⟩ ⟨w, hw⟩ h
      have h' := congrArg Subtype.val h
      simp only [f, Sym2.eq_iff] at h'
      rcases h' with ⟨h1, -⟩ | ⟨h1, h2⟩
      · exact Subtype.ext h1
      · have := hpar v hv; have := hpar w hw
        rw [← h1] at *; rw [h2] at *; omega
    · rintro ⟨e, he⟩
      induction e using Sym2.ind with
      | _ u v =>
      rcases (parGraph_adj hpar).mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨⟨u, h1⟩, Subtype.ext (by simp [f, h2])⟩
      · exact ⟨⟨v, h1⟩, Subtype.ext (by simp [f, h2, Sym2.eq_swap])⟩
  have hc : Fintype.card {v // v ≠ ρ} = Fintype.card V - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, hc]
  have : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨ρ⟩
  omega


/-! ### The tree of a binary hierarchy -/

/-- The members of `H` strictly containing `C`. -/
private def upper {X : Type} [DecidableEq X] (H : Finset (Finset X)) (C : Finset X) :
    Finset (Finset X) :=
  H.filter (C ⊂ ·)

/-- A member of `H` strictly containing `C` of least cardinality (or `C` if there is none). -/
private noncomputable def parentSet {X : Type} [DecidableEq X] (H : Finset (Finset X))
    (C : Finset X) : Finset X :=
  if h : (upper H C).Nonempty then Classical.choose (Finset.exists_min_image _ Finset.card h)
  else C

/-- `D` is a child of `C` in `H`: `D ⊂ C` and every member strictly containing `D` contains
`C`. -/
private def IsChild {X : Type} [DecidableEq X] (H : Finset (Finset X)) (D C : Finset X) :
    Prop :=
  D ⊂ C ∧ ∀ E ∈ H, D ⊂ E → C ⊆ E

private theorem parentSet_spec {X : Type} [DecidableEq X] {S : Finset X}
    {H : Finset (Finset X)} (hH : IsBinaryHierarchy S H) {C : Finset X} (hC : C ∈ H)
    (hCS : C ≠ S) : parentSet H C ∈ H ∧ IsChild H C (parentSet H C) := by
  obtain ⟨hS, hsub, -, hlam, -⟩ := hH
  have hne : (upper H C).Nonempty :=
    ⟨S, Finset.mem_filter.mpr ⟨hS, Finset.ssubset_iff_subset_ne.mpr ⟨(hsub C hC).2, hCS⟩⟩⟩
  have hP := Classical.choose_spec (Finset.exists_min_image _ Finset.card hne)
  simp only [parentSet, hne, ↓reduceDIte]
  set P := Classical.choose (Finset.exists_min_image _ Finset.card hne)
  obtain ⟨hPm, hmin⟩ := hP
  rw [upper, Finset.mem_filter] at hPm
  refine ⟨hPm.1, hPm.2, fun E hE hCE => ?_⟩
  obtain ⟨x, hx⟩ := (hsub C hC).1
  rcases hlam P hPm.1 E hE with h | h | h
  · exact h
  · by_cases hEP : E = P
    · exact hEP ▸ le_rfl
    · have := hmin E (Finset.mem_filter.mpr ⟨hE, hCE⟩)
      have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨h, hEP⟩)
      omega
  · exact absurd (hCE.1 hx) (Finset.disjoint_left.mp h (hPm.2.1 hx))

/-- A child of `C` is the parent set of its children. -/
private theorem parentSet_eq_of_isChild {X : Type} [DecidableEq X] {S : Finset X}
    {H : Finset (Finset X)} (hH : IsBinaryHierarchy S H) {C D : Finset X} (hC : C ∈ H)
    (hD : D ∈ H) (h : IsChild H D C) : D ≠ S ∧ parentSet H D = C := by
  have hDS : D ≠ S := by
    rintro rfl
    exact lt_irrefl _ (h.1.trans_le (hH.2.1 C hC).2)
  obtain ⟨hPm, hPc⟩ := parentSet_spec hH hD hDS
  exact ⟨hDS, le_antisymm (hPc.2 C hC h.1) (h.2 _ hPm hPc.1)⟩

private theorem isChild_unique {X : Type} [DecidableEq X] {H : Finset (Finset X)}
    {C D D' : Finset X} (h : IsChild H D C) (h' : IsChild H D' C) (hD : D ∈ H) (hD' : D' ∈ H)
    (hcomp : D ⊆ D' ∨ D' ⊆ D) : D = D' := by
  by_contra hne
  rcases hcomp with hc | hc
  · have := h.2 D' hD' (Finset.ssubset_iff_subset_ne.mpr ⟨hc, hne⟩)
    exact absurd (this.trans_ssubset h'.1) (lt_irrefl _)
  · have := h'.2 D hD (Finset.ssubset_iff_subset_ne.mpr ⟨hc, Ne.symm hne⟩)
    exact absurd (this.trans_ssubset h.1) (lt_irrefl _)

/-- The two parts of a split are exactly the children. -/
private theorem isChild_iff_split {X : Type} [DecidableEq X] {S : Finset X}
    {H : Finset (Finset X)} (hH : IsBinaryHierarchy S H) {C D₁ D₂ : Finset X} (hC : C ∈ H)
    (h₁ : D₁ ∈ H) (h₂ : D₂ ∈ H) (hd : Disjoint D₁ D₂) (hu : D₁ ∪ D₂ = C) {D : Finset X}
    (hD : D ∈ H) : IsChild H D C ↔ D = D₁ ∨ D = D₂ := by
  obtain ⟨-, hsub, -, hlam, -⟩ := hH
  have child : ∀ {A B : Finset X}, A ∈ H → B ∈ H → Disjoint A B → A ∪ B = C →
      IsChild H A C := by
    intro A B hA hB hAB hABC
    obtain ⟨y, hy⟩ := (hsub B hB).1
    obtain ⟨z, hz⟩ := (hsub A hA).1
    refine ⟨Finset.ssubset_iff_subset_ne.mpr ⟨hABC ▸ Finset.subset_union_left, fun he => ?_⟩,
      fun E hE hAE => ?_⟩
    · have : y ∈ A := he ▸ hABC ▸ Finset.mem_union_right _ hy
      exact Finset.disjoint_left.mp hAB this hy
    · rcases hlam E hE C hC with h | h | h
      · rcases hlam E hE B hB with h' | h' | h'
        · exact absurd (h' (hAE.1 hz)) (Finset.disjoint_left.mp hAB hz)
        · rw [← hABC]; exact Finset.union_subset hAE.1 h'
        · have hEA : E ⊆ A := by
            intro w hw
            have := h hw
            rw [← hABC, Finset.mem_union] at this
            exact this.resolve_right (Finset.disjoint_left.mp h' hw)
          exact absurd (hAE.trans_le hEA) (lt_irrefl _)
      · exact h
      · exact absurd (hABC ▸ Finset.mem_union_left _ hz) (Finset.disjoint_left.mp h (hAE.1 hz))
  have hc₁ := child h₁ h₂ hd hu
  have hc₂ := child h₂ h₁ hd.symm (Finset.union_comm D₂ D₁ ▸ hu)
  constructor
  · intro hc
    obtain ⟨x, hx⟩ := (hsub D hD).1
    rcases hlam D hD D₁ h₁ with h | h | h
    · exact Or.inl (isChild_unique hc hc₁ hD h₁ (Or.inl h))
    · exact Or.inl (isChild_unique hc hc₁ hD h₁ (Or.inr h))
    · rcases hlam D hD D₂ h₂ with h' | h' | h'
      · exact Or.inr (isChild_unique hc hc₂ hD h₂ (Or.inl h'))
      · exact Or.inr (isChild_unique hc hc₂ hD h₂ (Or.inr h'))
      · have := hc.1.1 hx
        rw [← hu, Finset.mem_union] at this
        rcases this with h'' | h''
        · exact absurd h'' (Finset.disjoint_left.mp h hx)
        · exact absurd h'' (Finset.disjoint_left.mp h' hx)
  · rintro (rfl | rfl)
    · exact hc₁
    · exact hc₂


private theorem parGraph_neighborFinset {V : Type} [Fintype V] [DecidableEq V] {ρ : V}
    {par : V → V} {depth : V → ℕ} (hpar : ∀ v, v ≠ ρ → depth (par v) + 1 = depth v)
    [DecidableRel (parGraph ρ par).Adj] (v : V) :
    (parGraph ρ par).neighborFinset v =
      (if v = ρ then ∅ else {par v}) ∪ Finset.univ.filter (fun w => w ≠ ρ ∧ par w = v) := by
  ext w
  rw [SimpleGraph.mem_neighborFinset, parGraph_adj hpar, Finset.mem_union, Finset.mem_filter]
  split_ifs with h <;> simp [h, eq_comm]

/-- The parent in the tree of a binary hierarchy. -/
private noncomputable def hierPar {X : Type} [DecidableEq X] {S : Finset X}
    {H : Finset (Finset X)} (hH : IsBinaryHierarchy S H) :
    Option {C // C ∈ H} → Option {C // C ∈ H}
  | none => none
  | some C => if h : C.1 = S then none else some ⟨parentSet H C.1, (parentSet_spec hH C.2 h).1⟩

/-- The depth in the tree of a binary hierarchy. -/
private def hierDepth {X : Type} [DecidableEq X] (H : Finset (Finset X)) :
    Option {C // C ∈ H} → ℕ
  | none => 0
  | some C => (upper H C.1).card + 1

private theorem hierDepth_par {X : Type} [DecidableEq X] {S : Finset X}
    {H : Finset (Finset X)} (hH : IsBinaryHierarchy S H) :
    ∀ v, v ≠ none → hierDepth H (hierPar hH v) + 1 = hierDepth H v := by
  rintro (_ | ⟨C, hC⟩) hv
  · exact absurd rfl hv
  by_cases hCS : C = S
  · subst hCS
    have : upper H C = ∅ := by
      ext E
      simp only [upper, Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      exact fun hE hlt => absurd (hlt.trans_le (hH.2.1 E hE).2) (lt_irrefl _)
    simp [hierPar, hierDepth, this]
  · obtain ⟨hPm, hPc⟩ := parentSet_spec hH hC hCS
    have hup : upper H C = insert (parentSet H C) (upper H (parentSet H C)) := by
      ext E
      simp only [upper, Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hE, hlt⟩
        by_cases he : E = parentSet H C
        · exact Or.inl he
        · exact Or.inr ⟨hE, Finset.ssubset_iff_subset_ne.mpr ⟨hPc.2 E hE hlt, Ne.symm he⟩⟩
      · rintro (rfl | ⟨hE, hlt⟩)
        · exact ⟨hPm, hPc.1⟩
        · exact ⟨hE, hPc.1.trans hlt⟩
    have hnot : parentSet H C ∉ upper H (parentSet H C) := by
      simp [upper]
    simp only [hierPar, hCS, dite_false, hierDepth]
    rw [hup, Finset.card_insert_of_notMem hnot]


private theorem hierPar_some_eq_some {X : Type} [DecidableEq X] {S : Finset X}
    {H : Finset (Finset X)} (hH : IsBinaryHierarchy S H) (C D : {C // C ∈ H}) :
    hierPar hH (some D) = some C ↔ IsChild H D.1 C.1 := by
  constructor
  · intro h
    by_cases hDS : D.1 = S
    · simp [hierPar, hDS] at h
    · simp only [hierPar, hDS, dite_false, Option.some.injEq] at h
      rw [← h]
      exact (parentSet_spec hH D.2 hDS).2
  · intro h
    obtain ⟨hDS, hP⟩ := parentSet_eq_of_isChild hH C.2 D.2 h
    simp only [hierPar, hDS, dite_false, Option.some.injEq]
    exact Subtype.ext hP

private theorem hierPar_some_eq_none {X : Type} [DecidableEq X] {S : Finset X}
    {H : Finset (Finset X)} (hH : IsBinaryHierarchy S H) (D : {C // C ∈ H}) :
    hierPar hH (some D) = none ↔ D.1 = S := by
  by_cases hDS : D.1 = S <;> simp [hierPar, hDS]

private theorem hier_degree_none {X : Type} [DecidableEq X] {S : Finset X}
    {H : Finset (Finset X)} (hH : IsBinaryHierarchy S H)
    [DecidableRel (parGraph none (hierPar hH)).Adj] :
    (parGraph none (hierPar hH)).degree none = 1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    parGraph_neighborFinset (hierDepth_par hH), Finset.card_eq_one]
  refine ⟨some ⟨S, hH.1⟩, ?_⟩
  simp only [↓reduceIte, Finset.empty_union]
  ext w
  rcases w with _ | D
  · simp
  · simp [hierPar_some_eq_none, Subtype.ext_iff]

private theorem hier_degree_some {X : Type} [DecidableEq X] {S : Finset X}
    {H : Finset (Finset X)} (hH : IsBinaryHierarchy S H)
    [DecidableRel (parGraph none (hierPar hH)).Adj] (C : {C // C ∈ H}) :
    (parGraph none (hierPar hH)).degree (some C) = if C.1.card = 1 then 1 else 3 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    parGraph_neighborFinset (hierDepth_par hH)]
  simp only [reduceCtorEq, ↓reduceIte]
  have hcne := (hH.2.1 C.1 C.2).1
  split_ifs with h1
  · have : Finset.univ.filter (fun w : Option {C // C ∈ H} => w ≠ none ∧
        hierPar hH w = some C) = ∅ := by
      ext w
      rcases w with _ | D
      · simp
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false, not_and]
        intro _ hD
        rw [hierPar_some_eq_some] at hD
        obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h1
        have hDne := (hH.2.1 D.1 D.2).1
        have := hD.1
        rw [hx] at this
        exact absurd ((Finset.Nonempty.subset_singleton_iff hDne).mp this.1) this.ne
    rw [this, Finset.union_empty, Finset.card_singleton]
  · have h2 : 1 < C.1.card := by have := hcne.card_pos; omega
    obtain ⟨D₁, hD₁, D₂, hD₂, hd, hu⟩ := hH.2.2.2.2 C.1 C.2 h2
    have hchild : Finset.univ.filter (fun w : Option {C // C ∈ H} => w ≠ none ∧
        hierPar hH w = some C) = {some ⟨D₁, hD₁⟩, some ⟨D₂, hD₂⟩} := by
      ext w
      rcases w with _ | D
      · simp
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, reduceCtorEq,
          not_false_eq_true, hierPar_some_eq_some, Finset.mem_insert, Finset.mem_singleton,
          Option.some.injEq]
        rw [isChild_iff_split hH C.2 hD₁ hD₂ hd hu D.2]
        constructor
        · rintro (h | h)
          · exact Or.inl (Subtype.ext h)
          · exact Or.inr (Subtype.ext h)
        · rintro (h | h)
          · exact Or.inl (by rw [h])
          · exact Or.inr (by rw [h])
    rw [hchild]
    have hdep : ∀ (D : {C // C ∈ H}), hierPar hH (some D) = some C →
        hierDepth H (some D) = hierDepth H (some C) + 1 := by
      intro D hD
      have := hierDepth_par hH (some D) (Option.some_ne_none D)
      rw [hD] at this
      omega
    have hpd := hierDepth_par hH (some C) (Option.some_ne_none C)
    have hc₁ : hierPar hH (some ⟨D₁, hD₁⟩) = some C := (hierPar_some_eq_some hH _ _).mpr
      ((isChild_iff_split hH C.2 hD₁ hD₂ hd hu hD₁).mpr (Or.inl rfl))
    have hc₂ : hierPar hH (some ⟨D₂, hD₂⟩) = some C := (hierPar_some_eq_some hH _ _).mpr
      ((isChild_iff_split hH C.2 hD₁ hD₂ hd hu hD₂).mpr (Or.inr rfl))
    have h₁ := hdep _ hc₁
    have h₂ := hdep _ hc₂
    have hD12 : (some ⟨D₁, hD₁⟩ : Option {C // C ∈ H}) ≠ some ⟨D₂, hD₂⟩ := by
      intro he
      simp only [Option.some.injEq, Subtype.mk.injEq] at he
      subst he
      obtain ⟨y, hy⟩ := (hH.2.1 D₁ hD₁).1
      exact Finset.disjoint_left.mp hd hy hy
    rw [Finset.singleton_union, Finset.card_insert_of_notMem, Finset.card_pair hD12]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · intro he; rw [he] at hpd; omega
    · intro he; rw [he] at hpd; omega



private theorem hier_adj_child {X : Type} [DecidableEq X] {S : Finset X}
    {H : Finset (Finset X)} (hH : IsBinaryHierarchy S H) {v c : Option {C // C ∈ H}}
    (hadj : (parGraph none (hierPar hH)).Adj v c)
    (hd : hierDepth H c = hierDepth H v + 1) : hierPar hH c = v ∧ c ≠ none := by
  rcases (parGraph_adj (hierDepth_par hH)).mp hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have := hierDepth_par hH v h1; rw [h2] at this; omega
  · exact ⟨h2, h1⟩

private theorem hier_beyond_subset {X : Type} [DecidableEq X] {S : Finset X}
    {H : Finset (Finset X)} (hH : IsBinaryHierarchy S H) :
    ∀ n (C D : {C // C ∈ H}), (parGraph none (hierPar hH)).dist (some C) (some D) = n →
      Beyond (parGraph none (hierPar hH)) none (some C) (some D) → D.1 ⊆ C.1 := by
  have hpar := hierDepth_par hH
  have hG := parGraph_connected hpar
  have hdist := parGraph_dist (rfl : hierDepth H none = 0) hpar
  intro n
  induction n with
  | zero =>
    intro C D hn _
    have := (hG.dist_eq_zero_iff).mp hn
    simp only [Option.some.injEq] at this
    rw [this]
  | succ n ih =>
    intro C D hn hb
    have hne : (some C : Option {C // C ∈ H}) ≠ some D := by
      intro h; rw [h, SimpleGraph.dist_self] at hn; omega
    obtain ⟨c, hc, hdc, hcb⟩ := exists_child_toward hG hb hne
    rw [hdist, hdist] at hdc
    obtain ⟨hpc, hcn⟩ := hier_adj_child hH hc hdc
    obtain ⟨E, rfl⟩ := Option.ne_none_iff_exists'.mp hcn
    have hEC := (hierPar_some_eq_some hH C E).mp hpc
    have hn' : (parGraph none (hierPar hH)).dist (some E) (some D) = n := by
      unfold Beyond at hb hcb
      rw [hdist, hdist] at hb hcb
      omega
    exact (ih E D hn' hcb).trans hEC.1.1

private theorem hier_subset_beyond {X : Type} [DecidableEq X] {S : Finset X}
    {H : Finset (Finset X)} (hH : IsBinaryHierarchy S H) :
    ∀ n (C D : {C // C ∈ H}), C.1.card - D.1.card = n → D.1 ⊆ C.1 →
      Beyond (parGraph none (hierPar hH)) none (some C) (some D) := by
  have hpar := hierDepth_par hH
  have hG := parGraph_connected hpar
  have hdist := parGraph_dist (rfl : hierDepth H none = 0) hpar
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro C D hn hDC
  by_cases hCD : D = C
  · rw [hCD]; exact beyond_self _ _ _
  have hlt : D.1 ⊂ C.1 :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hDC, fun h => hCD (Subtype.ext h)⟩
  have hDS : D.1 ≠ S := fun h => absurd (hlt.trans_le ((hH.2.1 C.1 C.2).2)) (h ▸ lt_irrefl _)
  obtain ⟨hPm, hPc⟩ := parentSet_spec hH D.2 hDS
  set P : {C // C ∈ H} := ⟨parentSet H D.1, hPm⟩
  have hPC : P.1 ⊆ C.1 := hPc.2 C.1 C.2 hlt
  have hcard : C.1.card - P.1.card < n := by
    have : D.1.card < P.1.card := Finset.card_lt_card hPc.1
    have := Finset.card_le_card hPC
    omega
  have h1 := ih _ hcard C P rfl hPC
  have hpd : hierPar hH (some D) = some P := (hierPar_some_eq_some hH P D).mpr hPc
  have hadj : (parGraph none (hierPar hH)).Adj (some P) (some D) :=
    (parGraph_adj hpar).mpr (Or.inr ⟨Option.some_ne_none D, hpd⟩)
  have h2 : Beyond (parGraph none (hierPar hH)) none (some P) (some D) := by
    unfold Beyond
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hadj, hdist, hdist]
    have := hpar (some D) (Option.some_ne_none D)
    rw [hpd] at this
    omega
  exact beyond_trans hG h1 h2

/-- Every binary hierarchy on the taxa other than `a` is the cluster set, seen from the leaf
`a`, of some unrooted binary phylogenetic tree (vertices: the leaf `a` and the members of the
hierarchy; each member is joined to the smallest member strictly containing it). -/
theorem exists_clusterSet_eq {X : Type} [Fintype X] [DecidableEq X] (a : X)
    (H : Finset (Finset X)) (hH : IsBinaryHierarchy (Finset.univ.erase a) H) :
    ∃ T : UnrootedBinaryTree X, clusterSet T a = H := by
  classical
  have hpar := hierDepth_par hH
  have hsing : ∀ x, x ≠ a → ({x} : Finset X) ∈ H := fun x hx =>
    hH.2.2.1 x (Finset.mem_erase.mpr ⟨hx, Finset.mem_univ x⟩)
  let G := parGraph none (hierPar hH)
  let g : X → {v // G.degree v = 1} := fun x =>
    if hx : x = a then ⟨none, hier_degree_none hH⟩
    else ⟨some ⟨{x}, hsing x hx⟩, by rw [hier_degree_some]; simp⟩
  have hg : Function.Bijective g := by
    constructor
    · intro x y hxy
      by_cases hx : x = a <;> by_cases hy : y = a
      · rw [hx, hy]
      · simp [g, hx, hy] at hxy
      · simp [g, hx, hy] at hxy
      · simpa [g, hx, hy] using hxy
    · rintro ⟨v, hv⟩
      rcases v with _ | C
      · exact ⟨a, by simp [g]⟩
      · rw [hier_degree_some] at hv
        have h1 : C.1.card = 1 := by
          by_contra h; simp only [h, ↓reduceIte] at hv; omega
        obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h1
        have hxa : x ≠ a := by
          have := (hH.2.1 C.1 C.2).2 (hx ▸ Finset.mem_singleton_self x)
          exact Finset.ne_of_mem_erase this
        refine ⟨x, ?_⟩
        simp only [g, hxa, dite_false, Subtype.mk.injEq, Option.some.injEq]
        exact Subtype.ext hx.symm
  let T : UnrootedBinaryTree X :=
    { V := Option {C // C ∈ H}
      G := G
      isTree := parGraph_isTree hpar
      label := Equiv.ofBijective g hg
      degree_eq_three := by
        intro v hv
        rcases v with _ | C
        · exact absurd (hier_degree_none hH) hv
        · rw [hier_degree_some] at hv ⊢
          split_ifs at hv ⊢ with h
          · exact absurd rfl hv
          · rfl }
  have hla : (T.label a : T.V) = none := by simp [T, g]
  have hlx : ∀ x (hx : x ≠ a), (T.label x : T.V) = some ⟨{x}, hsing x hx⟩ := by
    intro x hx; simp [T, g, hx]
  have hdist := parGraph_dist (rfl : hierDepth H none = 0) hpar
  have hcl : ∀ C : {C // C ∈ H}, cluster T a (some C) = C.1 := by
    intro C
    ext x
    rw [cluster_mem]
    constructor
    · rintro ⟨hx, hb⟩
      rw [hla, hlx x hx] at hb
      exact hier_beyond_subset hH _ C ⟨{x}, hsing x hx⟩ rfl hb (Finset.mem_singleton_self x)
    · intro hxC
      have hx : x ≠ a := Finset.ne_of_mem_erase ((hH.2.1 C.1 C.2).2 hxC)
      refine ⟨hx, ?_⟩
      rw [hla, hlx x hx]
      exact hier_subset_beyond hH _ C ⟨{x}, hsing x hx⟩ rfl
        (Finset.singleton_subset_iff.mpr hxC)
  refine ⟨T, ?_⟩
  ext C
  simp only [clusterSet, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨v, rfl⟩
    rcases v with _ | D
    · have := cluster_root T a
      rw [hla] at this
      rw [this]
      exact hH.1
    · rw [hcl]; exact D.2
  · intro hC
    exact ⟨some ⟨C, hC⟩, hcl ⟨C, hC⟩⟩

/-! ### The count -/

/-- Unrooted binary phylogenetic trees up to label-preserving isomorphism correspond to the
binary hierarchies on the taxa other than `a`, by their clusters seen from the leaf `a`. -/
noncomputable def quotEquivHierarchy {X : Type} [Fintype X] [DecidableEq X] (a : X) :
    Quot (UnrootedBinaryTree.Iso (X := X)) ≃
      {H : Finset (Finset X) // IsBinaryHierarchy (Finset.univ.erase a) H} := by
  refine Equiv.ofBijective
    (Quot.lift (fun T => ⟨clusterSet T a, isBinaryHierarchy_clusterSet T a⟩)
      fun T T' h => Subtype.ext (clusterSet_eq_of_iso h a)) ⟨?_, ?_⟩
  · intro p q hpq
    induction p using Quot.ind with
    | mk T =>
    induction q using Quot.ind with
    | mk T' =>
    exact Quot.sound (iso_of_clusterSet_eq a (congrArg Subtype.val hpq))
  · rintro ⟨H, hH⟩
    obtain ⟨T, hT⟩ := exists_clusterSet_eq a H hH
    exact ⟨Quot.mk _ T, Subtype.ext hT⟩

/-- The count `(2 n - 5)‼` of unrooted binary phylogenetic trees holds from `n = 2` taxa on:
for `n = 2` the single tree is one edge and `2 · 2 - 5 = 0` in `ℕ`, `0‼ = 1` (the conventional
value `(-1)‼ = 1`). For `n ≤ 1` there is no tree while the formula gives `1`. -/
theorem nat_card_unrootedBinaryTree_of_two_le (n : ℕ) (hn : 2 ≤ n) :
    Nat.card (Quot (UnrootedBinaryTree.Iso (X := Fin n))) = (2 * n - 5)‼ := by
  rw [Nat.card_congr (quotEquivHierarchy (⟨0, by omega⟩ : Fin n)),
    nat_card_binaryHierarchy _ ⟨⟨1, by omega⟩, by simp [Fin.ext_iff]⟩]
  congr 1
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  omega

/-- **The number of unrooted binary phylogenetic trees.** On `n ≥ 3` labeled taxa there are
`(2 n - 5)‼ = 1 · 3 ⋯ (2 n - 5)` unrooted binary phylogenetic trees up to label-preserving
isomorphism.

Source: Semple & Steel (2003), Proposition 2.1.4.
Proves the deferred entry `nat_card_unrootedBinaryTree`. -/
theorem nat_card_unrootedBinaryTree (n : ℕ) (hn : 3 ≤ n) :
    Nat.card (Quot (UnrootedBinaryTree.Iso (X := Fin n))) = (2 * n - 5)‼ :=
  nat_card_unrootedBinaryTree_of_two_le n (by omega)

end MathlibExt.Biology.Phylogenetics.UnrootedTreeCount
