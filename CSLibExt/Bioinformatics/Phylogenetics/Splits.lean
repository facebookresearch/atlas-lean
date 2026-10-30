/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Phylogenetics.UnrootedTreeCount
public import MathlibExt.Biology.Phylogenetics.Buneman
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.SymmDiff
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Splits, compatibility, Robinson–Foulds, ultrametrics, UPGMA and BUILD

A *split* `A | Aᶜ` of a finite set of taxa `X` is a bipartition, stored here by one side
`A : Finset X`. Two splits are *compatible* (`Compatible`) when one of the four intersections
`A ∩ B`, `A ∩ Bᶜ`, `Aᶜ ∩ B`, `Aᶜ ∩ Bᶜ` is empty. For a binary character `χ : X → Bool` the
split is `{x | χ x = true}`, and two characters give compatible splits exactly when they do not
show all four *gametes* `(0,0), (0,1), (1,0), (1,1)` (`compatible_iff_not_fourGametes`).

Rooting at a taxon `a` turns splits into *clusters*: the side of a split not containing `a`.
Two such sides are compatible iff they are nested or disjoint
(`compatible_iff_nested_or_disjoint`). The merged file `UnrootedTreeCount` shows that the
clusters `clusterSet T a` of an unrooted binary phylogenetic tree `T` seen from the leaf `a`
form a binary hierarchy and determine `T`, and that every binary hierarchy arises. The splits
of `T` are the sides of its edges (`edgeSplits T`); they are both sides of every cluster seen
from any leaf (`splitSet_eq_edgeSplits`), which transfers the hierarchy results to splits.

## Main results

* `splitSet_eq_edgeSplits`: the clusters seen from any leaf, with their complements, are
  exactly the edge splits of the tree.
* `exists_isBinaryHierarchy_superset`: every family of pairwise nested-or-disjoint nonempty
  subsets of `S` is contained in a binary hierarchy on `S` (every hierarchy is refined by a
  rooted binary tree); `isHierarchy_completion`: adding `S` and the singletons to such a family
  gives a hierarchy.
* `splits_equivalence`: **the splits-equivalence theorem** (Buneman 1971; Semple & Steel
  2003, Theorem 3.1.4) in its binary form: a family of splits is displayed by one unrooted
  binary phylogenetic tree iff its members are pairwise compatible.
* `exists_perfectPhylogeny_iff`: **the four-gamete test** (Estabrook, Johnson & McMorris 1976):
  a binary character matrix has a perfect phylogeny iff no two columns show all four gametes.
* `rfDist_self`, `rfDist_comm`, `rfDist_triangle`, `rfDist_eq_zero_iff`, `rfDist_le`: the
  **Robinson–Foulds distance** is a metric on unrooted binary trees up to isomorphism, at most
  `2 (n - 3)` on `n ≥ 3` taxa (Robinson & Foulds 1981); `two_mul_rfDist`: it is half the size
  of the symmetric difference of the split sets.
* `nested_or_disjoint_of_mem_majoritySplits`, `exists_tree_majoritySplits_subset`:
  **majority-rule consensus** (Margush & McMorris 1981): splits in more than half of the trees
  are pairwise compatible, hence displayed by one tree; `bootstrapSupport` is the frequency of
  a split over all site resamplings with replacement (Felsenstein 1985) and
  `one_half_lt_bootstrapSupport_iff` relates it to the majority rule.
* `isUltrametric_iff_isDatedTreeMetric`: a dissimilarity is an **ultrametric** (three-point
  condition) iff it is the metric of a dated rooted tree (Semple & Steel 2003, Theorem 7.2.5);
  `IsUltrametric.isTreeMetric`: ultrametrics satisfy the four-point condition, hence are tree
  metrics (Buneman's theorem, merged in `Buneman`).
* `upgma_exact`: **UPGMA is exact on ultrametrics** (Sokal & Michener 1958): every run of the
  average-linkage merges assigns to two taxa joined in one block exactly their distance.
* `eq_of_displaysTriplet_iff`, `iso_of_displaysQuartet_iff`: a binary tree is determined by its
  rooted triplets, and an unrooted binary tree by its quartets.
* `build_spec`: **correctness of BUILD** (Aho, Sagiv, Szymanski & Ullman 1981): a set of rooted
  triplets is displayed by a rooted binary tree iff on every subset of at least two taxa the Aho
  graph has a cut (is disconnected).

## Not covered

Running times (Gusfield's `O(nm)` perfect-phylogeny algorithm, linear-time Robinson–Foulds,
polynomial-time BUILD) and the bijection between non-binary hierarchies and non-binary trees:
the trees here are binary, so "displayed by a tree" means "displayed by a binary refinement".

## References

* P. Buneman, *The recovery of trees from measures of dissimilarity*, in Mathematics in the
  Archaeological and Historical Sciences, Edinburgh University Press, 1971, 387–395.
* G. F. Estabrook, C. S. Johnson Jr. and F. R. McMorris, *A mathematical foundation for the
  analysis of cladistic character compatibility*, Math. Biosci. 29 (1976), 181–187.
* D. F. Robinson and L. R. Foulds, *Comparison of phylogenetic trees*, Math. Biosci. 53 (1981),
  131–147.
* T. Margush and F. R. McMorris, *Consensus n-trees*, Bull. Math. Biol. 43 (1981), 239–244.
* J. Felsenstein, *Confidence limits on phylogenies: an approach using the bootstrap*,
  Evolution 39 (1985), 783–791.
* R. R. Sokal and C. D. Michener, *A statistical method for evaluating systematic
  relationships*, Univ. Kansas Sci. Bull. 38 (1958), 1409–1438.
* A. V. Aho, Y. Sagiv, T. G. Szymanski and J. D. Ullman, *Inferring a tree from lowest common
  ancestors with an application to the optimization of relational expressions*, SIAM J.
  Comput. 10 (1981), 405–421.
* C. Semple and M. Steel, *Phylogenetics*, Oxford University Press, 2003, chapters 3, 6, 7.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Bioinformatics.Phylogenetics.Splits

open MathlibExt.Biology.Phylogenetics.UnrootedTreeCount
open scoped symmDiff

/-! ### Hierarchies -/

section Hierarchy

variable {α : Type*} [DecidableEq α]

/-- A **hierarchy** on a finite set `S`: a family of nonempty subsets of `S` containing `S` and
every singleton, any two members nested or disjoint. These are the cluster systems of the rooted
phylogenetic trees on `S` (Semple & Steel 2003, Section 3.5). -/
def IsHierarchy (S : Finset α) (H : Finset (Finset α)) : Prop :=
  S ∈ H ∧ (∀ C ∈ H, C.Nonempty ∧ C ⊆ S) ∧ (∀ x ∈ S, {x} ∈ H) ∧
    ∀ C ∈ H, ∀ D ∈ H, C ⊆ D ∨ D ⊆ C ∨ Disjoint C D

/-- A binary hierarchy is a hierarchy. -/
theorem IsBinaryHierarchy.isHierarchy {S : Finset α} {H : Finset (Finset α)}
    (h : IsBinaryHierarchy S H) : IsHierarchy S H :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- **Pairwise nested-or-disjoint clusters form a hierarchy**: adding `S` and the singletons to
a family of pairwise nested-or-disjoint nonempty subsets of a nonempty `S` gives a hierarchy. -/
theorem isHierarchy_completion {S : Finset α} (hS : S.Nonempty) {F : Finset (Finset α)}
    (hF : ∀ C ∈ F, C.Nonempty ∧ C ⊆ S)
    (hlam : ∀ C ∈ F, ∀ D ∈ F, C ⊆ D ∨ D ⊆ C ∨ Disjoint C D) :
    IsHierarchy S (insert S (F ∪ S.image ({·}))) := by
  refine ⟨Finset.mem_insert_self _ _, ?_, ?_, ?_⟩
  · intro C hC
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hC
    rcases hC with rfl | hC | ⟨x, hx, rfl⟩
    · exact ⟨hS, le_rfl⟩
    · exact hF C hC
    · exact ⟨Finset.singleton_nonempty x, Finset.singleton_subset_iff.mpr hx⟩
  · intro x hx
    exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hx))
  · have hsub : ∀ C ∈ insert S (F ∪ S.image ({·})), C ⊆ S := by
      intro C hC
      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hC
      rcases hC with rfl | hC | ⟨x, hx, rfl⟩
      · exact le_rfl
      · exact (hF C hC).2
      · exact Finset.singleton_subset_iff.mpr hx
    have hsing : ∀ x : α, ∀ D : Finset α, {x} ⊆ D ∨ D ⊆ {x} ∨ Disjoint {x} D ∨
        D = ∅ := by
      intro x D
      by_cases hx : x ∈ D
      · exact Or.inl (Finset.singleton_subset_iff.mpr hx)
      · exact Or.inr (Or.inr (Or.inl (Finset.disjoint_singleton_left.mpr hx)))
    intro C hC D hD
    have hCS := hsub C hC
    have hDS := hsub D hD
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hC hD
    rcases hC with rfl | hC | ⟨x, hx, rfl⟩
    · exact Or.inr (Or.inl hDS)
    · rcases hD with rfl | hD | ⟨y, hy, rfl⟩
      · exact Or.inl hCS
      · exact hlam C hC D hD
      · rcases hsing y C with h | h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h.symm)
        · exact absurd h (hF C hC).1.ne_empty
    · rcases hD with rfl | hD | ⟨y, hy, rfl⟩
      · exact Or.inl hCS
      · rcases hsing x D with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
        · exact absurd h (hF D hD).1.ne_empty
      · rcases hsing x {y} with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
        · exact absurd h (Finset.singleton_ne_empty y)

/-- Two binary hierarchies on the parts of a bipartition of `S`, together with `S`, form a
binary hierarchy on `S`. -/
private theorem isBinaryHierarchy_combine {S D₁ D₂ : Finset α} {H₁ H₂ : Finset (Finset α)}
    (h₁ : IsBinaryHierarchy D₁ H₁) (h₂ : IsBinaryHierarchy D₂ H₂) (hd : Disjoint D₁ D₂)
    (hu : D₁ ∪ D₂ = S) : IsBinaryHierarchy S (insert S (H₁ ∪ H₂)) := by
  obtain ⟨hS₁, hsub₁, hsing₁, hlam₁, hsplit₁⟩ := h₁
  obtain ⟨hS₂, hsub₂, hsing₂, hlam₂, hsplit₂⟩ := h₂
  have hsub : ∀ C ∈ H₁ ∪ H₂, C.Nonempty ∧ C ⊆ S := by
    intro C hC
    rcases Finset.mem_union.mp hC with hC | hC
    · exact ⟨(hsub₁ C hC).1, (hsub₁ C hC).2.trans (hu ▸ Finset.subset_union_left)⟩
    · exact ⟨(hsub₂ C hC).1, (hsub₂ C hC).2.trans (hu ▸ Finset.subset_union_right)⟩
  refine ⟨Finset.mem_insert_self _ _, ?_, ?_, ?_, ?_⟩
  · intro C hC
    rcases Finset.mem_insert.mp hC with rfl | hC
    · exact ⟨(hsub₁ D₁ hS₁).1.mono (hu ▸ Finset.subset_union_left), le_rfl⟩
    · exact hsub C hC
  · intro x hx
    rw [← hu, Finset.mem_union] at hx
    rcases hx with hx | hx
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (hsing₁ x hx))
    · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (hsing₂ x hx))
  · intro C hC D hD
    rcases Finset.mem_insert.mp hC with hCS | hC'
    · rcases Finset.mem_insert.mp hD with hDS | hD'
      · exact Or.inl (by rw [hCS, hDS])
      · exact Or.inr (Or.inl (hCS ▸ (hsub D hD').2))
    rcases Finset.mem_insert.mp hD with hDS | hD'
    · exact Or.inl (hDS ▸ (hsub C hC').2)
    rcases Finset.mem_union.mp hC' with hC | hC <;> rcases Finset.mem_union.mp hD' with hD | hD
    · exact hlam₁ C hC D hD
    · exact Or.inr (Or.inr (hd.mono (hsub₁ C hC).2 (hsub₂ D hD).2))
    · exact Or.inr (Or.inr (hd.symm.mono (hsub₂ C hC).2 (hsub₁ D hD).2))
    · exact hlam₂ C hC D hD
  · intro C hC hc
    rcases Finset.mem_insert.mp hC with rfl | hC
    · exact ⟨D₁, Finset.mem_insert_of_mem (Finset.mem_union_left _ hS₁), D₂,
        Finset.mem_insert_of_mem (Finset.mem_union_right _ hS₂), hd, hu⟩
    rcases Finset.mem_union.mp hC with hC | hC
    · obtain ⟨E₁, hE₁, E₂, hE₂, hd', hu'⟩ := hsplit₁ C hC hc
      exact ⟨E₁, Finset.mem_insert_of_mem (Finset.mem_union_left _ hE₁), E₂,
        Finset.mem_insert_of_mem (Finset.mem_union_left _ hE₂), hd', hu'⟩
    · obtain ⟨E₁, hE₁, E₂, hE₂, hd', hu'⟩ := hsplit₂ C hC hc
      exact ⟨E₁, Finset.mem_insert_of_mem (Finset.mem_union_right _ hE₁), E₂,
        Finset.mem_insert_of_mem (Finset.mem_union_right _ hE₂), hd', hu'⟩

/-- The members of a binary hierarchy inside one of its members form a binary hierarchy (the
private `isBinaryHierarchy_filter` of `UnrootedTreeCount`, restated here). -/
private theorem isBinaryHierarchy_filter {S D : Finset α} {H : Finset (Finset α)}
    (hH : IsBinaryHierarchy S H) (hD : D ∈ H) : IsBinaryHierarchy D (H.filter (· ⊆ D)) := by
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

/-- The only binary hierarchy on a singleton. -/
private theorem isBinaryHierarchy_singleton (a : α) :
    IsBinaryHierarchy {a} {{a}} := by
  refine ⟨Finset.mem_singleton_self _, ?_, ?_, ?_, ?_⟩
  · intro C hC
    rw [Finset.mem_singleton] at hC
    exact ⟨hC ▸ Finset.singleton_nonempty a, hC ▸ le_rfl⟩
  · intro x hx
    rw [Finset.mem_singleton] at hx
    rw [hx]; exact Finset.mem_singleton_self _
  · intro C hC D hD
    rw [Finset.mem_singleton] at hC hD
    exact Or.inl (by rw [hC, hD])
  · intro C hC hc
    rw [Finset.mem_singleton] at hC
    rw [hC, Finset.card_singleton] at hc
    exact absurd hc (lt_irrefl _)

/-- A family of pairwise nested-or-disjoint proper nonempty subsets of `S`, with `|S| ≥ 2`, is
compatible with some bipartition of `S` into nonempty parts. -/
private theorem exists_bipartition {S : Finset α} (hS : 1 < S.card) {F : Finset (Finset α)}
    (hF : ∀ C ∈ F, C.Nonempty ∧ C ⊆ S)
    (hlam : ∀ C ∈ F, ∀ D ∈ F, C ⊆ D ∨ D ⊆ C ∨ Disjoint C D) :
    ∃ D₁ D₂ : Finset α, D₁.Nonempty ∧ D₂.Nonempty ∧ Disjoint D₁ D₂ ∧ D₁ ∪ D₂ = S ∧
      ∀ C ∈ F, C ≠ S → C ⊆ D₁ ∨ C ⊆ D₂ := by
  by_cases hF' : (F.filter (· ≠ S)).Nonempty
  · obtain ⟨M, hM, hmax⟩ := Finset.exists_max_image _ Finset.card hF'
    rw [Finset.mem_filter] at hM
    have hMS := (hF M hM.1).2
    refine ⟨M, S \ M, (hF M hM.1).1, ?_, Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hMS,
      ?_⟩
    · rw [Finset.sdiff_nonempty]
      exact fun h => hM.2 (le_antisymm hMS h)
    · intro C hC hCS
      rcases hlam C hC M hM.1 with h | h | h
      · exact Or.inl h
      · by_cases hCM : C = M
        · exact Or.inl hCM.le
        · have := hmax C (Finset.mem_filter.mpr ⟨hC, hCS⟩)
          have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨h, Ne.symm hCM⟩)
          omega
      · exact Or.inr (Finset.subset_sdiff.mpr ⟨(hF C hC).2, h⟩)
  · obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
    refine ⟨{x}, S.erase x, Finset.singleton_nonempty x, ?_, ?_, ?_, ?_⟩
    · rw [← Finset.card_pos, Finset.card_erase_of_mem hx]
      omega
    · exact Finset.disjoint_singleton_left.mpr (Finset.notMem_erase x S)
    · rw [← Finset.insert_eq, Finset.insert_erase hx]
    · intro C hC hCS
      exact absurd ⟨C, Finset.mem_filter.mpr ⟨hC, hCS⟩⟩ hF'

/-- **Hierarchies are refined by binary trees**: every family of pairwise nested-or-disjoint
nonempty subsets of a nonempty `S` is contained in a binary hierarchy on `S`, the cluster set of
a rooted binary phylogenetic tree on `S` (Semple & Steel 2003, Proposition 3.5.2 and the
refinement of a rooted tree to a binary one). -/
theorem exists_isBinaryHierarchy_superset {S : Finset α} (hS : S.Nonempty)
    {F : Finset (Finset α)} (hF : ∀ C ∈ F, C.Nonempty ∧ C ⊆ S)
    (hlam : ∀ C ∈ F, ∀ D ∈ F, C ⊆ D ∨ D ⊆ C ∨ Disjoint C D) :
    ∃ H, IsBinaryHierarchy S H ∧ F ⊆ H := by
  suffices ∀ n (S : Finset α) (F : Finset (Finset α)), S.card = n → S.Nonempty →
      (∀ C ∈ F, C.Nonempty ∧ C ⊆ S) → (∀ C ∈ F, ∀ D ∈ F, C ⊆ D ∨ D ⊆ C ∨ Disjoint C D) →
      ∃ H, IsBinaryHierarchy S H ∧ F ⊆ H from this _ S F rfl hS hF hlam
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S F hn hS hF hlam
  by_cases h1 : 1 < S.card
  · obtain ⟨D₁, D₂, hne₁, hne₂, hd, hu, hcov⟩ := exists_bipartition h1 hF hlam
    have hc₁ : D₁.card < n := by
      rw [← hn, ← hu, Finset.card_union_of_disjoint hd]
      have := hne₂.card_pos; omega
    have hc₂ : D₂.card < n := by
      rw [← hn, ← hu, Finset.card_union_of_disjoint hd]
      have := hne₁.card_pos; omega
    have sub : ∀ D : Finset α, ∀ C ∈ F.filter (· ⊆ D), C.Nonempty ∧ C ⊆ D := fun D C hC =>
      ⟨(hF C (Finset.mem_filter.mp hC).1).1, (Finset.mem_filter.mp hC).2⟩
    have lam : ∀ D : Finset α, ∀ C ∈ F.filter (· ⊆ D), ∀ E ∈ F.filter (· ⊆ D),
        C ⊆ E ∨ E ⊆ C ∨ Disjoint C E := fun D C hC E hE =>
      hlam C (Finset.mem_filter.mp hC).1 E (Finset.mem_filter.mp hE).1
    obtain ⟨H₁, hH₁, hF₁⟩ := ih _ hc₁ D₁ _ rfl hne₁ (sub D₁) (lam D₁)
    obtain ⟨H₂, hH₂, hF₂⟩ := ih _ hc₂ D₂ _ rfl hne₂ (sub D₂) (lam D₂)
    refine ⟨insert S (H₁ ∪ H₂), isBinaryHierarchy_combine hH₁ hH₂ hd hu, fun C hC => ?_⟩
    by_cases hCS : C = S
    · exact hCS ▸ Finset.mem_insert_self _ _
    rcases hcov C hC hCS with h | h
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _
        (hF₁ (Finset.mem_filter.mpr ⟨hC, h⟩)))
    · exact Finset.mem_insert_of_mem (Finset.mem_union_right _
        (hF₂ (Finset.mem_filter.mpr ⟨hC, h⟩)))
  · obtain ⟨a, rfl⟩ : ∃ a, S = {a} := by
      rw [← Finset.card_eq_one]
      have := hS.card_pos; omega
    refine ⟨{{a}}, isBinaryHierarchy_singleton a, fun C hC => ?_⟩
    rw [Finset.mem_singleton]
    exact (Finset.Nonempty.subset_singleton_iff (hF C hC).1).mp (hF C hC).2

/-- A binary hierarchy on `S` has `2 |S| - 1` members: the `|S|` singletons and `|S| - 1`
internal clusters (stated without subtraction). -/
theorem IsBinaryHierarchy.card_add_one {S : Finset α} {H : Finset (Finset α)}
    (h : IsBinaryHierarchy S H) : H.card + 1 = 2 * S.card := by
  suffices ∀ n (S : Finset α) (H : Finset (Finset α)), S.card = n → IsBinaryHierarchy S H →
      H.card + 1 = 2 * S.card from this _ S H rfl h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S H hn hH
  have hH' := hH
  obtain ⟨hS, hsub, hsing, hlam, hsplit⟩ := hH
  by_cases h1 : 1 < S.card
  · obtain ⟨D₁, h₁, D₂, h₂, hd, hu⟩ := hsplit S hS h1
    have hne₁ := (hsub D₁ h₁).1
    have hne₂ := (hsub D₂ h₂).1
    have hcu : S.card = D₁.card + D₂.card := by rw [← hu, Finset.card_union_of_disjoint hd]
    have e₁ := ih _ (by have := hne₂.card_pos; omega) D₁ _ rfl (isBinaryHierarchy_filter hH' h₁)
    have e₂ := ih _ (by have := hne₁.card_pos; omega) D₂ _ rfl (isBinaryHierarchy_filter hH' h₂)
    have hleft : ∀ {C A B : Finset α}, C ⊆ A ∪ B → Disjoint C B → C ⊆ A := fun hC hd y hy =>
      (Finset.mem_union.mp (hC hy)).resolve_right (Finset.disjoint_left.mp hd hy)
    have hdecomp : H = insert S (H.filter (· ⊆ D₁) ∪ H.filter (· ⊆ D₂)) := by
      ext C
      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hC
        by_cases hCS : C = S
        · exact Or.inl hCS
        right
        have hCS' : C ⊆ D₁ ∪ D₂ := hu ▸ (hsub C hC).2
        rcases hlam C hC D₁ h₁ with h | h | h
        · exact Or.inl ⟨hC, h⟩
        · rcases hlam C hC D₂ h₂ with h' | h' | h'
          · obtain ⟨y, hy⟩ := hne₁
            exact absurd (h' (h hy)) (Finset.disjoint_left.mp hd hy)
          · exact absurd (le_antisymm (hsub C hC).2 (hu ▸ Finset.union_subset h h')) hCS
          · exact Or.inl ⟨hC, hleft hCS' h'⟩
        · exact Or.inr ⟨hC, hleft (Finset.union_comm D₁ D₂ ▸ hCS') h⟩
      · rintro (rfl | h | h)
        · exact hS
        · exact h.1
        · exact h.1
    have hdis : Disjoint (H.filter (· ⊆ D₁)) (H.filter (· ⊆ D₂)) := by
      rw [Finset.disjoint_left]
      intro C hC hC'
      obtain ⟨y, hy⟩ := (hsub C (Finset.mem_filter.mp hC).1).1
      exact Finset.disjoint_left.mp hd ((Finset.mem_filter.mp hC).2 hy)
        ((Finset.mem_filter.mp hC').2 hy)
    have hnot : S ∉ H.filter (· ⊆ D₁) ∪ H.filter (· ⊆ D₂) := by
      intro hm
      rcases Finset.mem_union.mp hm with hm | hm
      · obtain ⟨y, hy⟩ := hne₂
        exact Finset.disjoint_left.mp hd ((Finset.mem_filter.mp hm).2
          (hu ▸ Finset.mem_union_right _ hy)) hy
      · obtain ⟨y, hy⟩ := hne₁
        exact Finset.disjoint_left.mp hd hy ((Finset.mem_filter.mp hm).2
          (hu ▸ Finset.mem_union_left _ hy))
    have hcard : H.card = (insert S (H.filter (· ⊆ D₁) ∪ H.filter (· ⊆ D₂))).card :=
      congrArg Finset.card hdecomp
    rw [hcard, Finset.card_insert_of_notMem hnot, Finset.card_union_of_disjoint hdis]
    omega
  · obtain ⟨a, rfl⟩ : ∃ a, S = {a} := by
      rw [← Finset.card_eq_one]
      have := (hsub S hS).1.card_pos; omega
    have : H = {{a}} := by
      ext C
      rw [Finset.mem_singleton]
      constructor
      · intro hC
        exact (Finset.Nonempty.subset_singleton_iff (hsub C hC).1).mp (hsub C hC).2
      · rintro rfl; exact hS
    rw [this]
    simp

end Hierarchy

/-! ### Splits and compatibility -/

section Compatibility

variable {X : Type} [Fintype X] [DecidableEq X]

/-- The splits `A | Aᶜ` and `B | Bᶜ` are **compatible**: one of `A ∩ B`, `A ∩ Bᶜ`, `Aᶜ ∩ B`,
`Aᶜ ∩ Bᶜ` is empty (Semple & Steel 2003, Section 3.1). -/
def Compatible (A B : Finset X) : Prop :=
  Disjoint A B ∨ Disjoint A Bᶜ ∨ Disjoint Aᶜ B ∨ Disjoint Aᶜ Bᶜ

/-- Compatibility is symmetric. -/
theorem Compatible.symm {A B : Finset X} (h : Compatible A B) : Compatible B A := by
  unfold Compatible at *
  rcases h with h | h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr (Or.inl h.symm))
  · exact Or.inr (Or.inl h.symm)
  · exact Or.inr (Or.inr (Or.inr h.symm))

/-- Compatibility depends only on the split, not on the side used to store it. -/
theorem compatible_compl_left {A B : Finset X} : Compatible Aᶜ B ↔ Compatible A B := by
  unfold Compatible
  rw [compl_compl]
  tauto

/-- Compatibility depends only on the split, not on the side used to store it. -/
theorem compatible_compl_right {A B : Finset X} : Compatible A Bᶜ ↔ Compatible A B := by
  unfold Compatible
  rw [compl_compl]
  tauto

/-- For the sides not containing a fixed taxon `a`, compatibility is being nested or disjoint:
splits seen from a root are clusters. -/
theorem compatible_iff_nested_or_disjoint {a : X} {A B : Finset X} (hA : a ∉ A) (hB : a ∉ B) :
    Compatible A B ↔ A ⊆ B ∨ B ⊆ A ∨ Disjoint A B := by
  have h4 : ¬ Disjoint Aᶜ Bᶜ := fun h =>
    Finset.disjoint_left.mp h (Finset.mem_compl.mpr hA) (Finset.mem_compl.mpr hB)
  unfold Compatible
  rw [disjoint_compl_right_iff, disjoint_compl_left_iff]
  tauto

/-- The binary characters `χ` and `ψ` show **all four gametes** `(0,0), (0,1), (1,0), (1,1)`
on the taxa. -/
def FourGametes (χ ψ : X → Bool) : Prop :=
  ∀ b c : Bool, ∃ x, χ x = b ∧ ψ x = c

/-- The split of a binary character: the taxa in state `true`. -/
def charSplit (χ : X → Bool) : Finset X :=
  Finset.univ.filter fun x => χ x = true

/-- **The four-gamete test**: two binary characters give compatible splits iff they do not
show all four gametes (Buneman 1971; Estabrook, Johnson & McMorris 1976). -/
theorem compatible_iff_not_fourGametes (χ ψ : X → Bool) :
    Compatible (charSplit χ) (charSplit ψ) ↔ ¬ FourGametes χ ψ := by
  have key : ∀ b c : Bool, (∃ x, χ x = b ∧ ψ x = c) ↔
      ¬ Disjoint (if b then charSplit χ else (charSplit χ)ᶜ)
        (if c then charSplit ψ else (charSplit ψ)ᶜ) := by
    intro b c
    rw [Finset.not_disjoint_iff]
    cases b <;> cases c <;> simp [charSplit]
  unfold Compatible FourGametes
  constructor
  · intro h hall
    rcases h with h | h | h | h
    · exact (key true true).mp (hall _ _) (by simpa using h)
    · exact (key true false).mp (hall _ _) (by simpa using h)
    · exact (key false true).mp (hall _ _) (by simpa using h)
    · exact (key false false).mp (hall _ _) (by simpa using h)
  · intro h
    by_contra hc
    apply h
    intro b c
    rw [key]
    cases b <;> cases c <;> simp only [ite_true, ite_false, Bool.false_eq_true] <;> tauto

end Compatibility

/-! ### Splits of unrooted binary trees -/

section Trees

variable {X : Type} [Fintype X] [DecidableEq X]

/-- The split set of `T` computed from the leaf `a`: both sides of every cluster of `T` seen
from `a`. It equals `edgeSplits T` for every `a` (`splitSet_eq_edgeSplits`). -/
noncomputable def splitSet (T : UnrootedBinaryTree X) (a : X) : Finset (Finset X) :=
  clusterSet T a ∪ (clusterSet T a).image (·ᶜ)

/-- The clusters seen from `a` do not contain `a`. -/
theorem notMem_of_mem_clusterSet (T : UnrootedBinaryTree X) (a : X) {C : Finset X}
    (hC : C ∈ clusterSet T a) : a ∉ C := by
  have := ((isBinaryHierarchy_clusterSet T a).2.1 C hC).2
  exact fun h => by simpa using this h

/-- A vertex on a walk splits its length into two parts, each at least a distance. -/
private theorem dist_add_dist_le_length {V : Type} {G : SimpleGraph V} {x y a : V}
    (q : G.Walk x y) (ha : a ∈ q.support) : G.dist x a + G.dist a y ≤ q.length := by
  classical
  have h := congrArg SimpleGraph.Walk.length (q.take_spec ha)
  rw [SimpleGraph.Walk.length_append] at h
  have h1 := SimpleGraph.dist_le (q.takeUntil a ha)
  have h2 := SimpleGraph.dist_le (q.dropUntil a ha)
  omega

/-- Two paths meeting only at the junction concatenate to a path (adapted from the private
`append_path` of `MathlibExt.Biology.Phylogenetics.Buneman`). -/
private theorem isPath_append {V : Type} {G : SimpleGraph V} {u m v : V}
    {p : G.Walk u m} {q : G.Walk m v} (hp : p.IsPath) (hq : q.IsPath)
    (hi : ∀ a ∈ p.support, a ∈ q.support → a = m) : (p.append q).IsPath := by
  apply SimpleGraph.Walk.IsPath.mk'
  rw [SimpleGraph.Walk.support_append]
  apply List.nodup_append.mpr
  refine ⟨hp.support_nodup, hq.support_nodup.tail, ?_⟩
  intro a ha b hb hab
  subst b
  have ham := hi a ha (List.mem_of_mem_tail hb)
  subst a
  have hn := hq.support_nodup
  rw [← q.cons_tail_support, List.nodup_cons] at hn
  exact hn.1 hb

/-- Crossing an edge: in a tree, if `v` is farther than its neighbor `p` from `s` and closer
than `p` to `w`, then `v` lies on the path from `s` to `w`. -/
private theorem dist_add_dist_of_cross {V : Type} {G : SimpleGraph V} (hG : G.IsTree)
    {s w p v : V} (hpv : G.Adj p v) (hs : G.dist s v = G.dist s p + 1)
    (hw : G.dist w p = G.dist w v + 1) : G.dist s v + G.dist v w = G.dist s w := by
  obtain ⟨q₁, hq₁, hl₁⟩ := hG.connected.exists_path_of_dist s p
  obtain ⟨q₂, hq₂, hl₂⟩ := hG.connected.exists_path_of_dist v w
  have hpq₂ : p ∉ q₂.support := by
    intro hm
    have := dist_add_dist_le_length q₂ hm
    have e1 : G.dist p w = G.dist w p := SimpleGraph.dist_comm
    have e2 : G.dist v w = G.dist w v := SimpleGraph.dist_comm
    omega
  have hpath : (q₁.append (SimpleGraph.Walk.cons hpv q₂)).IsPath := by
    refine isPath_append hq₁ (hq₂.cons hpq₂) fun a ha ha' => ?_
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at ha'
    rcases ha' with rfl | ha'
    · rfl
    exfalso
    have h1 := dist_add_dist_le_length q₁ ha
    have h2 := dist_add_dist_le_length q₂ ha'
    have h3 := hG.connected.dist_triangle (u := s) (v := a) (w := v)
    have h4 := hG.connected.dist_triangle (u := w) (v := a) (w := p)
    have e1 : G.dist a v = G.dist v a := SimpleGraph.dist_comm
    have e2 : G.dist w a = G.dist a w := SimpleGraph.dist_comm
    have e3 : G.dist w v = G.dist v w := SimpleGraph.dist_comm
    omega
  obtain ⟨q, hq, hl⟩ := hG.connected.exists_path_of_dist s w
  have := congrArg (fun r : G.Path s w => r.1.length)
    ((hG.isAcyclic.subsingleton_path s w).elim ⟨_, hpath⟩ ⟨q, hq⟩)
  simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons] at this
  omega


/-- The side of the edge `p – v` containing `v`: the taxa whose leaf is closer to `v` than to
`p`. -/
noncomputable def edgeSide (T : UnrootedBinaryTree X) (p v : T.V) : Finset X :=
  Finset.univ.filter fun x => T.G.dist (T.label x) v < T.G.dist (T.label x) p

/-- The **edge splits** of `T`: the sides of all its edges (both sides of every edge). -/
noncomputable def edgeSplits (T : UnrootedBinaryTree X) : Finset (Finset X) :=
  ((Finset.univ ×ˢ Finset.univ).filter fun e : T.V × T.V => T.G.Adj e.1 e.2).image
    fun e => edgeSide T e.1 e.2

/-- The two sides of an edge are complementary. -/
theorem compl_edgeSide (T : UnrootedBinaryTree X) {p v : T.V} (hpv : T.G.Adj p v) :
    (edgeSide T p v)ᶜ = edgeSide T v p := by
  ext x
  simp only [edgeSide, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
  rcases T.isTree.dist_eq_dist_add_one_of_adj (T.label x) hpv with h | h <;> omega

/-- The cluster of a vertex `v` seen from `a` is the side of `v` of the edge from `v` to its
neighbor `p` toward `a`. -/
theorem cluster_eq_edgeSide (T : UnrootedBinaryTree X) (a : X) {p v : T.V} (hpv : T.G.Adj p v)
    (hd : T.G.dist (T.label a) v = T.G.dist (T.label a) p + 1) :
    cluster T a v = edgeSide T p v := by
  ext x
  simp only [cluster, edgeSide, Finset.mem_filter, Finset.mem_univ, true_and]
  have h1 := SimpleGraph.dist_eq_one_iff_adj.mpr hpv
  have e : T.G.dist (T.label x) v = T.G.dist v (T.label x) := SimpleGraph.dist_comm
  have e' : T.G.dist (T.label x) p = T.G.dist p (T.label x) := SimpleGraph.dist_comm
  constructor
  · rintro ⟨-, hb⟩
    have := T.isTree.connected.dist_triangle (u := (T.label a : T.V)) (v := p)
      (w := (T.label x : T.V))
    omega
  · intro hlt
    have hx : x ≠ a := by
      rintro rfl
      omega
    refine ⟨hx, ?_⟩
    rcases T.isTree.dist_eq_dist_add_one_of_adj (T.label x) hpv with h | h
    · exact dist_add_dist_of_cross T.isTree hpv hd h
    · omega

omit [Fintype X] [DecidableEq X] in
/-- Every vertex other than the leaf `a` has a neighbor one step closer to `a` (adapted from the
private `exists_parent` of `UnrootedTreeCount`). -/
private theorem exists_parent (T : UnrootedBinaryTree X) (a : X) {v : T.V}
    (hv : v ≠ T.label a) :
    ∃ p, T.G.Adj p v ∧ T.G.dist (T.label a) v = T.G.dist (T.label a) p + 1 := by
  obtain ⟨q, hq⟩ := T.isTree.connected.exists_walk_length_eq_dist v (T.label a)
  cases q with
  | nil => exact absurd rfl hv
  | @cons _ c _ h q' =>
    refine ⟨c, h.symm, ?_⟩
    have h1 := SimpleGraph.dist_le q'
    have h3 := T.isTree.connected.dist_triangle (u := v) (v := c) (w := T.label a)
    have h2 := SimpleGraph.dist_eq_one_iff_adj.mpr h
    simp only [SimpleGraph.Walk.length_cons] at hq
    have e1 : T.G.dist (T.label a : T.V) v = T.G.dist v (T.label a) := SimpleGraph.dist_comm
    have e2 : T.G.dist (T.label a : T.V) c = T.G.dist c (T.label a) := SimpleGraph.dist_comm
    omega

/-- The cluster of the leaf `a` itself (all other taxa) is the side of its pendant edge. -/
private theorem cluster_label_mem_edgeSplits (T : UnrootedBinaryTree X) (a : X) :
    cluster T a (T.label a) ∈ edgeSplits T := by
  have hdeg := (T.label a).2
  rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_one] at hdeg
  obtain ⟨r, hr⟩ := hdeg
  have hra : T.G.Adj (T.label a) r := by
    rw [← SimpleGraph.mem_neighborFinset, hr]; exact Finset.mem_singleton_self r
  have huniq : ∀ c, T.G.Adj (T.label a) c → c = r := fun c hc => by
    have := (T.G.mem_neighborFinset _ c).mpr hc
    rwa [hr, Finset.mem_singleton] at this
  have hside : cluster T a (T.label a) = edgeSide T (T.label a) r := by
    ext x
    simp only [cluster, edgeSide, Finset.mem_filter, Finset.mem_univ, true_and,
      SimpleGraph.dist_self, zero_add, and_true]
    constructor
    · intro hx
      have hne : (T.label a : T.V) ≠ T.label x := fun e => hx (T.label.injective
        (Subtype.ext e)).symm
      obtain ⟨c, hc, hd⟩ := exists_parent T x hne
      rw [← huniq c hc.symm]
      omega
    · intro hlt hx
      subst hx
      simp at hlt
  rw [hside]
  exact Finset.mem_image.mpr ⟨(T.label a, r), Finset.mem_filter.mpr ⟨by simp, hra⟩, rfl⟩

/-- The split set computed from any leaf is the set of edge splits. -/
theorem splitSet_eq_edgeSplits (T : UnrootedBinaryTree X) (a : X) :
    splitSet T a = edgeSplits T := by
  have hmem : ∀ {p v : T.V}, T.G.Adj p v → edgeSide T p v ∈ edgeSplits T := fun h =>
    Finset.mem_image.mpr ⟨(_, _), Finset.mem_filter.mpr ⟨by simp, h⟩, rfl⟩
  have hcl : ∀ v, cluster T a v ∈ edgeSplits T ∧ (cluster T a v)ᶜ ∈ edgeSplits T := by
    intro v
    by_cases hv : v = T.label a
    · subst hv
      have h := cluster_label_mem_edgeSplits T a
      refine ⟨h, ?_⟩
      obtain ⟨e, he, he'⟩ := Finset.mem_image.mp h
      rw [← he', compl_edgeSide T (Finset.mem_filter.mp he).2]
      exact hmem (Finset.mem_filter.mp he).2.symm
    · obtain ⟨p, hpv, hd⟩ := exists_parent T a hv
      rw [cluster_eq_edgeSide T a hpv hd, compl_edgeSide T hpv]
      exact ⟨hmem hpv, hmem hpv.symm⟩
  ext A
  constructor
  · intro hA
    simp only [splitSet, clusterSet, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
      true_and] at hA
    rcases hA with ⟨v, rfl⟩ | ⟨C, ⟨v, rfl⟩, rfl⟩
    · exact (hcl v).1
    · exact (hcl v).2
  · intro hA
    obtain ⟨⟨u, v⟩, he, rfl⟩ := Finset.mem_image.mp hA
    have huv : T.G.Adj u v := (Finset.mem_filter.mp he).2
    simp only [splitSet, clusterSet, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
      true_and]
    rcases T.isTree.dist_eq_dist_add_one_of_adj (T.label a) huv with h | h
    · right
      refine ⟨cluster T a u, ⟨u, rfl⟩, ?_⟩
      rw [cluster_eq_edgeSide T a huv.symm h, compl_edgeSide T huv.symm]
    · left
      exact ⟨v, cluster_eq_edgeSide T a huv h⟩

/-- **The split set does not depend on the leaf used to compute it.** -/
theorem splitSet_eq_splitSet (T : UnrootedBinaryTree X) (a b : X) :
    splitSet T a = splitSet T b := by
  rw [splitSet_eq_edgeSplits, splitSet_eq_edgeSplits]

/-- Any two splits of one tree are compatible. -/
theorem compatible_of_mem_splitSet {T : UnrootedBinaryTree X} {a : X} {A B : Finset X}
    (hA : A ∈ splitSet T a) (hB : B ∈ splitSet T a) : Compatible A B := by
  have hcl : ∀ {C D : Finset X}, C ∈ clusterSet T a → D ∈ clusterSet T a → Compatible C D :=
    fun hC hD => (compatible_iff_nested_or_disjoint (notMem_of_mem_clusterSet T a hC)
      (notMem_of_mem_clusterSet T a hD)).mpr
      ((isBinaryHierarchy_clusterSet T a).2.2.2.1 _ hC _ hD)
  simp only [splitSet, Finset.mem_union, Finset.mem_image] at hA hB
  rcases hA with hA | ⟨C, hC, rfl⟩ <;> rcases hB with hB | ⟨D, hD, rfl⟩
  · exact hcl hA hB
  · exact compatible_compl_right.mpr (hcl hA hD)
  · exact compatible_compl_left.mpr (hcl hC hB)
  · exact compatible_compl_left.mpr (compatible_compl_right.mpr (hcl hC hD))

/-- The splits-equivalence theorem with the split set computed from the leaf `a`. -/
private theorem splits_equivalence_aux (a : X) (hX : (Finset.univ.erase a).Nonempty)
    (F : Finset (Finset X)) (hne : ∀ A ∈ F, A.Nonempty ∧ Aᶜ.Nonempty) :
    (∃ T : UnrootedBinaryTree X, F ⊆ splitSet T a) ↔
      ∀ A ∈ F, ∀ B ∈ F, Compatible A B := by
  constructor
  · rintro ⟨T, hT⟩ A hA B hB
    exact compatible_of_mem_splitSet (hT hA) (hT hB)
  intro hc
  set norm : Finset X → Finset X := fun A => if a ∈ A then Aᶜ else A with hnorm
  have hna : ∀ A, a ∉ norm A := by
    intro A
    by_cases h : a ∈ A <;> simp [hnorm, h]
  have hcomp : ∀ A B, Compatible (norm A) (norm B) ↔ Compatible A B := by
    intro A B
    by_cases h : a ∈ A <;> by_cases h' : a ∈ B <;>
      simp [hnorm, h, h', compatible_compl_left, compatible_compl_right]
  have hF : ∀ C ∈ F.image norm, C.Nonempty ∧ C ⊆ Finset.univ.erase a := by
    intro C hC
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hC
    refine ⟨?_, fun x hx => Finset.mem_erase.mpr ⟨fun e => hna A (e ▸ hx), Finset.mem_univ x⟩⟩
    by_cases h : a ∈ A
    · simpa [hnorm, h] using (hne A hA).2
    · simpa [hnorm, h] using (hne A hA).1
  have hlam : ∀ C ∈ F.image norm, ∀ D ∈ F.image norm, C ⊆ D ∨ D ⊆ C ∨ Disjoint C D := by
    intro C hC D hD
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hD
    exact (compatible_iff_nested_or_disjoint (hna A) (hna B)).mp ((hcomp A B).mpr (hc A hA B hB))
  obtain ⟨H, hH, hsub⟩ := exists_isBinaryHierarchy_superset hX hF hlam
  obtain ⟨T, hT⟩ := exists_clusterSet_eq a H hH
  refine ⟨T, fun A hA => ?_⟩
  have hm : norm A ∈ clusterSet T a := hT ▸ hsub (Finset.mem_image_of_mem norm hA)
  simp only [splitSet, Finset.mem_union, Finset.mem_image]
  by_cases h : a ∈ A
  · exact Or.inr ⟨Aᶜ, by simpa [hnorm, h] using hm, compl_compl A⟩
  · exact Or.inl (by simpa [hnorm, h] using hm)

/-- Any two splits of one tree are compatible. -/
theorem compatible_of_mem_edgeSplits {T : UnrootedBinaryTree X} {A B : Finset X}
    (hA : A ∈ edgeSplits T) (hB : B ∈ edgeSplits T) : Compatible A B := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨a⟩⟩
  · rw [Finset.eq_empty_of_isEmpty A]
    exact Or.inl (Finset.disjoint_empty_left B)
  · rw [← splitSet_eq_edgeSplits T a] at hA hB
    exact compatible_of_mem_splitSet hA hB

/-- **Splits-equivalence theorem**, binary form (Buneman 1971; Semple & Steel 2003, Theorem
3.1.4): on at least two taxa, a family `F` of proper splits (both sides nonempty) is contained in
the split set of some unrooted binary phylogenetic tree iff its members are pairwise compatible.
The tree is a binary refinement of the tree whose splits are exactly `F` and the trivial ones. -/
theorem splits_equivalence (hX : 1 < Fintype.card X) (F : Finset (Finset X))
    (hne : ∀ A ∈ F, A.Nonempty ∧ Aᶜ.Nonempty) :
    (∃ T : UnrootedBinaryTree X, F ⊆ edgeSplits T) ↔
      ∀ A ∈ F, ∀ B ∈ F, Compatible A B := by
  obtain ⟨a⟩ : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  have hX' : (Finset.univ.erase a).Nonempty := Finset.card_pos.mp (by
    rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ]; omega)
  simp only [← splitSet_eq_edgeSplits _ a]
  exact splits_equivalence_aux a hX' F hne

/-- `T` is a **perfect phylogeny** for the binary character matrix `M` (taxa by characters):
the split of every non-constant column is a split of `T`, i.e. every character changes state
on exactly one edge. -/
def IsPerfectPhylogeny {ι : Type} (T : UnrootedBinaryTree X) (M : X → ι → Bool) : Prop :=
  ∀ j, charSplit (M · j) = ∅ ∨ charSplit (M · j) = Finset.univ ∨
    charSplit (M · j) ∈ edgeSplits T

/-- **Perfect phylogeny and the four-gamete condition** (Estabrook, Johnson & McMorris 1976;
Gusfield 1991): a binary character matrix on at least two taxa has a perfect phylogeny iff no
two of its columns show all four gametes. -/
theorem exists_perfectPhylogeny_iff {ι : Type} (hX : 1 < Fintype.card X) (M : X → ι → Bool) :
    (∃ T : UnrootedBinaryTree X, IsPerfectPhylogeny T M) ↔
      ∀ j k, ¬ FourGametes (M · j) (M · k) := by
  have triv : ∀ A B : Finset X, (A = ∅ ∨ A = Finset.univ) → Compatible A B := by
    rintro A B (rfl | rfl)
    · exact Or.inl (Finset.disjoint_empty_left B)
    · exact Or.inr (Or.inr (Or.inl (by simp)))
  constructor
  · rintro ⟨T, hT⟩ j k
    rw [← compatible_iff_not_fourGametes]
    rcases hT j with h | h | h
    · exact triv _ _ (Or.inl h)
    · exact triv _ _ (Or.inr h)
    rcases hT k with h' | h' | h'
    · exact (triv _ _ (Or.inl h')).symm
    · exact (triv _ _ (Or.inr h')).symm
    exact compatible_of_mem_edgeSplits h h'
  intro hc
  classical
  let F : Finset (Finset X) := Finset.univ.filter fun A =>
    (∃ j, charSplit (M · j) = A) ∧ A.Nonempty ∧ Aᶜ.Nonempty
  obtain ⟨T, hT⟩ := (splits_equivalence hX F (fun A hA => (Finset.mem_filter.mp hA).2.2)).mpr
    (by
      intro A hA B hB
      obtain ⟨⟨j, rfl⟩, -⟩ := (Finset.mem_filter.mp hA).2
      obtain ⟨⟨k, rfl⟩, -⟩ := (Finset.mem_filter.mp hB).2
      exact (compatible_iff_not_fourGametes _ _).mpr (hc j k))
  refine ⟨T, fun j => ?_⟩
  by_cases h0 : charSplit (M · j) = ∅
  · exact Or.inl h0
  by_cases h1 : charSplit (M · j) = Finset.univ
  · exact Or.inr (Or.inl h1)
  refine Or.inr (Or.inr (hT (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨j, rfl⟩,
    Finset.nonempty_iff_ne_empty.mpr h0, ?_⟩)))
  rw [Finset.nonempty_iff_ne_empty, Ne, Finset.compl_eq_empty_iff]
  exact h1

end Trees

/-! ### The Robinson–Foulds distance -/

section RobinsonFoulds

variable {X : Type} [Fintype X] [DecidableEq X]

/-- The **Robinson–Foulds distance**: the number of splits in exactly one of the two trees.
Each split is counted once, by its side away from the leaf `a` (its cluster seen from `a`);
trivial splits are common to all trees and cancel. The value does not depend on `a`
(`rfDist_eq_rfDist`). -/
noncomputable def rfDist (a : X) (T T' : UnrootedBinaryTree X) : ℕ :=
  (clusterSet T a ∆ clusterSet T' a).card

/-- Each split is counted twice in the symmetric difference of the split sets (once per side),
so the Robinson–Foulds distance is half of it. -/
theorem two_mul_rfDist (a : X) (T T' : UnrootedBinaryTree X) :
    2 * rfDist a T T' = (splitSet T a ∆ splitSet T' a).card := by
  have hmem : ∀ (U : UnrootedBinaryTree X) (A : Finset X),
      A ∈ splitSet U a ↔ (a ∉ A ∧ A ∈ clusterSet U a) ∨ (a ∈ A ∧ Aᶜ ∈ clusterSet U a) := by
    intro U A
    simp only [splitSet, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro (hA | ⟨C, hC, rfl⟩)
      · exact Or.inl ⟨notMem_of_mem_clusterSet U a hA, hA⟩
      · refine Or.inr ⟨?_, by rwa [compl_compl]⟩
        simpa using notMem_of_mem_clusterSet U a hC
    · rintro (⟨-, hA⟩ | ⟨-, hA⟩)
      · exact Or.inl hA
      · exact Or.inr ⟨Aᶜ, hA, compl_compl A⟩
  set D := clusterSet T a ∆ clusterSet T' a with hD
  have hDa : ∀ C ∈ D, a ∉ C := by
    intro C hC
    rcases Finset.mem_symmDiff.mp hC with ⟨h, -⟩ | ⟨h, -⟩
    · exact notMem_of_mem_clusterSet T a h
    · exact notMem_of_mem_clusterSet T' a h
  have heq : splitSet T a ∆ splitSet T' a = D ∪ D.image (·ᶜ) := by
    ext A
    rw [Finset.mem_symmDiff, hmem, hmem, Finset.mem_union, Finset.mem_image, hD]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> by_cases ha : a ∈ A
      · exact Or.inr ⟨Aᶜ, Finset.mem_symmDiff.mpr (Or.inl ⟨by tauto, by tauto⟩), compl_compl A⟩
      · exact Or.inl (Finset.mem_symmDiff.mpr (Or.inl ⟨by tauto, by tauto⟩))
      · exact Or.inr ⟨Aᶜ, Finset.mem_symmDiff.mpr (Or.inr ⟨by tauto, by tauto⟩), compl_compl A⟩
      · exact Or.inl (Finset.mem_symmDiff.mpr (Or.inr ⟨by tauto, by tauto⟩))
    · rintro (hA | ⟨C, hC, rfl⟩)
      · have ha := hDa A hA
        rcases Finset.mem_symmDiff.mp hA with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨Or.inl ⟨ha, h1⟩, by tauto⟩
        · exact Or.inr ⟨Or.inl ⟨ha, h1⟩, by tauto⟩
      · have ha : a ∈ Cᶜ := by simpa using hDa C hC
        rw [compl_compl]
        rcases Finset.mem_symmDiff.mp hC with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨Or.inr ⟨ha, h1⟩, by tauto⟩
        · exact Or.inr ⟨Or.inr ⟨ha, h1⟩, by tauto⟩
  have hdis : Disjoint D (D.image (·ᶜ)) := by
    rw [Finset.disjoint_left]
    intro C hC hC'
    obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hC'
    exact hDa _ hC (by simpa using hDa E hE)
  rw [heq, Finset.card_union_of_disjoint hdis,
    Finset.card_image_of_injective _ compl_injective, rfDist]
  ring

/-- The Robinson–Foulds distance does not depend on the leaf used to compute it. -/
theorem rfDist_eq_rfDist (a b : X) (T T' : UnrootedBinaryTree X) :
    rfDist a T T' = rfDist b T T' := by
  have h1 := two_mul_rfDist a T T'
  have h2 := two_mul_rfDist b T T'
  rw [splitSet_eq_splitSet T a b, splitSet_eq_splitSet T' a b] at h1
  omega

/-- The Robinson–Foulds distance from a tree to itself is zero. -/
theorem rfDist_self (a : X) (T : UnrootedBinaryTree X) : rfDist a T T = 0 := by
  simp [rfDist]

/-- The Robinson–Foulds distance is symmetric. -/
theorem rfDist_comm (a : X) (T T' : UnrootedBinaryTree X) : rfDist a T T' = rfDist a T' T := by
  rw [rfDist, rfDist, symmDiff_comm]

/-- The Robinson–Foulds distance satisfies the triangle inequality. -/
theorem rfDist_triangle (a : X) (T₁ T₂ T₃ : UnrootedBinaryTree X) :
    rfDist a T₁ T₃ ≤ rfDist a T₁ T₂ + rfDist a T₂ T₃ := by
  unfold rfDist
  exact (Finset.card_le_card (symmDiff_triangle (clusterSet T₁ a) (clusterSet T₂ a)
    (clusterSet T₃ a))).trans (Finset.card_union_le _ _)

/-- The Robinson–Foulds distance vanishes exactly on isomorphic trees (Robinson & Foulds 1981). -/
theorem rfDist_eq_zero_iff (a : X) (T T' : UnrootedBinaryTree X) :
    rfDist a T T' = 0 ↔ T.Iso T' := by
  rw [rfDist, Finset.card_eq_zero]
  constructor
  · intro h
    exact iso_of_clusterSet_eq a (symmDiff_eq_bot.mp h)
  · intro h
    rw [clusterSet_eq_of_iso h a]
    exact symmDiff_self _

/-- The Robinson–Foulds distance is invariant under isomorphism, so it is a metric on the trees
up to isomorphism. -/
theorem rfDist_congr {a : X} {T₁ T₂ T' : UnrootedBinaryTree X} (h : T₁.Iso T₂) :
    rfDist a T₁ T' = rfDist a T₂ T' := by
  rw [rfDist, rfDist, clusterSet_eq_of_iso h a]

/-- **Maximum of the Robinson–Foulds distance**: on `n ≥ 3` taxa it is at most `2 (n - 3)`, the
number of nontrivial splits of two binary trees (Robinson & Foulds 1981). -/
theorem rfDist_le (a : X) (hn : 3 ≤ Fintype.card X) (T T' : UnrootedBinaryTree X) :
    rfDist a T T' ≤ 2 * (Fintype.card X - 3) := by
  set S : Finset X := Finset.univ.erase a with hSdef
  have hS : S.card = Fintype.card X - 1 := by
    rw [hSdef, Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ]
  set G : Finset (Finset X) := insert S (S.image ({·})) with hG
  have hGcard : G.card = Fintype.card X := by
    rw [hG, Finset.card_insert_of_notMem, Finset.card_image_of_injective _
      Finset.singleton_injective, hS]
    · omega
    · intro hm
      obtain ⟨x, -, hx⟩ := Finset.mem_image.mp hm
      have := congrArg Finset.card hx
      rw [Finset.card_singleton, hS] at this
      omega
  have hsub : ∀ U : UnrootedBinaryTree X, G ⊆ clusterSet U a := by
    intro U C hC
    have hH := isBinaryHierarchy_clusterSet U a
    rw [hG, Finset.mem_insert, Finset.mem_image] at hC
    rcases hC with rfl | ⟨x, hx, rfl⟩
    · exact hH.1
    · exact hH.2.2.1 x hx
  have hcard : ∀ U : UnrootedBinaryTree X, (clusterSet U a \ G).card + 3 = Fintype.card X := by
    intro U
    have h1 := IsBinaryHierarchy.card_add_one (isBinaryHierarchy_clusterSet U a)
    rw [Finset.card_sdiff_of_subset (hsub U), hGcard]
    have h2 := Finset.card_le_card (hsub U)
    rw [hGcard] at h2
    rw [hS] at h1
    omega
  have hss : clusterSet T a ∆ clusterSet T' a ⊆ (clusterSet T a \ G) ∪ (clusterSet T' a \ G) := by
    intro C hC
    rw [Finset.mem_symmDiff] at hC
    rw [Finset.mem_union, Finset.mem_sdiff, Finset.mem_sdiff]
    rcases hC with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, fun h => h2 (hsub T' h)⟩
    · exact Or.inr ⟨h1, fun h => h2 (hsub T h)⟩
  have := (Finset.card_le_card hss).trans (Finset.card_union_le _ _)
  have h1 := hcard T
  have h2 := hcard T'
  unfold rfDist
  omega

end RobinsonFoulds

/-! ### Majority-rule consensus and bootstrap support -/

section Consensus

variable {X : Type} [Fintype X] [DecidableEq X]

/-- The **majority splits** of a finite family of trees `T i`: the clusters, seen from `a`, of
more than half of the trees (repetitions in the family count). -/
noncomputable def majoritySplits {ι : Type} [Fintype ι] (T : ι → UnrootedBinaryTree X) (a : X) :
    Finset (Finset X) :=
  Finset.univ.filter fun A =>
    Fintype.card ι < 2 * (Finset.univ.filter fun i => A ∈ clusterSet (T i) a).card

/-- **Majority splits are compatible** (Margush & McMorris 1981): two clusters each in more than
half of the trees are both clusters of a common tree (pigeonhole), hence nested or disjoint. -/
theorem nested_or_disjoint_of_mem_majoritySplits {ι : Type} [Fintype ι]
    {T : ι → UnrootedBinaryTree X} {a : X} {A B : Finset X} (hA : A ∈ majoritySplits T a)
    (hB : B ∈ majoritySplits T a) : A ⊆ B ∨ B ⊆ A ∨ Disjoint A B := by
  classical
  simp only [majoritySplits, Finset.mem_filter, Finset.mem_univ, true_and] at hA hB
  set IA := Finset.univ.filter fun i => A ∈ clusterSet (T i) a
  set IB := Finset.univ.filter fun i => B ∈ clusterSet (T i) a
  have hu := Finset.card_union_add_card_inter IA IB
  have hle : (IA ∪ IB).card ≤ Fintype.card ι := Finset.card_le_univ _
  obtain ⟨i, hi⟩ : (IA ∩ IB).Nonempty := by
    rw [← Finset.card_pos]
    omega
  rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at hi
  exact (isBinaryHierarchy_clusterSet (T i) a).2.2.2.1 A hi.1.2 B hi.2.2

/-- **The majority-rule consensus tree**: the majority splits are clusters of one unrooted
binary phylogenetic tree (a binary refinement of the majority-rule consensus tree). -/
theorem exists_tree_majoritySplits_subset {ι : Type} [Fintype ι]
    (T : ι → UnrootedBinaryTree X) (a : X) (hX : (Finset.univ.erase a).Nonempty) :
    ∃ T₀ : UnrootedBinaryTree X, majoritySplits T a ⊆ clusterSet T₀ a := by
  have hF : ∀ C ∈ majoritySplits T a, C.Nonempty ∧ C ⊆ Finset.univ.erase a := by
    intro C hC
    simp only [majoritySplits, Finset.mem_filter, Finset.mem_univ, true_and] at hC
    obtain ⟨i, hi⟩ : (Finset.univ.filter fun i => C ∈ clusterSet (T i) a).Nonempty := by
      rw [← Finset.card_pos]
      omega
    exact (isBinaryHierarchy_clusterSet (T i) a).2.1 C (Finset.mem_filter.mp hi).2
  obtain ⟨H, hH, hsub⟩ := exists_isBinaryHierarchy_superset hX hF
    (fun A hA B hB => nested_or_disjoint_of_mem_majoritySplits hA hB)
  obtain ⟨T₀, hT₀⟩ := exists_clusterSet_eq a H hH
  exact ⟨T₀, hT₀ ▸ hsub⟩

/-- **Bootstrap support** (Felsenstein 1985) of the split with side `A` away from `a`, for a
tree estimator `est` and an alignment `M` of `m` sites: the fraction of the `m ^ m` site
resamplings with replacement `w : Fin m → Fin m` (uniform draws, whose site counts are
multinomial) for which the tree estimated from the resampled alignment `M ∘ w` has the
cluster `A`. This is the exact bootstrap proportion; Felsenstein's procedure estimates it from a
sample of resamplings. -/
noncomputable def bootstrapSupport {σ : Type} {m : ℕ}
    (est : (Fin m → X → σ) → UnrootedBinaryTree X) (a : X) (M : Fin m → X → σ)
    (A : Finset X) : ℝ :=
  ((Finset.univ.filter fun w : Fin m → Fin m => A ∈ clusterSet (est (M ∘ w)) a).card : ℝ) /
    ((m ^ m : ℕ) : ℝ)

/-- Bootstrap support is a frequency: it lies in `[0, 1]`. -/
theorem bootstrapSupport_mem_Icc {σ : Type} {m : ℕ}
    (est : (Fin m → X → σ) → UnrootedBinaryTree X) (a : X) (M : Fin m → X → σ)
    (A : Finset X) : bootstrapSupport est a M A ∈ Set.Icc 0 1 := by
  have hN : ((m ^ m : ℕ) : ℝ) = (Fintype.card (Fin m → Fin m) : ℝ) := by
    simp
  have hpos : (0 : ℝ) < (Fintype.card (Fin m → Fin m) : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := Fin m → Fin m) (h := ⟨id⟩)
  unfold bootstrapSupport
  rw [hN]
  refine ⟨div_nonneg (Nat.cast_nonneg _) hpos.le, (div_le_one hpos).mpr ?_⟩
  exact_mod_cast Finset.card_le_univ _

/-- A split has bootstrap support above one half iff it is a majority split of the bootstrap
replicate trees; so the splits with support above one half are pairwise compatible and form
one tree (`exists_tree_majoritySplits_subset`). -/
theorem one_half_lt_bootstrapSupport_iff {σ : Type} {m : ℕ}
    (est : (Fin m → X → σ) → UnrootedBinaryTree X) (a : X) (M : Fin m → X → σ)
    (A : Finset X) :
    1 / 2 < bootstrapSupport est a M A ↔ A ∈ majoritySplits (fun w => est (M ∘ w)) a := by
  have hN : ((m ^ m : ℕ) : ℝ) = (Fintype.card (Fin m → Fin m) : ℝ) := by
    simp
  have hpos : (0 : ℝ) < (Fintype.card (Fin m → Fin m) : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := Fin m → Fin m) (h := ⟨id⟩)
  unfold bootstrapSupport
  rw [hN, lt_div_iff₀ hpos]
  simp only [majoritySplits, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    have : (Fintype.card (Fin m → Fin m) : ℝ) <
        2 * ((Finset.univ.filter fun w : Fin m → Fin m =>
          A ∈ clusterSet (est (M ∘ w)) a).card : ℝ) := by linarith
    exact_mod_cast this
  · intro h
    have : (Fintype.card (Fin m → Fin m) : ℝ) <
        2 * ((Finset.univ.filter fun w : Fin m → Fin m =>
          A ∈ clusterSet (est (M ∘ w)) a).card : ℝ) := by exact_mod_cast h
    linarith

end Consensus

/-! ### Ultrametrics and UPGMA -/

section Ultrametric

variable {X : Type} [Fintype X]

/-- `d` is an **ultrametric** on the taxa: symmetric, zero exactly on the diagonal, and
satisfying the **three-point condition** `d x z ≤ max (d x y) (d y z)` (equivalently, of the
three distances among any three taxa the two largest are equal). -/
structure IsUltrametric (d : X → X → ℝ) : Prop where
  /-- Symmetry. -/
  symm : ∀ x y, d x y = d y x
  /-- Zero on the diagonal. -/
  self : ∀ x, d x x = 0
  /-- Positive off the diagonal. -/
  pos : ∀ x y, x ≠ y → 0 < d x y
  /-- The three-point condition. -/
  three_point : ∀ x y z, d x z ≤ max (d x y) (d y z)

/-- `d` is the metric of a **dated rooted tree**, encoded by its clusters: a hierarchy `H` on
the taxa with dates `h` (`0` at the leaves, strictly increasing from a cluster to any cluster
strictly containing it) such that `d x y` is the date of the smallest cluster containing `x`
and `y` (their most recent common ancestor). With edge lengths `(h D - h C) / 2` from each
cluster `C` to its parent `D`, `d x y` is the path length from `x` to `y` and all leaves are
equidistant from the root (Semple & Steel 2003, Section 7.2). -/
def IsDatedTreeMetric (d : X → X → ℝ) : Prop :=
  ∃ (H : Finset (Finset X)) (h : Finset X → ℝ), IsHierarchy Finset.univ H ∧
    (∀ x, h {x} = 0) ∧ (∀ C ∈ H, ∀ D ∈ H, C ⊂ D → h C < h D) ∧
    ∀ x y, ∃ C ∈ H, x ∈ C ∧ y ∈ C ∧ d x y = h C ∧ ∀ D ∈ H, x ∈ D → y ∈ D → C ⊆ D

omit [Fintype X] in
/-- In an ultrametric the two largest of the three distances among three taxa are equal. -/
private theorem IsUltrametric.isosceles {d : X → X → ℝ} (hd : IsUltrametric d) (x y z : X) :
    (d x y = d x z ∧ d y z ≤ d x y) ∨ (d x y = d y z ∧ d x z ≤ d x y) ∨
      (d x z = d y z ∧ d x y ≤ d x z) := by
  have h1 := hd.three_point x z y
  have h2 := hd.three_point x y z
  have h3 := hd.three_point y x z
  rw [hd.symm z y] at h1
  rw [hd.symm y x] at h3
  simp only [le_max_iff] at h1 h2 h3
  rcases le_total (d x y) (d x z) with h | h <;> rcases le_total (d x y) (d y z) with h' | h' <;>
    rcases le_total (d x z) (d y z) with h'' | h'' <;>
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
    first
    | exact Or.inl ⟨by linarith, by linarith⟩
    | exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
    | exact Or.inr (Or.inr ⟨by linarith, by linarith⟩)

omit [Fintype X] in
/-- **Ultrametrics satisfy the four-point condition** (Semple & Steel 2003, Section 7.2), so
every ultrametric on a finite set is a tree metric (`IsUltrametric.isTreeMetric`). -/
theorem IsUltrametric.fourPointCondition {d : X → X → ℝ} (hd : IsUltrametric d) :
    MathlibExt.Biology.Phylogenetics.Buneman.FourPointCondition d := by
  intro x y z t
  have e1 := hd.isosceles x y z
  have e2 := hd.isosceles x y t
  have e3 := hd.isosceles x z t
  have e4 := hd.isosceles y z t
  rw [le_max_iff]
  rcases e1 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> rcases e2 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;>
    rcases e3 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> rcases e4 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;>
    first | (left; linarith) | (right; linarith)

omit [Fintype X] in
/-- Every ultrametric on a finite set is a tree metric (via Buneman's four-point theorem). -/
theorem IsUltrametric.isTreeMetric [Finite X] {d : X → X → ℝ} (hd : IsUltrametric d) :
    MathlibExt.Biology.Phylogenetics.Buneman.IsTreeMetric d :=
  MathlibExt.Biology.Phylogenetics.Buneman.isTreeMetric_of_fourPointCondition d hd.self hd.symm
    hd.fourPointCondition

/-- The diameter of a cluster: the largest distance between two of its members (`0` for the
empty cluster). -/
private noncomputable def diam (d : X → X → ℝ) (C : Finset X) : ℝ :=
  if h : C.Nonempty then (C ×ˢ C).sup' (h.product h) fun p => d p.1 p.2 else 0

omit [Fintype X] in
private theorem le_diam {d : X → X → ℝ} {C : Finset X} {u v : X} (hu : u ∈ C) (hv : v ∈ C) :
    d u v ≤ diam d C := by
  unfold diam
  split_ifs with h
  · exact Finset.le_sup' (fun p : X × X => d p.1 p.2) (b := (u, v))
      (Finset.mem_product.mpr ⟨hu, hv⟩)
  · exact absurd ⟨u, hu⟩ h

omit [Fintype X] in
private theorem diam_le {d : X → X → ℝ} {C : Finset X} (hC : C.Nonempty) {r : ℝ}
    (h : ∀ u ∈ C, ∀ v ∈ C, d u v ≤ r) : diam d C ≤ r := by
  unfold diam
  split_ifs
  exact Finset.sup'_le _ _ fun p hp => h p.1 (Finset.mem_product.mp hp).1 p.2
    (Finset.mem_product.mp hp).2

private theorem isUltrametric_of_isDatedTreeMetric {d : X → X → ℝ} (hd : IsDatedTreeMetric d) :
    IsUltrametric d := by
  obtain ⟨H, h, ⟨-, hsub, hsing, hlam⟩, h0, hmono, hmin⟩ := hd
  have hle : ∀ C ∈ H, ∀ D ∈ H, C ⊆ D → h C ≤ h D := by
    intro C hC D hD hCD
    by_cases e : C = D
    · rw [e]
    · exact (hmono C hC D hD (Finset.ssubset_iff_subset_ne.mpr ⟨hCD, e⟩)).le
  have hself : ∀ x, d x x = 0 := by
    intro x
    obtain ⟨C, hC, hx, -, hdC, hCmin⟩ := hmin x x
    have : C = {x} := le_antisymm (hCmin _ (hsing x (Finset.mem_univ x))
      (Finset.mem_singleton_self x) (Finset.mem_singleton_self x))
      (Finset.singleton_subset_iff.mpr hx)
    rw [hdC, this, h0]
  refine ⟨?_, hself, ?_, ?_⟩
  · intro x y
    obtain ⟨C, hC, hx, hy, hdC, hCmin⟩ := hmin x y
    obtain ⟨D, hD, hy', hx', hdD, hDmin⟩ := hmin y x
    rw [hdC, hdD, le_antisymm (hCmin D hD hx' hy') (hDmin C hC hy hx)]
  · intro x y hxy
    obtain ⟨C, hC, hx, hy, hdC, -⟩ := hmin x y
    have hlt : ({x} : Finset X) ⊂ C := Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.singleton_subset_iff.mpr hx, fun e => hxy (Finset.mem_singleton.mp (e ▸ hy)).symm⟩
    have := hmono _ (hsing x (Finset.mem_univ x)) C hC hlt
    rw [h0] at this
    rw [hdC]; exact this
  · intro x y z
    obtain ⟨C₁, h₁, hx₁, hy₁, hd₁, -⟩ := hmin x y
    obtain ⟨C₂, h₂, hy₂, hz₂, hd₂, -⟩ := hmin y z
    obtain ⟨C₃, h₃, -, -, hd₃, hmin₃⟩ := hmin x z
    rcases hlam C₁ h₁ C₂ h₂ with h12 | h21 | hdis
    · rw [hd₃, hd₂]
      exact (hle C₃ h₃ C₂ h₂ (hmin₃ C₂ h₂ (h12 hx₁) hz₂)).trans (le_max_right _ _)
    · rw [hd₃, hd₁]
      exact (hle C₃ h₃ C₁ h₁ (hmin₃ C₁ h₁ hx₁ (h21 hz₂))).trans (le_max_left _ _)
    · exact absurd hy₂ (Finset.disjoint_left.mp hdis hy₁)

private theorem isDatedTreeMetric_of_isUltrametric [Nonempty X] {d : X → X → ℝ}
    (hd : IsUltrametric d) : IsDatedTreeMetric d := by
  classical
  have hnn : ∀ x y, 0 ≤ d x y := by
    intro x y
    by_cases e : x = y
    · rw [e, hd.self]
    · exact (hd.pos x y e).le
  set ball : X → ℝ → Finset X := fun x r => Finset.univ.filter fun y => d x y ≤ r with hball
  have mem_ball : ∀ {x : X} {r : ℝ} {y : X}, y ∈ ball x r ↔ d x y ≤ r := by
    intro x r y
    simp [hball]
  have center : ∀ {x : X} {r : ℝ}, 0 ≤ r → x ∈ ball x r := fun hr =>
    mem_ball.mpr (by rw [hd.self]; exact hr)
  have half : ∀ {x u : X} {r : ℝ}, u ∈ ball x r → ball u r ⊆ ball x r := by
    intro x u r hu w hw
    rw [mem_ball] at hu hw ⊢
    exact (hd.three_point x u w).trans (max_le hu hw)
  have ball_eq : ∀ {x u : X} {r : ℝ}, u ∈ ball x r → ball u r = ball x r := by
    intro x u r hu
    refine le_antisymm (half hu) (half ?_)
    rw [mem_ball] at hu ⊢
    rwa [hd.symm]
  have diam_mem : ∀ x y, diam d (ball x (d x y)) = d x y := by
    intro x y
    refine le_antisymm (diam_le ⟨x, center (hnn x y)⟩ fun u hu v hv => ?_)
      (le_diam (center (hnn x y)) (mem_ball.mpr le_rfl))
    rw [mem_ball] at hu hv
    exact (hd.three_point u x v).trans (max_le (by rw [hd.symm]; exact hu) hv)
  set H : Finset (Finset X) :=
    (Finset.univ ×ˢ Finset.univ).image fun p : X × X => ball p.1 (d p.1 p.2) with hH
  have memH : ∀ {C : Finset X}, C ∈ H ↔ ∃ x y, ball x (d x y) = C := by
    intro C
    simp [hH]
  have repr : ∀ C ∈ H, ∀ u ∈ C, C = ball u (diam d C) := by
    intro C hC u hu
    obtain ⟨x, y, rfl⟩ := memH.mp hC
    rw [diam_mem, ball_eq hu]
  have nonemptyH : ∀ C ∈ H, C.Nonempty := by
    intro C hC
    obtain ⟨x, y, rfl⟩ := memH.mp hC
    exact ⟨x, center (hnn x y)⟩
  refine ⟨H, diam d, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · obtain ⟨x₀⟩ := ‹Nonempty X›
    obtain ⟨y₀, -, hy₀⟩ := Finset.exists_max_image Finset.univ (d x₀) Finset.univ_nonempty
    refine memH.mpr ⟨x₀, y₀, ?_⟩
    ext w
    simp only [mem_ball, Finset.mem_univ, iff_true]
    exact hy₀ w (Finset.mem_univ w)
  · intro C hC
    exact ⟨nonemptyH C hC, Finset.subset_univ _⟩
  · intro x _
    refine memH.mpr ⟨x, x, ?_⟩
    ext w
    rw [mem_ball, hd.self, Finset.mem_singleton]
    constructor
    · intro h
      by_contra e
      exact absurd h (not_le.mpr (hd.pos x w (Ne.symm e)))
    · rintro rfl
      exact (hd.self w).le
  · intro C hC D hD
    by_cases hdis : Disjoint C D
    · exact Or.inr (Or.inr hdis)
    obtain ⟨z, hzC, hzD⟩ := Finset.not_disjoint_iff.mp hdis
    rw [repr C hC z hzC, repr D hD z hzD]
    rcases le_total (diam d C) (diam d D) with h | h
    · left
      intro w hw
      rw [mem_ball] at hw ⊢
      exact hw.trans h
    · right; left
      intro w hw
      rw [mem_ball] at hw ⊢
      exact hw.trans h
  · intro x
    refine le_antisymm (diam_le (Finset.singleton_nonempty x) fun u hu v hv => ?_) ?_
    · rw [Finset.mem_singleton] at hu hv
      rw [hu, hv, hd.self]
    · have := le_diam (d := d) (Finset.mem_singleton_self x) (Finset.mem_singleton_self x)
      rwa [hd.self] at this
  · intro C hC D hD hCD
    have hle : diam d C ≤ diam d D := diam_le (nonemptyH C hC) fun u hu v hv =>
      le_diam (hCD.subset hu) (hCD.subset hv)
    refine lt_of_le_of_ne hle fun e => ?_
    obtain ⟨u, hu⟩ := nonemptyH C hC
    have : D = C := by rw [repr D hD u (hCD.subset hu), ← e, ← repr C hC u hu]
    exact hCD.ne this.symm
  · intro x y
    refine ⟨ball x (d x y), memH.mpr ⟨x, y, rfl⟩, center (hnn x y), mem_ball.mpr le_rfl,
      (diam_mem x y).symm, ?_⟩
    intro D hD hx hy
    rw [repr D hD x hx]
    intro w hw
    rw [mem_ball] at hw ⊢
    exact hw.trans (le_diam hx hy)

/-- **Ultrametrics are dated tree metrics** (Semple & Steel 2003, Theorem 7.2.5): on a
nonempty finite set of taxa, a dissimilarity satisfies the three-point condition (and is a
metric) iff it is the metric of a dated rooted tree. -/
theorem isUltrametric_iff_isDatedTreeMetric [Nonempty X] (d : X → X → ℝ) :
    IsUltrametric d ↔ IsDatedTreeMetric d :=
  ⟨isDatedTreeMetric_of_isUltrametric, isUltrametric_of_isDatedTreeMetric⟩

variable [DecidableEq X]

/-- The **average linkage** between two clusters: the mean of `d x y` over `x ∈ C`, `y ∈ D`.
-/
noncomputable def avgDist (d : X → X → ℝ) (C D : Finset X) : ℝ :=
  (∑ x ∈ C, ∑ y ∈ D, d x y) / (C.card * D.card : ℝ)

/-- The states reachable by **UPGMA** (Sokal & Michener 1958) on `d`: a partition `P` of the
taxa into blocks and the heights `c x y` recorded so far. It starts from the singletons; each
step merges two distinct blocks `C`, `D` of least average linkage (ties broken arbitrarily) and
records `avgDist d C D` as the height at which every `x ∈ C` and `y ∈ D` are joined (the
distance between them in the output tree; their common ancestor sits at half of it). -/
inductive UpgmaReaches (d : X → X → ℝ) : Finset (Finset X) → (X → X → ℝ) → Prop
  | init : UpgmaReaches d (Finset.univ.image ({·})) fun _ _ => 0
  | step {P : Finset (Finset X)} {c : X → X → ℝ} {C D : Finset X} :
      UpgmaReaches d P c → C ∈ P → D ∈ P → C ≠ D →
      (∀ E ∈ P, ∀ F ∈ P, E ≠ F → avgDist d C D ≤ avgDist d E F) →
      UpgmaReaches d (insert (C ∪ D) ((P.erase C).erase D))
        fun x y => if (x ∈ C ∧ y ∈ D) ∨ (x ∈ D ∧ y ∈ C) then avgDist d C D else c x y

/-- The blocks form a partition of the taxa into nonempty parts. -/
private def IsPartition (P : Finset (Finset X)) : Prop :=
  (∀ B ∈ P, B.Nonempty) ∧ (∀ x, ∃ B ∈ P, x ∈ B) ∧ ∀ B ∈ P, ∀ B' ∈ P, B ≠ B' → Disjoint B B'

omit [Fintype X] in
private theorem mem_erase_erase {P : Finset (Finset X)} {C D E : Finset X}
    (hE : E ∈ (P.erase C).erase D) : E ∈ P ∧ E ≠ C ∧ E ≠ D := by
  rw [Finset.mem_erase, Finset.mem_erase] at hE
  exact ⟨hE.2.2, hE.2.1, hE.1⟩

omit [Fintype X] in
private theorem isPartition_merge {P : Finset (Finset X)} (hP : IsPartition P) {C D : Finset X}
    (hC : C ∈ P) (hD : D ∈ P) :
    IsPartition (insert (C ∪ D) ((P.erase C).erase D)) := by
  obtain ⟨hne, hcov, hdis⟩ := hP
  refine ⟨?_, ?_, ?_⟩
  · intro B hB
    rw [Finset.mem_insert] at hB
    rcases hB with rfl | hB
    · exact (hne C hC).mono Finset.subset_union_left
    · exact hne B (mem_erase_erase hB).1
  · intro x
    obtain ⟨B, hB, hx⟩ := hcov x
    by_cases h1 : B = C
    · exact ⟨C ∪ D, Finset.mem_insert_self _ _, Finset.mem_union_left _ (h1 ▸ hx)⟩
    by_cases h2 : B = D
    · exact ⟨C ∪ D, Finset.mem_insert_self _ _, Finset.mem_union_right _ (h2 ▸ hx)⟩
    exact ⟨B, Finset.mem_insert_of_mem
      (Finset.mem_erase.mpr ⟨h2, Finset.mem_erase.mpr ⟨h1, hB⟩⟩), hx⟩
  · have hU : ∀ E, E ∈ (P.erase C).erase D → Disjoint (C ∪ D) E := by
      intro E hE
      obtain ⟨hE, h1, h2⟩ := mem_erase_erase hE
      exact Finset.disjoint_union_left.mpr
        ⟨hdis C hC E hE (Ne.symm h1), hdis D hD E hE (Ne.symm h2)⟩
    intro B hB B' hB' hne'
    rw [Finset.mem_insert] at hB hB'
    rcases hB with rfl | hB <;> rcases hB' with rfl | hB'
    · exact absurd rfl hne'
    · exact hU B' hB'
    · exact (hU B hB).symm
    · exact hdis B (mem_erase_erase hB).1 B' (mem_erase_erase hB').1 hne'

private theorem isPartition_of_upgmaReaches {d : X → X → ℝ} {P : Finset (Finset X)}
    {c : X → X → ℝ} (h : UpgmaReaches d P c) : IsPartition P := by
  induction h with
  | init =>
    refine ⟨?_, ?_, ?_⟩
    · intro B hB
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hB
      exact Finset.singleton_nonempty x
    · intro x
      exact ⟨{x}, Finset.mem_image_of_mem _ (Finset.mem_univ x), Finset.mem_singleton_self x⟩
    · intro B hB B' hB' hne
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hB
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hB'
      exact Finset.disjoint_singleton.mpr fun e => hne (e ▸ rfl)
  | step _ hC hD _ _ ih => exact isPartition_merge ih hC hD

/-- `B` is a weak cluster of `d`: two members are no farther apart than a member and an
outsider. -/
private def IsWeakCluster (d : X → X → ℝ) (B : Finset X) : Prop :=
  ∀ x ∈ B, ∀ y ∈ B, ∀ z, z ∉ B → d x y ≤ d x z

omit [Fintype X] [DecidableEq X] in
private theorem cross_eq {d : X → X → ℝ} (hd : IsUltrametric d) {C D : Finset X}
    (hC : IsWeakCluster d C) (hdis : Disjoint C D) {x x' y : X} (hx : x ∈ C) (hx' : x' ∈ C)
    (hy : y ∈ D) : d x y = d x' y := by
  have hyC : y ∉ C := Finset.disjoint_right.mp hdis hy
  have key : ∀ u v, u ∈ C → v ∈ C → d u y ≤ d v y := by
    intro u v hu hv
    have h2 : d u v ≤ d v y := by rw [hd.symm u v]; exact hC v hv u hu y hyC
    exact (hd.three_point u v y).trans (max_le h2 le_rfl)
  exact le_antisymm (key x x' hx hx') (key x' x hx' hx)

omit [Fintype X] [DecidableEq X] in
private theorem avgDist_eq {d : X → X → ℝ} (hd : IsUltrametric d) {C D : Finset X}
    (hC : IsWeakCluster d C) (hD : IsWeakCluster d D) (hdis : Disjoint C D) {x y : X}
    (hx : x ∈ C) (hy : y ∈ D) : avgDist d C D = d x y := by
  have hconst : ∀ u ∈ C, ∀ v ∈ D, d u v = d x y := by
    intro u hu v hv
    rw [cross_eq hd hC hdis hu hx hv, hd.symm x v, cross_eq hd hD hdis.symm hv hy hx,
      hd.symm y x]
  unfold avgDist
  rw [Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v hv => hconst u hu v hv]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hc : (C.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr ⟨x, hx⟩).ne'
  have hd' : (D.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr ⟨y, hy⟩).ne'
  field_simp

private theorem upgma_inv {d : X → X → ℝ} (hd : IsUltrametric d) {P : Finset (Finset X)}
    {c : X → X → ℝ} (h : UpgmaReaches d P c) :
    (∀ B ∈ P, IsWeakCluster d B) ∧ ∀ B ∈ P, ∀ x ∈ B, ∀ y ∈ B, c x y = d x y := by
  induction h with
  | init =>
    refine ⟨?_, ?_⟩
    · intro B hB x hx y hy z hz
      obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hB
      rw [Finset.mem_singleton] at hx hy hz
      subst hx hy
      rw [hd.self]
      exact (hd.pos _ _ (Ne.symm hz)).le
    · intro B hB x hx y hy
      obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hB
      rw [Finset.mem_singleton] at hx hy
      subst hx hy
      exact (hd.self _).symm
  | @step P c C D hreach hC hD hCD hmin ih =>
    obtain ⟨hw, hc⟩ := ih
    have hpart := isPartition_of_upgmaReaches hreach
    have hdisCD := hpart.2.2 C hC D hD hCD
    have havg : ∀ x ∈ C, ∀ y ∈ D, avgDist d C D = d x y := fun x hx y hy =>
      avgDist_eq hd (hw C hC) (hw D hD) hdisCD hx hy
    refine ⟨?_, ?_⟩
    · intro B hB
      rw [Finset.mem_insert] at hB
      rcases hB with rfl | hB
      · intro x hx y hy z hz
        obtain ⟨E, hE, hzE⟩ := hpart.2.1 z
        have hzC : z ∉ C := fun h => hz (Finset.mem_union_left _ h)
        have hzD : z ∉ D := fun h => hz (Finset.mem_union_right _ h)
        have hEC : C ≠ E := fun e => hzC (e ▸ hzE)
        have hED : D ≠ E := fun e => hzD (e ▸ hzE)
        rw [Finset.mem_union] at hx hy
        rcases hx with hx | hx <;> rcases hy with hy | hy
        · exact hw C hC x hx y hy z hzC
        · rw [← havg x hx y hy,
            ← avgDist_eq hd (hw C hC) (hw E hE) (hpart.2.2 C hC E hE hEC) hx hzE]
          exact hmin C hC E hE hEC
        · rw [hd.symm x y, ← havg y hy x hx,
            ← avgDist_eq hd (hw D hD) (hw E hE) (hpart.2.2 D hD E hE hED) hx hzE]
          exact hmin D hD E hE hED
        · exact hw D hD x hx y hy z hzD
      · exact hw B (mem_erase_erase hB).1
    · intro B hB x hx y hy
      rw [Finset.mem_insert] at hB
      rcases hB with rfl | hB
      · dsimp only
        split_ifs with hxy
        · rcases hxy with ⟨hx', hy'⟩ | ⟨hx', hy'⟩
          · exact havg x hx' y hy'
          · rw [hd.symm]; exact havg y hy' x hx'
        · rw [Finset.mem_union] at hx hy
          rcases hx with hx | hx <;> rcases hy with hy | hy
          · exact hc C hC x hx y hy
          · exact absurd (Or.inl ⟨hx, hy⟩) hxy
          · exact absurd (Or.inr ⟨hx, hy⟩) hxy
          · exact hc D hD x hx y hy
      · obtain ⟨hBP, hBC, hBD⟩ := mem_erase_erase hB
        have hxC : x ∉ C := Finset.disjoint_left.mp (hpart.2.2 B hBP C hC hBC) hx
        have hxD : x ∉ D := Finset.disjoint_left.mp (hpart.2.2 B hBP D hD hBD) hx
        dsimp only
        split_ifs with hxy
        · tauto
        · exact hc B hBP x hx y hy

/-- **UPGMA is exact on ultrametrics**: in every UPGMA run on an ultrametric, the recorded
height of two taxa in the same block is their distance. In particular a completed run (one
block) reconstructs `d`, i.e. the dated tree, exactly (Semple & Steel 2003, Section 7.2). -/
theorem upgma_exact {d : X → X → ℝ} (hd : IsUltrametric d) {P : Finset (Finset X)}
    {c : X → X → ℝ} (h : UpgmaReaches d P c) {B : Finset X} (hB : B ∈ P) {x y : X}
    (hx : x ∈ B) (hy : y ∈ B) : c x y = d x y := by
  exact (upgma_inv hd h).2 B hB x hx y hy

/-- UPGMA always completes: from the singletons it reaches the single block `univ`. -/
theorem exists_upgmaReaches_univ [Nonempty X] (d : X → X → ℝ) :
    ∃ c, UpgmaReaches d {Finset.univ} c := by
  have main : ∀ n (P : Finset (Finset X)) (c : X → X → ℝ), UpgmaReaches d P c → P.card = n →
      ∃ c', UpgmaReaches d {Finset.univ} c' := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro P c h hn
    have hpart := isPartition_of_upgmaReaches h
    obtain ⟨x₀⟩ := ‹Nonempty X›
    obtain ⟨B₀, hB₀, -⟩ := hpart.2.1 x₀
    by_cases h1 : P.card ≤ 1
    · have hall := Finset.card_le_one.mp h1
      have hB₀u : B₀ = Finset.univ := by
        ext x
        simp only [Finset.mem_univ, iff_true]
        obtain ⟨B, hB, hx⟩ := hpart.2.1 x
        exact hall B hB B₀ hB₀ ▸ hx
      have hP : P = {Finset.univ} := by
        ext B
        rw [Finset.mem_singleton]
        constructor
        · intro hB; rw [← hB₀u]; exact hall B hB B₀ hB₀
        · rintro rfl; exact hB₀u ▸ hB₀
      exact ⟨c, hP ▸ h⟩
    · obtain ⟨C, hC, D, hD, hCD⟩ := Finset.one_lt_card.mp (show 1 < P.card by omega)
      have hne : P.offDiag.Nonempty := ⟨(C, D), Finset.mem_offDiag.mpr ⟨hC, hD, hCD⟩⟩
      obtain ⟨p, hp, hmin⟩ := Finset.exists_min_image P.offDiag
        (fun p => avgDist d p.1 p.2) hne
      obtain ⟨hp1, hp2, hp12⟩ := Finset.mem_offDiag.mp hp
      have hstep := UpgmaReaches.step h hp1 hp2 hp12 fun E hE F hF hEF =>
        hmin (E, F) (Finset.mem_offDiag.mpr ⟨hE, hF, hEF⟩)
      have hnot : p.1 ∪ p.2 ∉ (P.erase p.1).erase p.2 := by
        intro hm
        obtain ⟨hE, hE1, -⟩ := mem_erase_erase hm
        obtain ⟨y, hy⟩ := hpart.1 p.1 hp1
        exact Finset.disjoint_left.mp (hpart.2.2 _ hE _ hp1 hE1)
          (Finset.mem_union_left _ hy) hy
      have hcard : (insert (p.1 ∪ p.2) ((P.erase p.1).erase p.2)).card + 1 = n := by
        rw [Finset.card_insert_of_notMem hnot,
          Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hp12, hp2⟩),
          Finset.card_erase_of_mem hp1]
        omega
      exact ih _ (by omega) _ _ hstep rfl
  exact main _ _ _ UpgmaReaches.init rfl

end Ultrametric

/-! ### Rooted triplets, quartets and BUILD -/

section Triplets

variable {α : Type*} [DecidableEq α]

/-- A **rooted triplet** `xy|z`: `x` and `y` are closer to each other than to `z`. -/
structure Triplet (α : Type*) where
  /-- The first taxon of the cherry. -/
  x : α
  /-- The second taxon of the cherry. -/
  y : α
  /-- The outgroup. -/
  z : α

/-- The cluster system `H` **displays** the triplet `xy|z`: some cluster contains `x` and `y`
but not `z`. -/
def DisplaysTriplet (H : Finset (Finset α)) (t : Triplet α) : Prop :=
  ∃ C ∈ H, t.x ∈ C ∧ t.y ∈ C ∧ t.z ∉ C

/-- The **Aho graph** of the triplets `R` on `S'` (vertices `S'`, an edge `x y` for each
`xy|z ∈ R` with `x, y, z ∈ S'`) has a cut: a partition of `S'` into two nonempty parts with no
edge across, i.e. the graph is disconnected. -/
def HasAhoCut (R : Finset (Triplet α)) (S' : Finset α) : Prop :=
  ∃ K ⊆ S', K.Nonempty ∧ (S' \ K).Nonempty ∧
    ∀ t ∈ R, t.x ∈ S' → t.y ∈ S' → t.z ∈ S' → (t.x ∈ K ↔ t.y ∈ K)

/-- A member of a hierarchy meeting both parts of a split member contains it. -/
private theorem subset_of_meets {H : Finset (Finset α)}
    (hlam : ∀ C ∈ H, ∀ D ∈ H, C ⊆ D ∨ D ⊆ C ∨ Disjoint C D) {E D₁ D₂ C : Finset α}
    (hE : E ∈ H) (h₁ : D₁ ∈ H) (h₂ : D₂ ∈ H) (hd : Disjoint D₁ D₂) (hu : D₁ ∪ D₂ = C)
    {u v : α} (hu₁ : u ∈ D₁) (hv₂ : v ∈ D₂) (huE : u ∈ E) (hvE : v ∈ E) : C ⊆ E := by
  have hsub : ∀ {D D' : Finset α} {w w' : α}, D ∈ H → Disjoint D D' → w ∈ D → w' ∈ D' →
      w ∈ E → w' ∈ E → D ⊆ E := by
    intro D D' w w' hD hdd hw hw' hwE hw'E
    rcases hlam E hE D hD with h | h | h
    · exact absurd (h hw'E) (Finset.disjoint_right.mp hdd hw')
    · exact h
    · exact absurd hw (Finset.disjoint_left.mp h hwE)
  rw [← hu]
  exact Finset.union_subset (hsub h₁ hd hu₁ hv₂ huE hvE) (hsub h₂ hd.symm hv₂ hu₁ hvE huE)

omit [DecidableEq α] in
private theorem DisplaysTriplet.mono {H H' : Finset (Finset α)} (hH : H ⊆ H') {t : Triplet α}
    (h : DisplaysTriplet H t) : DisplaysTriplet H' t := by
  obtain ⟨C, hC, hx, hy, hz⟩ := h
  exact ⟨C, hH hC, hx, hy, hz⟩

private theorem HasAhoCut.mono {R R' : Finset (Triplet α)} (hR : R' ⊆ R) {S' : Finset α}
    (h : HasAhoCut R S') : HasAhoCut R' S' := by
  obtain ⟨K, hK, hne, hne', hcut⟩ := h
  exact ⟨K, hK, hne, hne', fun t ht => hcut t (hR ht)⟩

private theorem subset_of_displaysTriplet {S : Finset α} {H H' : Finset (Finset α)}
    (hH : IsBinaryHierarchy S H) (hH' : IsBinaryHierarchy S H')
    (h : ∀ t : Triplet α, DisplaysTriplet H t → DisplaysTriplet H' t) : H ⊆ H' := by
  intro C hC
  obtain ⟨hS', hsub', -, hlam', hsplit'⟩ := hH'
  have hCS := (hH.2.1 C hC).2
  have hne : (H'.filter (C ⊆ ·)).Nonempty := ⟨S, Finset.mem_filter.mpr ⟨hS', hCS⟩⟩
  obtain ⟨C', hC', hmin⟩ := Finset.exists_min_image _ Finset.card hne
  rw [Finset.mem_filter] at hC'
  by_cases heq : C' = C
  · exact heq ▸ hC'.1
  exfalso
  have hlt : C ⊂ C' := Finset.ssubset_iff_subset_ne.mpr ⟨hC'.2, Ne.symm heq⟩
  obtain ⟨z, hzC', hzC⟩ := Finset.exists_of_ssubset hlt
  have hc : 1 < C'.card := by
    have := Finset.card_lt_card hlt
    have := (hH.2.1 C hC).1.card_pos
    omega
  obtain ⟨D₁, h₁, D₂, h₂, hd, hu⟩ := hsplit' C' hC'.1 hc
  have meet : ∀ D ∈ H', D ⊆ C' → D ≠ C' → ∃ x ∈ C, x ∉ D := by
    intro D hD hDC' hne'
    by_contra hall
    simp only [not_exists, not_and, not_not] at hall
    have := hmin D (Finset.mem_filter.mpr ⟨hD, hall⟩)
    have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hDC', hne'⟩)
    omega
  have hne₁ := (hsub' D₁ h₁).1
  have hne₂ := (hsub' D₂ h₂).1
  have hD₁ : D₁ ≠ C' := by
    intro e
    obtain ⟨w, hw⟩ := hne₂
    exact Finset.disjoint_left.mp hd (e ▸ hu ▸ Finset.mem_union_right _ hw) hw
  have hD₂ : D₂ ≠ C' := by
    intro e
    obtain ⟨w, hw⟩ := hne₁
    exact Finset.disjoint_left.mp hd hw (e ▸ hu ▸ Finset.mem_union_left _ hw)
  obtain ⟨y, hyC, hyD₁⟩ := meet D₁ h₁ (hu ▸ Finset.subset_union_left) hD₁
  obtain ⟨x, hxC, hxD₂⟩ := meet D₂ h₂ (hu ▸ Finset.subset_union_right) hD₂
  have hyD₂ : y ∈ D₂ :=
    (Finset.mem_union.mp (hu ▸ hC'.2 hyC)).resolve_left hyD₁
  have hxD₁ : x ∈ D₁ :=
    (Finset.mem_union.mp (hu ▸ hC'.2 hxC)).resolve_right hxD₂
  obtain ⟨E, hE, hxE, hyE, hzE⟩ := h ⟨x, y, z⟩ ⟨C, hC, hxC, hyC, hzC⟩
  exact hzE (subset_of_meets hlam' hE h₁ h₂ hd hu hxD₁ hyD₂ hxE hyE hzC')

/-- **A rooted binary tree is determined by its triplets** (Semple & Steel 2003, Theorem
6.4.1): two binary hierarchies on `S` displaying the same triplets are equal. -/
theorem eq_of_displaysTriplet_iff {S : Finset α} {H H' : Finset (Finset α)}
    (hH : IsBinaryHierarchy S H) (hH' : IsBinaryHierarchy S H')
    (h : ∀ t : Triplet α, DisplaysTriplet H t ↔ DisplaysTriplet H' t) : H = H' := by
  exact Finset.Subset.antisymm (subset_of_displaysTriplet hH hH' fun t => (h t).mp)
    (subset_of_displaysTriplet hH' hH fun t => (h t).mpr)

/-- **Correctness of BUILD** (Aho, Sagiv, Szymanski & Ullman 1981; Semple & Steel 2003,
Section 6.4): a set `R` of triplets on a nonempty `S`, none of the degenerate form `xx|x` (which
no tree displays and no cut detects), is displayed by a rooted binary phylogenetic tree on `S`
iff for every subset `S'` of at least two taxa the Aho graph of `R` on `S'` is disconnected.
BUILD splits along the components and recurses; the converse direction builds the tree this
way, splitting along any cut. -/
theorem build_spec {S : Finset α} (hS : S.Nonempty) (R : Finset (Triplet α))
    (hR : ∀ t ∈ R, t.x ∈ S ∧ t.y ∈ S ∧ t.z ∈ S ∧ (t.z ≠ t.x ∨ t.z ≠ t.y)) :
    (∃ H, IsBinaryHierarchy S H ∧ ∀ t ∈ R, DisplaysTriplet H t) ↔
      ∀ S' ⊆ S, 2 ≤ S'.card → HasAhoCut R S' := by
  constructor
  · rintro ⟨H, hH, hR'⟩ S' hS'S hcard
    obtain ⟨hS0, hsub, -, hlam, hsplit⟩ := hH
    have hne : (H.filter (S' ⊆ ·)).Nonempty := ⟨S, Finset.mem_filter.mpr ⟨hS0, hS'S⟩⟩
    obtain ⟨C, hC, hmin⟩ := Finset.exists_min_image _ Finset.card hne
    rw [Finset.mem_filter] at hC
    have hc : 1 < C.card := by have := Finset.card_le_card hC.2; omega
    obtain ⟨D₁, h₁, D₂, h₂, hd, hu⟩ := hsplit C hC.1 hc
    have notsub : ∀ D ∈ H, D ⊆ C → D ≠ C → ∃ x ∈ S', x ∉ D := by
      intro D hD hDC hne'
      by_contra hall
      simp only [not_exists, not_and, not_not] at hall
      have := hmin D (Finset.mem_filter.mpr ⟨hD, hall⟩)
      have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hDC, hne'⟩)
      omega
    have hne₁ := (hsub D₁ h₁).1
    have hne₂ := (hsub D₂ h₂).1
    have hD₁ : D₁ ≠ C := by
      intro e
      obtain ⟨w, hw⟩ := hne₂
      exact Finset.disjoint_left.mp hd (e ▸ hu ▸ Finset.mem_union_right _ hw) hw
    have hD₂ : D₂ ≠ C := by
      intro e
      obtain ⟨w, hw⟩ := hne₁
      exact Finset.disjoint_left.mp hd hw (e ▸ hu ▸ Finset.mem_union_left _ hw)
    have side : ∀ {w}, w ∈ S' → w ∈ D₁ ∨ w ∈ D₂ := fun hw =>
      Finset.mem_union.mp (hu ▸ hC.2 hw)
    refine ⟨S' ∩ D₁, Finset.inter_subset_left, ?_, ?_, ?_⟩
    · obtain ⟨x, hx, hxD₂⟩ := notsub D₂ h₂ (hu ▸ Finset.subset_union_right) hD₂
      exact ⟨x, Finset.mem_inter.mpr ⟨hx, (side hx).resolve_right hxD₂⟩⟩
    · obtain ⟨x, hx, hxD₁⟩ := notsub D₁ h₁ (hu ▸ Finset.subset_union_left) hD₁
      exact ⟨x, Finset.mem_sdiff.mpr ⟨hx, fun h => hxD₁ (Finset.mem_inter.mp h).2⟩⟩
    · intro t ht hx hy hz
      simp only [Finset.mem_inter, hx, hy, true_and]
      obtain ⟨E, hE, hxE, hyE, hzE⟩ := hR' t ht
      by_contra hne'
      rcases side hx with hx₁ | hx₂ <;> rcases side hy with hy₁ | hy₂
      · exact hne' (iff_of_true hx₁ hy₁)
      · exact hzE (subset_of_meets hlam hE h₁ h₂ hd hu hx₁ hy₂ hxE hyE (hC.2 hz))
      · exact hzE (subset_of_meets hlam hE h₁ h₂ hd hu hy₁ hx₂ hyE hxE (hC.2 hz))
      · exact hne' (iff_of_false (Finset.disjoint_right.mp hd hx₂)
          (Finset.disjoint_right.mp hd hy₂))
  intro hcut
  suffices ∀ n (S : Finset α) (R : Finset (Triplet α)), S.card = n → S.Nonempty →
      (∀ t ∈ R, t.x ∈ S ∧ t.y ∈ S ∧ t.z ∈ S ∧ (t.z ≠ t.x ∨ t.z ≠ t.y)) →
      (∀ S' ⊆ S, 2 ≤ S'.card → HasAhoCut R S') →
      ∃ H, IsBinaryHierarchy S H ∧ ∀ t ∈ R, DisplaysTriplet H t from this _ S R rfl hS hR hcut
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S R hn hS hR hcut
  by_cases h1 : 1 < S.card
  · obtain ⟨K, hKS, hKne, hSKne, hK⟩ := hcut S le_rfl h1
    have hd : Disjoint K (S \ K) := Finset.disjoint_sdiff
    have hu : K ∪ (S \ K) = S := Finset.union_sdiff_of_subset hKS
    have hcu : S.card = K.card + (S \ K).card := by
      rw [← Finset.card_union_of_disjoint hd, hu]
    have hc₁ : K.card < n := by have := hSKne.card_pos; omega
    have hc₂ : (S \ K).card < n := by have := hKne.card_pos; omega
    have recur : ∀ D, D ⊆ S → D.card < n → D.Nonempty → ∃ H, IsBinaryHierarchy D H ∧
        ∀ t ∈ R, t.x ∈ D → t.y ∈ D → t.z ∈ D → DisplaysTriplet H t := by
      intro D hDS hDn hDne
      obtain ⟨H, hH, hdisp⟩ := ih _ hDn D (R.filter fun t => t.x ∈ D ∧ t.y ∈ D ∧ t.z ∈ D)
        rfl hDne (fun t ht => by
          obtain ⟨-, hx, hy, hz⟩ := Finset.mem_filter.mp ht
          exact ⟨hx, hy, hz, (hR t (Finset.mem_filter.mp ht).1).2.2.2⟩)
        (fun S' hS' h2 => (hcut S' (hS'.trans hDS) h2).mono (Finset.filter_subset _ _))
      exact ⟨H, hH, fun t ht hx hy hz => hdisp t (Finset.mem_filter.mpr ⟨ht, hx, hy, hz⟩)⟩
    obtain ⟨H₁, hH₁, hd₁⟩ := recur K hKS hc₁ hKne
    obtain ⟨H₂, hH₂, hd₂⟩ := recur (S \ K) Finset.sdiff_subset hc₂ hSKne
    refine ⟨insert S (H₁ ∪ H₂), isBinaryHierarchy_combine hH₁ hH₂ hd hu, fun t ht => ?_⟩
    have hsub₁ : H₁ ⊆ insert S (H₁ ∪ H₂) := fun C hC =>
      Finset.mem_insert_of_mem (Finset.mem_union_left _ hC)
    have hsub₂ : H₂ ⊆ insert S (H₁ ∪ H₂) := fun C hC =>
      Finset.mem_insert_of_mem (Finset.mem_union_right _ hC)
    obtain ⟨hx, hy, hz, -⟩ := hR t ht
    have hxy := hK t ht hx hy hz
    by_cases hxK : t.x ∈ K
    · have hyK := hxy.mp hxK
      by_cases hzK : t.z ∈ K
      · exact (hd₁ t ht hxK hyK hzK).mono hsub₁
      · exact ⟨K, hsub₁ hH₁.1, hxK, hyK, hzK⟩
    · have hyK : t.y ∉ K := fun h => hxK (hxy.mpr h)
      have hx' : t.x ∈ S \ K := Finset.mem_sdiff.mpr ⟨hx, hxK⟩
      have hy' : t.y ∈ S \ K := Finset.mem_sdiff.mpr ⟨hy, hyK⟩
      by_cases hzK : t.z ∈ K
      · exact ⟨S \ K, hsub₂ hH₂.1, hx', hy', fun h => (Finset.mem_sdiff.mp h).2 hzK⟩
      · exact (hd₂ t ht hx' hy' (Finset.mem_sdiff.mpr ⟨hz, hzK⟩)).mono hsub₂
  · obtain ⟨a, rfl⟩ : ∃ a, S = {a} := by
      rw [← Finset.card_eq_one]
      have := hS.card_pos; omega
    refine ⟨{{a}}, isBinaryHierarchy_singleton a, fun t ht => ?_⟩
    obtain ⟨hx, hy, hz, hne⟩ := hR t ht
    rw [Finset.mem_singleton] at hx hy hz
    rcases hne with hne | hne
    · exact absurd (hz.trans hx.symm) hne
    · exact absurd (hz.trans hy.symm) hne

end Triplets

section Quartets

variable {X : Type} [Fintype X] [DecidableEq X]

/-- `T` **displays the quartet** `xy|zw`: some edge split of `T` has `x, y` on one side and
`z, w` on the other. -/
def DisplaysQuartet (T : UnrootedBinaryTree X) (x y z w : X) : Prop :=
  ∃ A ∈ edgeSplits T, x ∈ A ∧ y ∈ A ∧ z ∉ A ∧ w ∉ A

/-- **An unrooted binary tree is determined by its quartets** (Semple & Steel 2003, Corollary
6.3.8): two trees displaying the same quartets are isomorphic. Already the quartets containing
the taxon `a` suffice; they are the rooted triplets seen from `a`. -/
theorem iso_of_displaysQuartet_iff {T T' : UnrootedBinaryTree X} (a : X)
    (h : ∀ x y z, DisplaysQuartet T x y z a ↔ DisplaysQuartet T' x y z a) : T.Iso T' := by
  have key : ∀ (U : UnrootedBinaryTree X) (t : Triplet X),
      DisplaysTriplet (clusterSet U a) t ↔ DisplaysQuartet U t.x t.y t.z a := by
    intro U t
    rw [DisplaysQuartet, ← splitSet_eq_edgeSplits U a]
    constructor
    · rintro ⟨C, hC, hx, hy, hz⟩
      exact ⟨C, Finset.mem_union_left _ hC, hx, hy, hz, notMem_of_mem_clusterSet U a hC⟩
    · rintro ⟨A, hA, hx, hy, hz, ha⟩
      simp only [splitSet, Finset.mem_union, Finset.mem_image] at hA
      rcases hA with hA | ⟨C, hC, rfl⟩
      · exact ⟨A, hA, hx, hy, hz⟩
      · exact absurd (by simpa using ha) (notMem_of_mem_clusterSet U a hC)
  apply iso_of_clusterSet_eq a
  exact eq_of_displaysTriplet_iff (isBinaryHierarchy_clusterSet T a)
    (isBinaryHierarchy_clusterSet T' a) fun t => by rw [key, key]; exact h _ _ _

end Quartets

end Cslib.Bioinformatics.Phylogenetics.Splits
