/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Phylogenetics.Splits

/-!
# Quartet support and determination by quartets

For an unrooted binary tree `T` on taxa `X` and a four-taxon set `q`, exactly one of the
three resolutions `A | q \ A` is *induced* by `T` (displayed as a quartet). Given
resolution frequencies `f q ρ` (e.g. estimated quartet frequencies), the total quartet
support of a tree is `quartetScore f T = ∑_q f q (T|q)`, summing the frequency of the
resolution `T` induces on each quartet. If on every quartet the resolution induced by a
species tree `S` is the strict plurality of `f` (`IsStrictPlurality f S`, no `> 1/2`
needed), then `S` is the unique maximizer of total quartet support up to isomorphism:
equal support forces the same induced quartet on every four-taxon set, hence an isomorphic
tree, and every non-isomorphic tree scores strictly less. In particular a binary tree is
determined by its quartets. On five taxa there are `15` unrooted binary trees.

## References

* C. Semple and M. Steel, *Phylogenetics*, Oxford University Press, 2003, Ch. 6 (quartets
  determine trees).
-/

@[expose] public section

open MathlibExt.Biology.Phylogenetics.UnrootedTreeCount

namespace Cslib.Bioinformatics.Phylogenetics.Splits

section QuartetSupport

variable {X : Type} [Fintype X] [DecidableEq X]

/-- The four-taxon subsets. -/
def quartets : Finset (Finset X) := Finset.univ.powersetCard 4

/-- The three resolutions `A | q \ A` of a four-taxon set `q`, each recorded as the pair
`{A, q \ A}` of its sides. For any `q` it is the family of the pairs `{A, q \ A}` with `A ⊆ q`
and `#A = 2`. -/
def resolutions (q : Finset X) : Finset (Finset (Finset X)) :=
  (q.powersetCard 2).image fun A => {A, q \ A}

/-- `T` **induces** the family `ρ` on the finite set `q`: some edge split `B` of `T` has
`q ∩ B ∈ ρ`. For a four-taxon set `q` and a resolution `ρ = {A, q \ A}` of `q`, this says that the
quartet tree `T|q` is `ρ`. -/
def Induces (T : UnrootedBinaryTree X) (q : Finset X) (ρ : Finset (Finset X)) : Prop :=
  ∃ B ∈ edgeSplits T, q ∩ B ∈ ρ

open Classical in
/-- The **total quartet support** `S(T) = ∑_q f_q(T|q)` of `T` for resolution frequencies
`f q ρ` (each four-taxon set contributes the frequency of the resolution `T` induces on it). -/
noncomputable def quartetScore (f : Finset X → Finset (Finset X) → ℝ)
    (T : UnrootedBinaryTree X) : ℝ :=
  ∑ q ∈ quartets, ∑ ρ ∈ (resolutions q).filter (Induces T q), f q ρ

/-- On every four-taxon set the resolution induced by `S` is the **strict plurality** of `f`:
it is strictly more frequent than each resolution `S` does not induce (no `> 1/2` needed). -/
def IsStrictPlurality (f : Finset X → Finset (Finset X) → ℝ) (S : UnrootedBinaryTree X) :
    Prop :=
  ∀ q ∈ quartets, ∀ ρ ∈ resolutions q, ∀ σ ∈ resolutions q,
    Induces S q ρ → ¬ Induces S q σ → f q σ < f q ρ

/-! ### Edge splits -/

/-- The complement of an edge split is an edge split. -/
theorem compl_mem_edgeSplits {T : UnrootedBinaryTree X} {B : Finset X}
    (hB : B ∈ edgeSplits T) : Bᶜ ∈ edgeSplits T := by
  simp only [edgeSplits, Finset.mem_image, Finset.mem_filter, Finset.mem_product,
    Finset.mem_univ, true_and] at hB ⊢
  obtain ⟨⟨p, v⟩, hpv, rfl⟩ := hB
  exact ⟨⟨v, p⟩, hpv.symm, (compl_edgeSide T hpv).symm⟩

/-- Every cluster seen from a leaf is an edge split. -/
theorem mem_edgeSplits_of_mem_clusterSet {T : UnrootedBinaryTree X} {a : X} {C : Finset X}
    (hC : C ∈ clusterSet T a) : C ∈ edgeSplits T := by
  rw [← splitSet_eq_edgeSplits T a]
  exact Finset.mem_union_left _ hC

/-! ### Two-element sides of a four-element set -/

omit [Fintype X] in
private theorem card_sdiff_two {q A : Finset X} (hq : q.card = 4) (hA : A ⊆ q)
    (hA2 : A.card = 2) : (q \ A).card = 2 := by
  rw [Finset.card_sdiff_of_subset hA, hq, hA2]

omit [Fintype X] [DecidableEq X] in
private theorem eq_of_subset_of_card_two {A C : Finset X} (h : A ⊆ C) (hA : A.card = 2)
    (hC : C.card = 2) : A = C :=
  Finset.eq_of_subset_of_card_le h (by omega)

omit [Fintype X] in
/-- Two resolutions of a four-element set whose sides cross on all four intersections are
different; contrapositively, a vanishing intersection forces the same resolution. -/
private theorem pair_eq_of_inter {q A C : Finset X} (hq : q.card = 4) (hA : A ⊆ q)
    (hA2 : A.card = 2) (hC : C ⊆ q) (hC2 : C.card = 2)
    (h : Disjoint A C ∨ Disjoint A (q \ C) ∨ Disjoint (q \ A) C ∨ Disjoint (q \ A) (q \ C)) :
    ({A, q \ A} : Finset (Finset X)) = {C, q \ C} := by
  have hA' := card_sdiff_two hq hA hA2
  have hC' := card_sdiff_two hq hC hC2
  rcases h with h | h | h | h
  · -- `C ⊆ q \ A`
    have : C = q \ A := eq_of_subset_of_card_two
      (fun x hx => Finset.mem_sdiff.2 ⟨hC hx, Finset.disjoint_right.1 h hx⟩) hC2 hA'
    rw [this, Finset.sdiff_sdiff_eq_self hA, Finset.pair_comm]
  · -- `A ⊆ C`
    have : A = C := eq_of_subset_of_card_two (fun x hx => by
      by_contra hxC
      exact Finset.disjoint_left.1 h hx (Finset.mem_sdiff.2 ⟨hA hx, hxC⟩)) hA2 hC2
    rw [this]
  · -- `C ⊆ A`
    have : C = A := eq_of_subset_of_card_two (fun x hx => by
      by_contra hxA
      exact Finset.disjoint_right.1 h hx (Finset.mem_sdiff.2 ⟨hC hx, hxA⟩)) hC2 hA2
    rw [this]
  · -- `q \ C ⊆ A`, so `q \ C = A`
    have : q \ C = A := eq_of_subset_of_card_two (fun x hx => by
      by_contra hxA
      exact Finset.disjoint_left.1 h (Finset.mem_sdiff.2 ⟨(Finset.mem_sdiff.1 hx).1, hxA⟩) hx)
      hC' hA2
    rw [← this, Finset.sdiff_sdiff_eq_self hC, Finset.pair_comm]

/-! ### The induced quartet tree -/

omit [Fintype X] in
/-- Every resolution of `q` is a pair `{A, q \ A}` with `A` a two-element subset. -/
private theorem mem_resolutions {q : Finset X} {ρ : Finset (Finset X)} :
    ρ ∈ resolutions q ↔ ∃ A ∈ q.powersetCard 2, ρ = {A, q \ A} := by
  simp only [resolutions, Finset.mem_image]
  constructor
  · rintro ⟨A, hA, rfl⟩; exact ⟨A, hA, rfl⟩
  · rintro ⟨A, hA, rfl⟩; exact ⟨A, hA, rfl⟩


/-- A four-taxon set has exactly **three resolutions**. -/
theorem card_resolutions {q : Finset X} (hq : q ∈ quartets) : (resolutions q).card = 3 := by
  have hq4 : q.card = 4 := (Finset.mem_powersetCard.1 hq).2
  obtain ⟨a, ha⟩ : q.Nonempty := Finset.card_pos.1 (by omega)
  have key : resolutions q = (q.erase a).image fun y => {{a, y}, q \ {a, y}} := by
    ext ρ
    rw [mem_resolutions, Finset.mem_image]
    constructor
    · rintro ⟨A, hA, rfl⟩
      obtain ⟨hAq, hA2⟩ := Finset.mem_powersetCard.1 hA
      by_cases haA : a ∈ A
      · obtain ⟨y, hyA, hya⟩ : ∃ y ∈ A, y ≠ a := by
          by_contra h
          push Not at h
          have : A ⊆ {a} := fun y hy => Finset.mem_singleton.2 (h y hy)
          have := Finset.card_le_card this
          simp at this; omega
        have hAeq : A = {a, y} := (Finset.eq_of_subset_of_card_le (by
          intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl <;> assumption) (by rw [hA2, Finset.card_pair hya.symm])).symm
        exact ⟨y, Finset.mem_erase.2 ⟨hya, hAq hyA⟩, by rw [hAeq]⟩
      · have haq' : a ∈ q \ A := Finset.mem_sdiff.2 ⟨ha, haA⟩
        have hq2 : (q \ A).card = 2 := card_sdiff_two hq4 hAq hA2
        obtain ⟨y, hyA, hya⟩ : ∃ y ∈ q \ A, y ≠ a := by
          by_contra h
          push Not at h
          have : q \ A ⊆ {a} := fun y hy => Finset.mem_singleton.2 (h y hy)
          have := Finset.card_le_card this
          simp at this; omega
        have hAeq : q \ A = {a, y} := (Finset.eq_of_subset_of_card_le (by
          intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl <;> assumption) (by rw [hq2, Finset.card_pair hya.symm])).symm
        refine ⟨y, Finset.mem_erase.2 ⟨hya, (Finset.mem_sdiff.1 hyA).1⟩, ?_⟩
        rw [← hAeq, Finset.sdiff_sdiff_eq_self hAq, Finset.pair_comm]
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨hya, hyq⟩ := Finset.mem_erase.1 hy
      refine ⟨{a, y}, Finset.mem_powersetCard.2 ⟨?_, Finset.card_pair hya.symm⟩, rfl⟩
      intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl <;> assumption
  rw [key, Finset.card_image_of_injOn, Finset.card_erase_of_mem ha, hq4]
  intro y hy y' hy' hyy
  obtain ⟨hya, -⟩ := Finset.mem_erase.1 hy
  obtain ⟨hy'a, -⟩ := Finset.mem_erase.1 hy'
  simp only at hyy
  have hmem : ({a, y} : Finset X) ∈ ({{a, y'}, q \ {a, y'}} : Finset (Finset X)) := by
    rw [← hyy]; exact Finset.mem_insert_self _ _
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h
  · have : y ∈ ({a, y'} : Finset X) := h ▸ (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h' | h'
    · exact absurd h' hya
    · exact h'
  · exfalso
    have : a ∈ q \ {a, y'} := h ▸ (by simp)
    simp at this

/-- **An unrooted binary tree resolves every four-taxon set** (at least one induced quartet). -/
theorem exists_induces (T : UnrootedBinaryTree X) {q : Finset X} (hq : q ∈ quartets) :
    ∃ ρ ∈ resolutions q, Induces T q ρ := by
  have hq4 : q.card = 4 := (Finset.mem_powersetCard.1 hq).2
  obtain ⟨a, ha⟩ : q.Nonempty := Finset.card_pos.1 (by omega)
  set R := q.erase a with hR
  have hR3 : R.card = 3 := by rw [Finset.card_erase_of_mem ha, hq4]
  have hH := isBinaryHierarchy_clusterSet T a
  set H := clusterSet T a
  have hRS : R ⊆ Finset.univ.erase a := fun x hx =>
    Finset.mem_erase.2 ⟨(Finset.mem_erase.1 hx).1, Finset.mem_univ x⟩
  obtain ⟨C, hCmem, hCmin⟩ := Finset.exists_min_image (H.filter (R ⊆ ·)) Finset.card
    ⟨_, Finset.mem_filter.2 ⟨hH.1, hRS⟩⟩
  obtain ⟨hCH, hRC⟩ := Finset.mem_filter.1 hCmem
  have hC1 : 1 < C.card := by have := Finset.card_le_card hRC; omega
  obtain ⟨D₁, hD₁, D₂, hD₂, hdisj, hunion⟩ := hH.2.2.2.2 C hCH hC1
  have hD₁ne : D₁.Nonempty := (hH.2.1 D₁ hD₁).1
  have hD₂ne : D₂.Nonempty := (hH.2.1 D₂ hD₂).1
  -- neither part contains `R`
  have hnot : ∀ D ∈ H, D ⊆ C → D ≠ C → ¬ R ⊆ D := fun D hD hDC hne hRD => by
    have hlt : D.card < C.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hDC, hne⟩)
    have := hCmin D (Finset.mem_filter.2 ⟨hD, hRD⟩)
    omega
  have hD₁C : D₁ ⊆ C := hunion ▸ Finset.subset_union_left
  have hD₂C : D₂ ⊆ C := hunion ▸ Finset.subset_union_right
  have hD₁ne' : D₁ ≠ C := fun h => by
    obtain ⟨x, hx⟩ := hD₂ne
    exact Finset.disjoint_left.1 hdisj (h ▸ hD₂C hx) hx
  have hD₂ne' : D₂ ≠ C := fun h => by
    obtain ⟨x, hx⟩ := hD₁ne
    exact Finset.disjoint_left.1 hdisj hx (h ▸ hD₁C hx)
  have hsplit : (R ∩ D₁).card + (R ∩ D₂).card = 3 := by
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right hdisj)),
      ← Finset.inter_union_distrib_left, hunion, Finset.inter_eq_left.2 hRC, hR3]
  have h1 : (R ∩ D₁).card ≠ 3 := fun h => hnot D₁ hD₁ hD₁C hD₁ne'
    (Finset.inter_eq_left.1 (Finset.eq_of_subset_of_card_le Finset.inter_subset_left
      (by omega)))
  have h2 : (R ∩ D₂).card ≠ 3 := fun h => hnot D₂ hD₂ hD₂C hD₂ne'
    (Finset.inter_eq_left.1 (Finset.eq_of_subset_of_card_le Finset.inter_subset_left
      (by omega)))
  obtain ⟨D, hDH, hD2⟩ : ∃ D ∈ H, (R ∩ D).card = 2 := by
    by_cases h : (R ∩ D₁).card = 2
    · exact ⟨D₁, hD₁, h⟩
    · exact ⟨D₂, hD₂, by omega⟩
  have haD : a ∉ D := notMem_of_mem_clusterSet T a hDH
  have hqD : q ∩ D = R ∩ D := by
    ext x
    simp only [Finset.mem_inter, hR, Finset.mem_erase]
    constructor
    · rintro ⟨hxq, hxD⟩; exact ⟨⟨fun h => haD (h ▸ hxD), hxq⟩, hxD⟩
    · rintro ⟨⟨-, hxq⟩, hxD⟩; exact ⟨hxq, hxD⟩
  refine ⟨{q ∩ D, q \ (q ∩ D)}, mem_resolutions.2 ⟨q ∩ D, ?_, rfl⟩,
    D, mem_edgeSplits_of_mem_clusterSet hDH, by simp⟩
  exact Finset.mem_powersetCard.2 ⟨Finset.inter_subset_left, by rw [hqD, hD2]⟩

/-- **An unrooted binary tree induces at most one resolution of each four-taxon set**: two edge
splits are compatible. -/
theorem induces_unique (T : UnrootedBinaryTree X) {q : Finset X} (hq : q ∈ quartets)
    {ρ σ : Finset (Finset X)} (hρ : ρ ∈ resolutions q) (hσ : σ ∈ resolutions q)
    (hTρ : Induces T q ρ) (hTσ : Induces T q σ) : ρ = σ := by
  have hq4 : q.card = 4 := (Finset.mem_powersetCard.1 hq).2
  obtain ⟨A, hA, rfl⟩ := mem_resolutions.1 hρ
  obtain ⟨C, hC, rfl⟩ := mem_resolutions.1 hσ
  obtain ⟨hAq, hA2⟩ := Finset.mem_powersetCard.1 hA
  obtain ⟨hCq, hC2⟩ := Finset.mem_powersetCard.1 hC
  obtain ⟨B₁, hB₁, h₁⟩ := hTρ
  obtain ⟨B₂, hB₂, h₂⟩ := hTσ
  -- rewrite both resolutions through the actual traces `q ∩ Bᵢ`
  have key : ∀ {E : Finset X}, E ⊆ q → E.card = 2 → q ∩ B₁ ∈ ({E, q \ E} : Finset _) →
      ({E, q \ E} : Finset (Finset X)) = {q ∩ B₁, q \ (q ∩ B₁)} := by
    intro E hE hE2 h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h
    · rw [h]
    · rw [h, Finset.sdiff_sdiff_eq_self hE, Finset.pair_comm]
  have key2 : ∀ {E : Finset X}, E ⊆ q → E.card = 2 → q ∩ B₂ ∈ ({E, q \ E} : Finset _) →
      ({E, q \ E} : Finset (Finset X)) = {q ∩ B₂, q \ (q ∩ B₂)} := by
    intro E hE hE2 h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h
    · rw [h]
    · rw [h, Finset.sdiff_sdiff_eq_self hE, Finset.pair_comm]
  rw [key hAq hA2 h₁, key2 hCq hC2 h₂]
  have hcard : ∀ {E : Finset X}, E ⊆ q → E.card = 2 → q ∩ B₁ ∈ ({E, q \ E} : Finset _) →
      (q ∩ B₁).card = 2 := by
    intro E hE hE2 h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h
    · rw [h, hE2]
    · rw [h, card_sdiff_two hq4 hE hE2]
  have hcard2 : ∀ {E : Finset X}, E ⊆ q → E.card = 2 → q ∩ B₂ ∈ ({E, q \ E} : Finset _) →
      (q ∩ B₂).card = 2 := by
    intro E hE hE2 h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h
    · rw [h, hE2]
    · rw [h, card_sdiff_two hq4 hE hE2]
  refine pair_eq_of_inter hq4 Finset.inter_subset_left (hcard hAq hA2 h₁)
    Finset.inter_subset_left (hcard2 hCq hC2 h₂) ?_
  -- compatibility of the two edge splits, traced on `q`
  have hsd : ∀ B : Finset X, q \ (q ∩ B) = q ∩ Bᶜ := fun B => by
    ext x; simp [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_compl]
  rw [hsd, hsd]
  rcases compatible_of_mem_edgeSplits hB₁ hB₂ with h | h | h | h
  · exact Or.inl (Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right h))
  · exact Or.inr (Or.inl (Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right h)))
  · exact Or.inr (Or.inr (Or.inl (Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right h))))
  · exact Or.inr (Or.inr (Or.inr (Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right h))))

/-- The quartet tree `T|q` is well defined: exactly one resolution of `q` is induced; equivalently
the set of induced resolutions of `q` has exactly one element (`card_filter_induces`). -/
theorem existsUnique_induces (T : UnrootedBinaryTree X) {q : Finset X} (hq : q ∈ quartets) :
    ∃! ρ, ρ ∈ resolutions q ∧ Induces T q ρ := by
  obtain ⟨ρ, hρ, hT⟩ := exists_induces T hq
  exact ⟨ρ, ⟨hρ, hT⟩, fun σ ⟨hσ, hTσ⟩ => induces_unique T hq hσ hρ hTσ hT⟩

open Classical in
/-- The support of `T` on one four-taxon set is the frequency of the quartet tree `T|q`. -/
private theorem sum_filter_induces (f : Finset X → Finset (Finset X) → ℝ)
    (T : UnrootedBinaryTree X) {q : Finset X} (hq : q ∈ quartets) {ρ : Finset (Finset X)}
    (hρ : ρ ∈ resolutions q) (hT : Induces T q ρ) :
    ∑ σ ∈ (resolutions q).filter (Induces T q), f q σ = f q ρ := by
  rw [Finset.sum_eq_single_of_mem ρ (Finset.mem_filter.2 ⟨hρ, hT⟩)]
  intro σ hσ hne
  obtain ⟨hσr, hTσ⟩ := Finset.mem_filter.1 hσ
  exact absurd (induces_unique T hq hσr hρ hTσ hT) hne

open Classical in
/-- Per four-taxon set, the species tree's support dominates any tree's support, strictly when
the two quartet trees differ. -/
private theorem local_le {f : Finset X → Finset (Finset X) → ℝ} {S : UnrootedBinaryTree X}
    (hS : IsStrictPlurality f S) (T : UnrootedBinaryTree X) {q : Finset X} (hq : q ∈ quartets) :
    ∑ σ ∈ (resolutions q).filter (Induces T q), f q σ ≤
        ∑ σ ∈ (resolutions q).filter (Induces S q), f q σ ∧
      (∑ σ ∈ (resolutions q).filter (Induces T q), f q σ =
          ∑ σ ∈ (resolutions q).filter (Induces S q), f q σ →
        ∀ ρ ∈ resolutions q, (Induces T q ρ ↔ Induces S q ρ)) := by
  obtain ⟨ρT, hρT, hT⟩ := exists_induces T hq
  obtain ⟨ρS, hρS, hS'⟩ := exists_induces S hq
  rw [sum_filter_induces f T hq hρT hT, sum_filter_induces f S hq hρS hS']
  by_cases heq : ρT = ρS
  · subst heq
    refine ⟨le_rfl, fun _ ρ hρ => ⟨fun h => ?_, fun h => ?_⟩⟩
    · rw [induces_unique T hq hρ hρT h hT]; exact hS'
    · rw [induces_unique S hq hρ hρT h hS']; exact hT
  · have hnS : ¬ Induces S q ρT := fun h => heq (induces_unique S hq hρT hρS h hS')
    have hlt := hS q hq ρS hρS ρT hρT hS' hnS
    exact ⟨hlt.le, fun h => absurd h hlt.ne⟩

/-- **The species tree maximizes total quartet support**: under strict plurality on every
four-taxon set, `S(T) ≤ S(species tree)` for every unrooted binary tree `T`. -/
theorem quartetScore_le {f : Finset X → Finset (Finset X) → ℝ} {S : UnrootedBinaryTree X}
    (hS : IsStrictPlurality f S) (T : UnrootedBinaryTree X) :
    quartetScore f T ≤ quartetScore f S :=
  Finset.sum_le_sum fun _ hq => (local_le hS T hq).1

/-- Under strict plurality (`IsStrictPlurality f S`), a tree with the same total quartet support as
the species tree `S` induces the same quartet tree on every four-taxon set. -/
theorem induces_iff_of_quartetScore_eq {f : Finset X → Finset (Finset X) → ℝ}
    {S T : UnrootedBinaryTree X} (hS : IsStrictPlurality f S)
    (h : quartetScore f T = quartetScore f S) :
    ∀ q ∈ quartets, ∀ ρ ∈ resolutions q, (Induces T q ρ ↔ Induces S q ρ) := by
  classical
  intro q hq
  have hall := (Finset.sum_eq_sum_iff_of_le fun q hq => (local_le hS T hq).1).1 h
  exact (local_le hS T hq).2 (hall q hq)

/-- Displaying the quartet `xy|zw` (taxa `x, y` separated from `z, w`) is inducing the family
`{{x, y}, {z, w}}` on `{x, y, z, w}`, for `x` and `y` both distinct from `z` and `w`. For four
distinct taxa this family is the quartet resolution; for `x = y` and `z = w` it is not a resolution
of `{x, z}`. -/
theorem displaysQuartet_iff_induces (T : UnrootedBinaryTree X) {x y z w : X}
    (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z) (hyw : y ≠ w) :
    DisplaysQuartet T x y z w ↔ Induces T {x, y, z, w} {{x, y}, {z, w}} := by
  constructor
  · rintro ⟨A, hA, hx, hy, hz, hw⟩
    refine ⟨A, hA, ?_⟩
    have : ({x, y, z, w} : Finset X) ∩ A = {x, y} := by
      ext t
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨h | h | h | h, ht⟩
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd (h ▸ ht) hz
        · exact absurd (h ▸ ht) hw
      · rintro (h | h)
        · exact ⟨Or.inl h, h ▸ hx⟩
        · exact ⟨Or.inr (Or.inl h), h ▸ hy⟩
    rw [this]; exact Finset.mem_insert_self _ _
  · rintro ⟨B, hB, hqB⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hqB
    rcases hqB with h | h
    · have hxB : x ∈ B := (Finset.mem_inter.1 (h ▸ (by simp : x ∈ ({x, y} : Finset X)))).2
      have hyB : y ∈ B := (Finset.mem_inter.1 (h ▸ (by simp : y ∈ ({x, y} : Finset X)))).2
      have hzB : z ∉ B := fun hz => by
        have : z ∈ ({x, y, z, w} : Finset X) ∩ B := Finset.mem_inter.2 ⟨by simp, hz⟩
        rw [h] at this
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with h' | h' <;> [exact hxz h'.symm; exact hyz h'.symm]
      have hwB : w ∉ B := fun hw => by
        have : w ∈ ({x, y, z, w} : Finset X) ∩ B := Finset.mem_inter.2 ⟨by simp, hw⟩
        rw [h] at this
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with h' | h' <;> [exact hxw h'.symm; exact hyw h'.symm]
      exact ⟨B, hB, hxB, hyB, hzB, hwB⟩
    · have hzB : z ∈ B := (Finset.mem_inter.1 (h ▸ (by simp : z ∈ ({z, w} : Finset X)))).2
      have hwB : w ∈ B := (Finset.mem_inter.1 (h ▸ (by simp : w ∈ ({z, w} : Finset X)))).2
      have hxB : x ∉ B := fun hx => by
        have : x ∈ ({x, y, z, w} : Finset X) ∩ B := Finset.mem_inter.2 ⟨by simp, hx⟩
        rw [h] at this
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with h' | h' <;> [exact hxz h'; exact hxw h']
      have hyB : y ∉ B := fun hy => by
        have : y ∈ ({x, y, z, w} : Finset X) ∩ B := Finset.mem_inter.2 ⟨by simp, hy⟩
        rw [h] at this
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with h' | h' <;> [exact hyz h'; exact hyw h']
      exact ⟨Bᶜ, compl_mem_edgeSplits hB, Finset.mem_compl.2 hxB, Finset.mem_compl.2 hyB,
        fun h => (Finset.mem_compl.1 h) hzB, fun h => (Finset.mem_compl.1 h) hwB⟩

/-- Quartets with a repeated taxon are displayed by every unrooted binary tree or by none:
the answer is `x ≠ z ∧ x ≠ a ∧ y ≠ z ∧ y ≠ a`. -/
private theorem displaysQuartet_iff_of_not_distinct (T : UnrootedBinaryTree X) {x y z a : X}
    (hnd : ¬ (x ≠ y ∧ x ≠ z ∧ x ≠ a ∧ y ≠ z ∧ y ≠ a ∧ z ≠ a)) :
    DisplaysQuartet T x y z a ↔ (x ≠ z ∧ x ≠ a ∧ y ≠ z ∧ y ≠ a) := by
  constructor
  · rintro ⟨A, -, hx, hy, hz, ha⟩
    exact ⟨fun h => hz (h ▸ hx), fun h => ha (h ▸ hx), fun h => hz (h ▸ hy),
      fun h => ha (h ▸ hy)⟩
  · rintro ⟨hxz, hxa, hyz, hya⟩
    have hH := isBinaryHierarchy_clusterSet T a
    by_cases hxy : x = y
    · subst hxy
      have hx : x ∈ Finset.univ.erase a := Finset.mem_erase.2 ⟨hxa, Finset.mem_univ x⟩
      refine ⟨{x}, mem_edgeSplits_of_mem_clusterSet (hH.2.2.1 x hx), Finset.mem_singleton_self x,
        Finset.mem_singleton_self x, by simpa [eq_comm] using hxz, by simpa [eq_comm] using hxa⟩
    · have hza : z = a := by
        by_contra hza
        exact hnd ⟨hxy, hxz, hxa, hyz, hya, hza⟩
      subst hza
      refine ⟨Finset.univ.erase z, mem_edgeSplits_of_mem_clusterSet hH.1,
        Finset.mem_erase.2 ⟨hxa, Finset.mem_univ x⟩, Finset.mem_erase.2 ⟨hya, Finset.mem_univ y⟩,
        Finset.notMem_erase z _, Finset.notMem_erase z _⟩

/-- **An unrooted binary tree is determined by its induced quartet trees**: on a nonempty taxon
set, two trees inducing the same resolution on every four-taxon set are isomorphic. -/
theorem iso_of_induces_iff [Nonempty X] {S T : UnrootedBinaryTree X}
    (hind : ∀ q ∈ quartets, ∀ ρ ∈ resolutions q, (Induces T q ρ ↔ Induces S q ρ)) :
    T.Iso S := by
  obtain ⟨a⟩ := ‹Nonempty X›
  refine iso_of_displaysQuartet_iff a fun x y z => ?_
  by_cases hd : x ≠ y ∧ x ≠ z ∧ x ≠ a ∧ y ≠ z ∧ y ≠ a ∧ z ≠ a
  · obtain ⟨hxy, hxz, hxa, hyz, hya, hza⟩ := hd
    rw [displaysQuartet_iff_induces T hxz hxa hyz hya,
      displaysQuartet_iff_induces S hxz hxa hyz hya]
    have hq : ({x, y, z, a} : Finset X) ∈ quartets := by
      refine Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, ?_⟩
      rw [Finset.card_insert_of_notMem (by simp [hxy, hxz, hxa]),
        Finset.card_insert_of_notMem (by simp [hyz, hya]),
        Finset.card_pair hza]
    have hρ : ({{x, y}, {z, a}} : Finset (Finset X)) ∈ resolutions {x, y, z, a} := by
      refine mem_resolutions.2 ⟨{x, y}, Finset.mem_powersetCard.2 ⟨by
        intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht ⊢; tauto,
        Finset.card_pair hxy⟩, ?_⟩
      congr 1
      congr 1
      ext t
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (h | h)
        · exact ⟨Or.inr (Or.inr (Or.inl h)), by rintro (h' | h') <;> [exact hxz (h'.symm.trans h); exact hyz (h'.symm.trans h)]⟩
        · exact ⟨Or.inr (Or.inr (Or.inr h)), by rintro (h' | h') <;> [exact hxa (h'.symm.trans h); exact hya (h'.symm.trans h)]⟩
      · rintro ⟨h | h | h | h, hn⟩
        · exact absurd (Or.inl h) hn
        · exact absurd (Or.inr h) hn
        · exact Or.inl h
        · exact Or.inr h
    exact hind _ hq _ hρ
  · rw [displaysQuartet_iff_of_not_distinct T hd, displaysQuartet_iff_of_not_distinct S hd]

/-- **Equal total support forces the species topology**: on a nonempty taxon set, under strict
plurality, a binary tree whose total quartet support equals that of the species tree is
isomorphic to it. -/
theorem iso_of_quartetScore_eq [Nonempty X] {f : Finset X → Finset (Finset X) → ℝ}
    {S T : UnrootedBinaryTree X} (hS : IsStrictPlurality f S)
    (h : quartetScore f T = quartetScore f S) : T.Iso S :=
  iso_of_induces_iff (induces_iff_of_quartetScore_eq hS h)

/-- **Strict-plurality support maximization**: on a nonempty taxon set, under strict plurality
on every four-taxon set, every unrooted binary tree that is not isomorphic to the species tree has
strictly smaller total quartet support. -/
theorem quartetScore_lt_of_not_iso [Nonempty X] {f : Finset X → Finset (Finset X) → ℝ}
    {S T : UnrootedBinaryTree X} (hS : IsStrictPlurality f S) (hT : ¬ T.Iso S) :
    quartetScore f T < quartetScore f S :=
  lt_of_le_of_ne (quartetScore_le hS T) fun h => hT (iso_of_quartetScore_eq hS h)

/-! ### Acceptance, boundary and non-vacuity checks -/

open Classical in
/-- Exactly one resolution of each four-taxon set is induced. -/
theorem card_filter_induces (T : UnrootedBinaryTree X) {q : Finset X} (hq : q ∈ quartets) :
    ((resolutions q).filter (Induces T q)).card = 1 := by
  obtain ⟨ρ, ⟨hρ, hT⟩, huniq⟩ := existsUnique_induces T hq
  refine Finset.card_eq_one.2 ⟨ρ, Finset.ext fun σ => ?_⟩
  rw [Finset.mem_filter, Finset.mem_singleton]
  exact ⟨fun h => huniq σ h, fun h => h ▸ ⟨hρ, hT⟩⟩

end QuartetSupport

end Cslib.Bioinformatics.Phylogenetics.Splits
