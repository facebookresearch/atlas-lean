/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.SetTheory.Cardinal.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.Zorn
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Tactic.Group

/-!
# Cardinalities of maximal direct factors in infinite groups (Kourovka Notebook Problem 21.58)

Kourovka Notebook, Problem 21.58 (M. H. Hooshmand), marked solved in the 21st issue: we say that a
product `XY = {xy | x ∈ X, y ∈ Y}` of two subsets `X, Y` of a group `G` is direct if for every
`z ∈ XY` there are unique `x ∈ X`, `y ∈ Y` such that `z = xy`. Is there an infinite group `G` such
that every subset `A ⊆ G` satisfies the following property: all the maximal subsets `B` for which
the product `AB` is direct have the same cardinality?

The answer is no (M. I. Kabenyuk): by `existsInfiniteGroupStableFactors_refuted`, every infinite
group `G` has a subset `A` with two maximal subsets `B` for which `AB` is direct and whose
cardinalities differ. The proof finds such sets with at most four and at least five elements.

## Proof outline

* `AB` is direct exactly when no element `x⁻¹ y ≠ 1` with `x, y ∈ A` is of the form `b₂ b₁⁻¹`
  with `b₁, b₂ ∈ B`.
* Let `K ⊆ G` be finite, closed under inverses, and contain `1`. Well-order `G` so that every
  initial segment has fewer elements than `G`. Along this order, pick for each `g ∉ K` an element
  `x_g` such that neither `x_g` nor `x_g g` has a quotient in `K` with an element chosen earlier;
  this excludes fewer than `|G|` values. Then `A = {x_g, x_g g | g ∉ K}` satisfies
  `A⁻¹A = (G \ K) ∪ {1}` (Kabenyuk, Lemma 2, credited there to Ravsky). For this `A`, the
  product `AB` is direct exactly when `b₂ b₁⁻¹ ∈ K` for all `b₁, b₂ ∈ B`.
* Take five distinct elements `Q ⊆ G`, an element `a` outside the finite set
  `(QQ⁻¹)⁻¹(QQ⁻¹)`, and `K = {1, a, a⁻¹} ∪ QQ⁻¹`. A maximal `B ⊇ {1, a}` satisfies
  `B ⊆ K ∩ Ka ⊆ {1, a, a⁻¹, a²}`, so it has at most four elements. A maximal `B ⊇ Q` has at
  least five. Zorn's lemma gives both maximal sets.

Kabenyuk's proof uses the same reduction to a finite set `K` (Lemmas 1 and 2) but chooses `K`
through a case analysis on the orders of the elements of `G` (Sections 4-6); the set `K` above
works in every infinite group.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.DirectProductFactorCardinalityKourovka21Problem58Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 21.58 (M. H. Hooshmand). UnsolvedMath
record UM-00002567 (`KOU-21.58`), dataset ulamai/UnsolvedMath v1.8.0.

Maximal is Mathlib's `Maximal` for inclusion of subsets; cardinalities are `Cardinal.mk`. Groups are
taken in `Type`.
-/

/-- **Direct product of subsets.** For subsets $A$ and $B$ of a group $G$, the product
$AB = \{ab \mid a \in A,\ b \in B\}$ is direct when each element of $AB$ is $ab$ for unique
$a \in A$ and $b \in B$: whenever $a_1 b_1 = a_2 b_2$ with $a_1, a_2 \in A$ and $b_1, b_2 \in B$,
we have $a_1 = a_2$ and $b_1 = b_2$. -/
def IsDirectProduct {G : Type} [Group G] (A B : Set G) : Prop :=
  ∀ a₁ ∈ A, ∀ a₂ ∈ A, ∀ b₁ ∈ B, ∀ b₂ ∈ B, a₁ * b₁ = a₂ * b₂ → a₁ = a₂ ∧ b₁ = b₂

/-- **Infinite groups with equicardinal maximal direct factors (Kourovka 21.58).** The statement
that there is an infinite group $G$ such that for every subset $A \subseteq G$, any two subsets
$B_1, B_2 \subseteq G$ that are maximal under inclusion among the subsets $B$ for which the
product $AB$ is direct have the same cardinality. -/
def existsInfiniteGroupStableFactors : Prop :=
  ∃ (G : Type) (_ : Group G), Infinite G ∧ ∀ A B₁ B₂ : Set G,
    Maximal (IsDirectProduct A) B₁ → Maximal (IsDirectProduct A) B₂ →
      Cardinal.mk B₁ = Cardinal.mk B₂

/-- In an infinite group, a finite set `K` closed under inverses meets the quotients `x⁻¹ * y` of
some set `A` only in quotients with `x = y`, while every element outside `K` is such a quotient
(Kabenyuk, Lemma 2). The witnesses are chosen by well-founded recursion along a well-order of `G`
whose initial segments have fewer elements than `G`. -/
private theorem exists_inv_mul_eq_compl {G : Type} [Group G] [Infinite G] (K : Finset G)
    (hK : ∀ k ∈ K, k⁻¹ ∈ K) :
    ∃ A : Set G, (∀ x ∈ A, ∀ y ∈ A, x⁻¹ * y ∈ K → x = y) ∧
      ∀ g ∉ K, ∃ x ∈ A, ∃ y ∈ A, x⁻¹ * y = g := by
  obtain ⟨r, hr, hord⟩ := Cardinal.exists_ord_eq G
  have hG : Cardinal.aleph0 ≤ Cardinal.mk G := Cardinal.aleph0_le_mk G
  have hsmall (g : G) : Cardinal.mk {h // r h g} < Cardinal.mk G := by
    simpa using Cardinal.card_typein_lt g hord
  have hfin (α : Type) [Finite α] : Cardinal.mk α < Cardinal.mk G :=
    (Cardinal.lt_aleph0_of_finite α).trans_le hG
  -- At step `g`, fewer than `#G` values are forbidden for the new witness.
  have hex (g : G) (IH : ∀ h, r h g → G) : ∃ x : G, ∀ h (hh : r h g), ∀ k ∈ K, ∀ b c : Bool,
      x ≠ IH h hh * (if b then h else 1) * k⁻¹ * (if c then g⁻¹ else 1) := by
    let f : {h // r h g} × K × Bool × Bool → G := fun p =>
      IH p.1.1 p.1.2 * (if p.2.2.1 then p.1.1 else 1) * (p.2.1 : G)⁻¹ *
        (if p.2.2.2 then g⁻¹ else 1)
    have hlt : Cardinal.mk (Set.range f) < Cardinal.mk G := by
      refine Cardinal.mk_range_le.trans_lt ?_
      simp only [Cardinal.mk_prod, Cardinal.lift_id]
      exact Cardinal.mul_lt_of_lt hG (hsmall g) (Cardinal.mul_lt_of_lt hG (hfin K)
        (Cardinal.mul_lt_of_lt hG (hfin Bool) (hfin Bool)))
    obtain ⟨x, hx⟩ : ∃ x, x ∉ Set.range f := by
      by_contra! h
      rw [Set.eq_univ_of_forall h, Cardinal.mk_univ] at hlt
      exact hlt.false
    exact ⟨x, fun h hh k hk b c hxe => hx ⟨(⟨h, hh⟩, ⟨k, hk⟩, b, c), hxe.symm⟩⟩
  let W : G → G := hr.wf.fix fun g IH => Classical.choose (hex g IH)
  have hW (g : G) : ∀ h (hh : r h g), ∀ k ∈ K, ∀ b c : Bool,
      W g ≠ W h * (if b then h else 1) * k⁻¹ * (if c then g⁻¹ else 1) := by
    have e : W g = Classical.choose (hex g fun h _ => W h) := hr.wf.fix_eq _ g
    rw [e]
    exact Classical.choose_spec (hex g fun h _ => W h)
  -- The two elements chosen at step `g` and those chosen at an earlier step `h` have no quotient
  -- in `K`.
  have hfar (g h : G) (hhg : r h g) (x y : G) (hx : x = W g ∨ x = W g * g)
      (hy : y = W h ∨ y = W h * h) : x⁻¹ * y ∉ K := by
    intro hk
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact hW g h hhg _ hk false false (by simp)
    · exact hW g h hhg _ hk true false (by simp only [Bool.false_eq_true, ↓reduceIte]; group)
    · exact hW g h hhg _ hk false true (by simp only [Bool.false_eq_true, ↓reduceIte]; group)
    · exact hW g h hhg _ hk true true (by simp only [↓reduceIte]; group)
  refine ⟨{y | ∃ g ∉ K, y = W g ∨ y = W g * g}, ?_, fun g hg =>
    ⟨W g, ⟨g, hg, .inl rfl⟩, W g * g, ⟨g, hg, .inr rfl⟩, by group⟩⟩
  rintro x ⟨g, hg, hx⟩ y ⟨h, hh, hy⟩ hxy
  rcases trichotomous_of r h g with hhg | rfl | hgh
  · exact absurd hxy (hfar g h hhg x y hx hy)
  · rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · exact absurd (by simpa using hxy) hg
    · exact absurd (by simpa using hK _ hxy) hg
    · rfl
  · exact absurd (by simpa using hK _ hxy) (hfar h g hgh y x hy hx)

/-- Every infinite group has a subset `A` with two maximal subsets `B` for which `AB` is direct and
whose cardinalities differ (Kabenyuk, Section 6, Theorem). -/
private theorem exists_maximal_isDirectProduct_mk_ne (G : Type) [Group G] [Infinite G] :
    ∃ A B₁ B₂ : Set G, Maximal (IsDirectProduct A) B₁ ∧ Maximal (IsDirectProduct A) B₂ ∧
      Cardinal.mk B₁ ≠ Cardinal.mk B₂ := by
  classical
  obtain ⟨Q, hQ⟩ := Infinite.exists_subset_card_eq G 5
  obtain ⟨P, hP⟩ : ∃ P : Finset G, ∀ x, x ∈ P ↔ ∃ q₁ ∈ Q, ∃ q₂ ∈ Q, q₁ * q₂⁻¹ = x := by
    refine ⟨(Q ×ˢ Q).image fun p => p.1 * p.2⁻¹, fun x => ?_⟩
    simp only [Finset.mem_image, Finset.mem_product, Prod.exists]
    constructor
    · rintro ⟨q₁, q₂, ⟨h₁, h₂⟩, rfl⟩
      exact ⟨q₁, h₁, q₂, h₂, rfl⟩
    · rintro ⟨q₁, h₁, q₂, h₂, rfl⟩
      exact ⟨q₁, q₂, ⟨h₁, h₂⟩, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : G, ∀ p₁ ∈ P, ∀ p₂ ∈ P, p₁⁻¹ * p₂ ≠ a := by
    obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset ((P ×ˢ P).image fun p => p.1⁻¹ * p.2)
    exact ⟨a, fun p₁ h₁ p₂ h₂ he =>
      ha (Finset.mem_image.2 ⟨(p₁, p₂), Finset.mem_product.2 ⟨h₁, h₂⟩, he⟩)⟩
  obtain ⟨K, hK⟩ : ∃ K : Finset G, ∀ x, x ∈ K ↔ x = 1 ∨ x = a ∨ x = a⁻¹ ∨ x ∈ P :=
    ⟨insert 1 (insert a (insert a⁻¹ P)), fun x => by simp⟩
  have h1K : (1 : G) ∈ K := (hK 1).2 (.inl rfl)
  have hKinv : ∀ k ∈ K, k⁻¹ ∈ K := by
    intro k hk
    rw [hK] at hk ⊢
    rcases hk with rfl | rfl | rfl | hk
    · exact .inl inv_one
    · exact .inr (.inr (.inl rfl))
    · exact .inr (.inl (inv_inv a))
    · obtain ⟨q₁, h₁, q₂, h₂, rfl⟩ := (hP k).1 hk
      exact .inr (.inr (.inr ((hP _).2 ⟨q₂, h₂, q₁, h₁, by group⟩)))
  obtain ⟨A, hA₁, hA₂⟩ := exists_inv_mul_eq_compl K hKinv
  -- For this `A`, the product `AB` is direct exactly when all quotients `b₂ * b₁⁻¹` lie in `K`.
  have hdir (B : Set G) (hB : ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₂ * b₁⁻¹ ∈ K) : IsDirectProduct A B := by
    intro a₁ ha₁ a₂ ha₂ b₁ hb₁ b₂ hb₂ he
    have hq : a₂⁻¹ * a₁ = b₂ * b₁⁻¹ :=
      calc a₂⁻¹ * a₁ = a₂⁻¹ * (a₁ * b₁) * b₁⁻¹ := by group
        _ = a₂⁻¹ * (a₂ * b₂) * b₁⁻¹ := by rw [he]
        _ = b₂ * b₁⁻¹ := by group
    obtain rfl := hA₁ a₂ ha₂ a₁ ha₁ (hq ▸ hB b₁ hb₁ b₂ hb₂)
    exact ⟨rfl, mul_left_cancel he⟩
  have hquot (B : Set G) (hB : IsDirectProduct A B) (b₁ : G) (hb₁ : b₁ ∈ B) (b₂ : G)
      (hb₂ : b₂ ∈ B) : b₂ * b₁⁻¹ ∈ K := by
    by_contra hk
    obtain ⟨x, hx, y, hy, hxy⟩ := hA₂ _ hk
    have he : y * b₁ = x * b₂ :=
      calc y * b₁ = x * (x⁻¹ * y) * b₁ := by group
        _ = x * (b₂ * b₁⁻¹) * b₁ := by rw [hxy]
        _ = x * b₂ := by group
    obtain ⟨-, rfl⟩ := hB y hy x hx b₁ hb₁ b₂ hb₂ he
    exact hk (by simpa using h1K)
  -- Zorn's lemma: every set `B₀` with `AB₀` direct lies in a maximal one.
  have hzorn (B₀ : Set G) (hB₀ : IsDirectProduct A B₀) :
      ∃ B, B₀ ⊆ B ∧ Maximal (IsDirectProduct A) B := by
    refine zorn_subset_nonempty {B | IsDirectProduct A B}
      (fun c hc hchain _ => ⟨⋃₀ c, ?_, fun s hs => Set.subset_sUnion_of_mem hs⟩) B₀ hB₀
    rintro a₁ ha₁ a₂ ha₂ b₁ ⟨s₁, hs₁, hb₁⟩ b₂ ⟨s₂, hs₂, hb₂⟩ he
    rcases hchain.total hs₁ hs₂ with h | h
    · exact hc hs₂ a₁ ha₁ a₂ ha₂ b₁ (h hb₁) b₂ hb₂ he
    · exact hc hs₁ a₁ ha₁ a₂ ha₂ b₁ hb₁ b₂ (h hb₂) he
  obtain ⟨B₁, h1a, hmax₁⟩ := hzorn {1, a} <| hdir _ fun b₁ hb₁ b₂ hb₂ => by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb₁ hb₂
    rw [hK]
    rcases hb₁ with rfl | rfl <;> rcases hb₂ with rfl | rfl <;> simp
  obtain ⟨B₂, hQB, hmax₂⟩ := hzorn Q <| hdir _ fun b₁ hb₁ b₂ hb₂ =>
    (hK _).2 (.inr (.inr (.inr ((hP _).2 ⟨b₂, hb₂, b₁, hb₁, rfl⟩))))
  refine ⟨A, B₁, B₂, hmax₁, hmax₂, ?_⟩
  -- Every element of `B₁` lies in `K ∩ K a ⊆ {1, a, a⁻¹, a * a}`.
  have hB₁ : B₁ ⊆ (({1, a, a⁻¹, a * a} : Finset G) : Set G) := by
    intro b hb
    have hb1 : b ∈ K := by simpa using hquot B₁ hmax₁.1 1 (h1a (by simp)) b hb
    have hba : b * a⁻¹ ∈ K := hquot B₁ hmax₁.1 a (h1a (by simp)) b hb
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    rw [hK] at hb1 hba
    rcases hb1 with h | h | h | hbP
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
    · rcases hba with h | h | h | hbaP
      · exact .inr (.inl (mul_inv_eq_one.1 h))
      · exact .inr (.inr (.inr (mul_inv_eq_iff_eq_mul.1 h)))
      · exact .inl (by simpa using h)
      · exact absurd (by group) (ha _ hbaP _ hbP)
  have c₁ : Cardinal.mk B₁ ≤ 4 :=
    calc Cardinal.mk B₁ ≤ Cardinal.mk (({1, a, a⁻¹, a * a} : Finset G) : Set G) :=
          Cardinal.mk_le_mk_of_subset hB₁
      _ = (({1, a, a⁻¹, a * a} : Finset G).card : Cardinal) := Cardinal.mk_coe_finset
      _ ≤ 4 := by exact_mod_cast Finset.card_le_four
  have c₂ : 5 ≤ Cardinal.mk B₂ :=
    calc (5 : Cardinal) = (Q.card : Cardinal) := by rw [hQ]; norm_cast
      _ = Cardinal.mk (Q : Set G) := Cardinal.mk_coe_finset.symm
      _ ≤ Cardinal.mk B₂ := Cardinal.mk_le_mk_of_subset hQB
  intro h
  have h54 : (5 : Cardinal) ≤ 4 := c₂.trans (h ▸ c₁)
  exact absurd h54 (by exact_mod_cast (by norm_num : ¬ (5 : ℕ) ≤ 4))

/--
**No infinite group has equicardinal maximal direct factors.** For every infinite group $G$ there
are subsets $A, B_1, B_2 \subseteq G$ such that $B_1$ and $B_2$ are both maximal under inclusion
among the subsets $B$ for which the product $AB$ is direct, but $B_1$ and $B_2$ have different
cardinalities. That is, the answer to Kourovka Problem 21.58 is negative.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 21.58 (M. H. Hooshmand); resolution: M. I.
Kabenyuk, Factors in infinite groups, preprint, arXiv:2602.22876 (2026); M. H. Hooshmand, preprint,
arXiv:2604.08724 (2026), Remark 1.16, Kabenyuk, Section 6, Theorem: every infinite group is
unstable, i.e. has a subset A whose maximal subsets U with AU direct do not all have the same
cardinality; Kourovka Notebook (21st issue), Problem 21.58: No, there are no such groups,
https://arxiv.org/abs/2602.22876.
-/
public theorem existsInfiniteGroupStableFactors_refuted : ¬ existsInfiniteGroupStableFactors := by
  rintro ⟨G, _, _, h⟩
  obtain ⟨A, B₁, B₂, h₁, h₂, hne⟩ := exists_maximal_isDirectProduct_mk_ne G
  exact hne (h A B₁ B₂ h₁ h₂)

end MathlibExt.GroupTheory.DirectProductFactorCardinalityKourovka21Problem58Wanted
