/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
public import Mathlib.Topology.Maps.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-!
# Closed embeddings in `TopCat`

Morphism property `TopCat.closedEmbeddings` for closed embeddings, defined via
`Topology.IsClosedEmbedding` on the underlying map (`f.hom`). Provides
`IsMultiplicative`, `RespectsIso`, `IsStableUnderBaseChange`, and
`IsStableUnderCobaseChange` (pushout stability) via `IsClosedEmbedding`
adapters and `TopCat` (co)limit APIs.

Pushout stability is proved via the modern `Limits.Types` pushout APIs:
`pushoutCocone_inr_injective_of_isColimit` for injectivity,
`isPullback_of_isPushout` for the required preimage identification, and
`TopCat.isClosed_iff_of_isColimit` for closed images, finishing with
`IsClosedEmbedding.of_continuous_injective_isClosedMap`. The
`IsStableUnderCobaseChange` instance is oriented via `sq.flip`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Topology

namespace TopCat

/-- Morphism property of being a closed embedding in `TopCat`. -/
def closedEmbeddings : MorphismProperty TopCat.{u} :=
  fun _ _ f => IsClosedEmbedding f.hom

@[simp]
lemma closedEmbeddings_iff {X Y : TopCat.{u}} (f : X ⟶ Y) :
    closedEmbeddings f ↔ IsClosedEmbedding f.hom :=
  Iff.rfl

@[simp]
lemma mem_closedEmbeddings {X Y : TopCat.{u}} (f : X ⟶ Y) :
    closedEmbeddings f ↔ IsClosedEmbedding (f : X → Y) :=
  Iff.rfl

instance : closedEmbeddings.IsMultiplicative where
  id_mem _ := IsClosedEmbedding.id
  comp_mem _ _ hf hg := hg.comp hf

instance : closedEmbeddings.RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ f _ =>
    (TopCat.homeoOfIso (asIso f)).isClosedEmbedding

private lemma fst_isClosedEmbedding_of_right {X Y S : TopCat.{u}} (f : X ⟶ S)
    {g : Y ⟶ S} (hg : IsClosedEmbedding g.hom) :
    IsClosedEmbedding (pullback.fst f g).hom := by
  refine ⟨fst_isEmbedding_of_right f hg.isEmbedding, ?_⟩
  have h_range : Set.range (pullback.fst f g) = f.hom ⁻¹' Set.range g.hom := by
    ext x
    simp only [pullback_fst_range, Set.mem_preimage, Set.mem_range]
    constructor
    · rintro ⟨y, hxy⟩
      exact ⟨y, hxy.symm⟩
    · rintro ⟨y, hxy⟩
      exact ⟨y, hxy.symm⟩
  rw [h_range]
  exact hg.isClosed_range.preimage f.hom.continuous

instance : closedEmbeddings.IsStableUnderBaseChange :=
  MorphismProperty.IsStableUnderBaseChange.mk' fun _ _ _ _ _ _ hg => by
    simpa [closedEmbeddings] using fst_isClosedEmbedding_of_right _ hg

section Pushout

variable {X₁ X₂ X₃ X₄ : TopCat.{u}} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃}
  {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}

-- Minimal modern exact-pin API: closed embeddings stable under cobase change.
-- Proof route: map TopCat pushout through `forget TopCat`;
-- obtain injectivity of the pushed-out leg from
-- `Limits.Types.pushoutCocone_inr_injective_of_isColimit`;
-- identify required preimage/image using `Limits.Types.isPullback_of_isPushout`;
-- prove closed images with `TopCat.isClosed_iff_of_isColimit`;
-- finish with `IsClosedEmbedding.of_continuous_injective_isClosedMap`.
-- Instance orientation via `sq.flip`.

lemma isClosed_image_iff_of_isPushout (sq : IsPushout t l r b)
    (ht : IsClosedEmbedding t) (F : Set X₃) :
    IsClosed (b '' F) ↔ IsClosed F := by
  have hb : Function.Injective b := by
    have hMap : IsPushout ((forget TopCat).map t) ((forget TopCat).map l)
        ((forget TopCat).map r) ((forget TopCat).map b) :=
      sq.map (forget TopCat)
    exact CategoryTheory.Limits.Types.pushoutCocone_inr_injective_of_isColimit
      hMap.isColimit ht.injective
  constructor
  · intro hF
    have : b ⁻¹' (b '' F) = F := hb.preimage_image F
    rw [← this]
    exact IsClosed.preimage b.hom.continuous hF
  · intro hF
    have hMap : IsPushout ((forget TopCat).map t) ((forget TopCat).map l)
        ((forget TopCat).map r) ((forget TopCat).map b) :=
      sq.map (forget TopCat)
    have hPull : IsPullback ((forget TopCat).map t) ((forget TopCat).map l)
        ((forget TopCat).map r) ((forget TopCat).map b) :=
      CategoryTheory.Limits.Types.isPullback_of_isPushout hMap ht.injective
    have hw : ∀ s : X₁, r (t s) = b (l s) := fun s => by
      change (t ≫ r) s = (l ≫ b) s
      rw [sq.w]
    have h_eq_r : r ⁻¹' (b '' F) = t '' (l ⁻¹' F) := by
      ext x₂
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · rintro ⟨x₃, hx₃, h_eq⟩
        have h_eq' : ((forget TopCat).map r) x₂ = ((forget TopCat).map b) x₃ := h_eq.symm
        have hExists := (CategoryTheory.Limits.Types.pushoutCocone_inl_eq_inr_iff_of_isColimit
          hMap.isColimit ht.injective x₂ x₃).mp h_eq'
        obtain ⟨s, h1, h2⟩ := hExists
        exact ⟨s, by simpa [← h2] using hx₃, h1⟩
      · rintro ⟨s, hs, rfl⟩
        exact ⟨l s, hs, (hw s).symm⟩
    have h_eq_zero : (t ≫ r) ⁻¹' (b '' F) = l ⁻¹' F := by
      ext x₁
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · rintro ⟨x₃, hx₃, h_eq⟩
        have h_eq1 : r (t x₁) = b x₃ := h_eq.symm
        have h_eq2 : r (t x₁) = b (l x₁) := hw x₁
        have hb_eq : b (l x₁) = b x₃ := by rw [← h_eq2, h_eq1]
        have hl_eq : l x₁ = x₃ := hb hb_eq
        have hx' : l x₁ ∈ F := hl_eq.symm ▸ hx₃
        exact hx'
      · intro hx
        exact ⟨l x₁, hx, (hw x₁).symm⟩
    have hColim := sq.isColimit
    have h_transport : IsClosed (b '' F : Set X₄) ↔ IsClosed (b '' F : Set sq.cocone.pt) := by
      -- `sq.cocone.pt = X₄` definitionally
      rfl
    rw [h_transport, TopCat.isClosed_iff_of_isColimit sq.cocone hColim (b '' F)]
    intro j
    cases j with
    | none =>
      -- WalkingSpan.zero : avoid rewriting `h_app` under `ConcreteCategory.hom`;
      -- `h_app` via `condition_zero` would need `simpa [hinl] using h0` where `h0` is `True`,
      -- and rewriting the morphism makes the `Set.preimage` motive ill-typed at
      -- implicit transparency (heterogeneous cocone domains). Prove the required
      -- closed preimage after an explicit `change` to the concrete `t ≫ r`.
      change IsClosed ((t ≫ r) ⁻¹' (b '' F))
      rw [h_eq_zero]
      exact IsClosed.preimage l.hom.continuous hF
    | some x =>
      cases x with
      | left =>
        change IsClosed (r ⁻¹' (b '' F))
        rw [h_eq_r]
        rw [← ht.isClosed_iff_image_isClosed]
        exact IsClosed.preimage l.hom.continuous hF
      | right =>
        change IsClosed (b ⁻¹' (b '' F))
        have : b ⁻¹' (b '' F) = F := hb.preimage_image F
        rw [this]
        exact hF

lemma isClosedEmbedding_of_isPushout (sq : IsPushout t l r b)
    (ht : IsClosedEmbedding t) : IsClosedEmbedding b := by
  have hb : Function.Injective b := by
    have hMap : IsPushout ((forget TopCat).map t) ((forget TopCat).map l)
        ((forget TopCat).map r) ((forget TopCat).map b) :=
      sq.map (forget TopCat)
    exact CategoryTheory.Limits.Types.pushoutCocone_inr_injective_of_isColimit
      hMap.isColimit ht.injective
  refine IsClosedEmbedding.of_continuous_injective_isClosedMap
    b.hom.continuous hb ?_
  intro F hF
  exact (isClosed_image_iff_of_isPushout sq ht F).mpr hF

instance : closedEmbeddings.{u}.IsStableUnderCobaseChange where
  of_isPushout {A A' B B'} {f : A ⟶ A'} {g : A ⟶ B} {f' : B ⟶ B'} {g' : A' ⟶ B'}
      (sq : IsPushout g f f' g') (hf : closedEmbeddings f) : closedEmbeddings f' :=
    isClosedEmbedding_of_isPushout sq.flip hf

end Pushout

end TopCat
