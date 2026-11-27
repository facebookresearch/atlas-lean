/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Topology.Category.TopCat.Embedding.ClosedEmbedding
public import Mathlib.CategoryTheory.Types.Monomorphisms
public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition

/-!
# Closed embeddings are stable under transfinite composition in `TopCat`

Exact-pin transfinite-composition stability for `TopCat.closedEmbeddings`,
independently of cobase change. Provides the comparison
`closedEmbeddings ≤ inverseImage monomorphisms`, the colimit-leg auxiliary
theorem, and `IsStableUnderTransfiniteComposition` via
`Types.FilteredColimit.isColimit_eq_iff'`, `TopCat.isClosed_iff_of_isColimit`,
`MorphismProperty.transfiniteCompositionsOfShape_le`, `SuccOrder.limitRecOn`,
and the `TransfiniteCompositionOfShape.ici/iic/isColimitOfIsWellOrderContinuous`
APIs.
-/

@[expose] public section

universe v u

open CategoryTheory Limits Topology

namespace TopCat

lemma closedEmbeddings_le_inverseImage_monomorphisms :
    closedEmbeddings.{u} ≤
      (MorphismProperty.monomorphisms (Type u)).inverseImage (forget TopCat.{u}) :=
  fun _ _ f hf => by
    simpa [MorphismProperty.monomorphisms.iff, CategoryTheory.mono_iff_injective] using hf.injective

variable {J : Type v} [LinearOrder J]

instance : CategoryTheory.Limits.PreservesWellOrderContinuousOfShape J (forget TopCat.{u}) where

private lemma isClosedEmbedding_of_isIso {X Y : TopCat.{u}} (f : X ⟶ Y) [IsIso f] :
    IsClosedEmbedding f :=
  (homeoOfIso (asIso f)).isClosedEmbedding

variable [OrderBot J]

private lemma isClosedEmbedding_of_transfiniteCompositionOfShape_aux
    {X : J ⥤ TopCat.{u}} {c : Cocone X} (hc : IsColimit c)
    (hX : ∀ (j : J), IsClosedEmbedding (X.map (homOfLE (bot_le : (⊥ : J) ≤ j))))
    (h' : ∀ ⦃j j' : J⦄ (f : j ⟶ j'), Function.Injective (X.map f)) :
    IsClosedEmbedding (c.ι.app (⊥ : J)) := by
  have inj (j : J) : Function.Injective (c.ι.app j) := fun x₁ x₂ h => by
    obtain ⟨k, g, hk⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff'
          (isColimitOfPreserves (forget TopCat.{u}) hc) _ _).1 h
    exact h' _ hk
  have closed {F : Set (X.obj ⊥)} (hF : IsClosed F) :
      IsClosed (c.ι.app ⊥ '' F) := by
    rw [isClosed_iff_of_isColimit c hc]
    intro j
    convert (hX j).isClosedMap _ hF
    ext x
    simp only [Set.mem_preimage, Set.mem_image, homOfLE_leOfHom]
    constructor
    · rintro ⟨y, hy, h⟩
      refine ⟨y, hy, inj _ ?_⟩
      rw [← h]
      exact
        ConcreteCategory.congr_hom
          ((forget TopCat.{u}).congr_map (c.w (homOfLE (bot_le : (⊥ : J) ≤ j)))) y
    · rintro ⟨y, hy, rfl⟩
      exact
        ⟨y, hy,
          ConcreteCategory.congr_hom
            ((forget TopCat.{u}).congr_map
                (c.w (homOfLE (bot_le : (⊥ : J) ≤ j))).symm) y⟩
  exact
    { eq_induced := by
        rw [TopologicalSpace.ext_iff_isClosed]
        intro F
        simp only [isClosed_induced_iff]
        constructor
        · intro hF
          exact ⟨c.ι.app ⊥ '' F, closed hF, (inj ⊥).preimage_image F⟩
        · rintro ⟨V, hV, rfl⟩
          exact IsClosed.preimage (by continuity) hV
      injective := inj ⊥
      isClosed_range := by simpa using closed isClosed_univ }

lemma isClosedEmbedding_of_transfiniteCompositionOfShape
    [WellFoundedLT J] [SuccOrder J] {X Y : TopCat.{u}} {f : X ⟶ Y}
    (hf : closedEmbeddings.{u}.TransfiniteCompositionOfShape J f) :
    IsClosedEmbedding f := by
  have inj : ∀ ⦃j j' : J⦄ (g : j ⟶ j'), Function.Injective (hf.F.map g) := by
    intro j j' g
    exact
      ((CategoryTheory.mono_iff_injective _).mp
        ((MorphismProperty.monomorphisms (Type u)).transfiniteCompositionsOfShape_le _ _
          ((((hf.ici j).iic ⟨j', leOfHom g⟩).ofLE
              closedEmbeddings_le_inverseImage_monomorphisms).map.mem)))
  simp only [← hf.fac, Functor.const_obj_obj, hom_comp, ContinuousMap.coe_comp]
  refine IsClosedEmbedding.comp
    (isClosedEmbedding_of_transfiniteCompositionOfShape_aux hf.isColimit (fun j => ?_) inj)
    (isClosedEmbedding_of_isIso _)
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
    obtain rfl := hj.eq_bot
    simpa using IsClosedEmbedding.id
  | succ j hj hj' =>
    rw [← homOfLE_comp (bot_le : (⊥ : J) ≤ j) (Order.le_succ j), Functor.map_comp]
    exact (hf.map_mem j hj).comp hj'
  | isSuccLimit j hj hj' =>
    let : OrderBot (Set.Iio j) :=
      { bot := ⟨⊥, hj.bot_lt⟩
        bot_le := fun ⟨_, _⟩ => bot_le }
    exact
      isClosedEmbedding_of_transfiniteCompositionOfShape_aux
        (hf.F.isColimitOfIsWellOrderContinuous j hj) (fun ⟨i, hi⟩ => hj' i hi)
        (fun _ _ g => inj (homOfLE (leOfHom g)))

instance : closedEmbeddings.{u}.IsStableUnderTransfiniteComposition.{v} where
  isStableUnderTransfiniteCompositionOfShape _ _ _ _ _ :=
    ⟨fun _ _ _ ⟨hf⟩ => isClosedEmbedding_of_transfiniteCompositionOfShape hf⟩

end TopCat
