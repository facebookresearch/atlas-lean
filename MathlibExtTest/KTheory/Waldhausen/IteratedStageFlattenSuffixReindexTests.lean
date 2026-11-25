/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.IteratedStageFlattenSuffixReindex

/-!
# Clients for the original appended-suffix flatten square

The original onefold maps act on every finite prefix length. These clients
retain both moving suffix endpoints, all original objects and morphisms,
and the original Cons coordinate transports.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace MathlibExtTest.KTheory.Waldhausen.IteratedStageFlattenSuffixReindexTests

open CategoryTheory.Waldhausen.SConstruction

variable (C : Type (max u v)) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- The full original appended operator retains its moving last coordinate. -/
theorem originalMovingCoordinates {r : ℕ} {a b : StageSimplexTuple r} (α : a ⟶ b)
    {x y z w : SimplexCategoryᵒᵖ} (h : x ⟶ y) (f : z ⟶ w) :
    eqToHom (stageTupleSnoc_cons x a z).symm ≫
        stageTupleSnocMap (stageTupleConsMap α h) f ≫
          eqToHom (stageTupleSnoc_cons y b w) =
      stageTupleConsMap (stageTupleSnocMap α f) h :=
  stageTupleSnocMap_cons_moving α h f

/-- Exactness of the original suffix operator is earned from its original charts. -/
theorem originalSingleExact {z w : SimplexCategoryᵒᵖ} (f : z ⟶ w) :
    (iteratedStageSingleReindex C f).IsWaldhausenExact :=
  iteratedStageSingleReindex_isWaldhausenExact C f

/-- Suffix composition retains the same original single-stage functors. -/
theorem originalSingleComposition {z w t : SimplexCategoryᵒᵖ}
    (f : z ⟶ w) (g : w ⟶ t) :
    iteratedStageSingleReindex C (f ≫ g) =
      iteratedStageSingleReindex C f ⋙ iteratedStageSingleReindex C g :=
  iteratedStageSingleReindex_comp C f g

/-- Every finite prefix length retains the original whole suffix square. -/
theorem originalSuffixSquare (r : ℕ) (a : StageSimplexTuple r)
    {z w : SimplexCategoryᵒᵖ} (f : z ⟶ w) :
    mapIteratedStage (iteratedStageSingleReindex_isWaldhausenExact C f)
        (stageTupleDegrees a) ⋙
        (iteratedStageTupleSnocFlattenEquivalence C a w).functor =
      (iteratedStageTupleSnocFlattenEquivalence C a z).functor ⋙
        reindexIteratedStage C (stageTupleSnocMap (𝟙 a) f) :=
  iteratedStageTupleSnocFlattenEquivalence_suffix C r a f

/-- At zero prefix length the actual nil carrier and the original suffix map remain. -/
theorem originalEmptyPrefix (a : StageSimplexTuple 0)
    {z w : SimplexCategoryᵒᵖ} (f : z ⟶ w) :
    mapIteratedStage (iteratedStageSingleReindex_isWaldhausenExact C f) [] ⋙
        (iteratedStageTupleSnocFlattenEquivalence C a w).functor =
      (iteratedStageTupleSnocFlattenEquivalence C a z).functor ⋙
        reindexIteratedStage C (stageTupleSnocMap (𝟙 a) f) :=
  iteratedStageTupleSnocFlattenEquivalence_suffix C 0 a f

/-- Every original object follows the same literal suffix and flattening maps. -/
theorem originalSuffixObject (r : ℕ) (a : StageSimplexTuple r)
    {z w : SimplexCategoryᵒᵖ} (f : z ⟶ w)
    (X : StageAtTuple (IteratedStage C [z.unop.len]) a) :
    (iteratedStageTupleSnocFlattenEquivalence C a w).functor.obj
        ((mapIteratedStage (iteratedStageSingleReindex_isWaldhausenExact C f)
          (stageTupleDegrees a)).obj X) =
      (reindexIteratedStage C (stageTupleSnocMap (𝟙 a) f)).obj
        ((iteratedStageTupleSnocFlattenEquivalence C a z).functor.obj X) :=
  iteratedStageTupleSnocFlattenEquivalence_suffix_obj C r a f X

/-- The full original morphism maps retain their actual endpoint transports. -/
theorem originalSuffixMorphism (r : ℕ) (a : StageSimplexTuple r)
    {z w : SimplexCategoryᵒᵖ} (f : z ⟶ w)
    {X Y : StageAtTuple (IteratedStage C [z.unop.len]) a} (h : X ⟶ Y) :
    HEq ((iteratedStageTupleSnocFlattenEquivalence C a w).functor.map
        ((mapIteratedStage (iteratedStageSingleReindex_isWaldhausenExact C f)
          (stageTupleDegrees a)).map h))
      ((reindexIteratedStage C (stageTupleSnocMap (𝟙 a) f)).map
        ((iteratedStageTupleSnocFlattenEquivalence C a z).functor.map h)) :=
  iteratedStageTupleSnocFlattenEquivalence_suffix_map C r a f h

end MathlibExtTest.KTheory.Waldhausen.IteratedStageFlattenSuffixReindexTests

end
