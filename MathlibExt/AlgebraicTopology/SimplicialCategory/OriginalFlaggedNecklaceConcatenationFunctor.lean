/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceConcatenationMaps

/-!
# The actual full original flagged concatenation functor

Both full native flagged maps concatenate through the original pushout.
The genuine identity and composition laws follow on those same maps,
with every original input, endpoint and coefficient flag retained.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace

open SSet.OriginalNecklace

variable {K : SSet.{u}} {x y z : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}

/-- Concatenation of the same full native identities is the original flagged identity. -/
theorem concatHom_id (T : Object K x y q) (U : Object K y z q) :
    concatHom (𝟙 T) (𝟙 U) = 𝟙 (concat T U) := by
  apply Hom.ext
  apply Morphism.map_injective.{u}
  rw [concatHom_map]
  change concatMap (𝟙 T.necklace) (𝟙 U.necklace) =
    (Morphism.id (T.necklace.concat U.necklace)).map
  rw [Morphism.map_id]
  apply (concat_isPushout T.necklace U.necklace).hom_ext
  · rw [concatLeft_map, show (𝟙 T.necklace : T.necklace ⟶ T.necklace).map.{u} = 𝟙 T.necklace.object from
      Morphism.map_id T.necklace, Category.id_comp, Category.comp_id]
  · rw [concatRight_map, show (𝟙 U.necklace : U.necklace ⟶ U.necklace).map.{u} = 𝟙 U.necklace.object from
      Morphism.map_id U.necklace, Category.id_comp, Category.comp_id]

/-- Both original full-map compositions commute with actual flagged concatenation. -/
theorem concatHom_comp {T T' T'' : Object K x y q} {U U' U'' : Object K y z q}
    (f : T ⟶ T') (f' : T' ⟶ T'') (g : U ⟶ U') (g' : U' ⟶ U'') :
    concatHom (f ≫ f') (g ≫ g') = concatHom f g ≫ concatHom f' g' := by
  apply Hom.ext
  apply Morphism.map_injective.{u}
  change (concatHom (f ≫ f') (g ≫ g')).necklaceMap.map =
    (Morphism.comp (concatHom f g).necklaceMap (concatHom f' g').necklaceMap).map
  rw [Morphism.map_comp, concatHom_map, concatHom_map, concatHom_map]
  apply (concat_isPushout T.necklace U.necklace).hom_ext
  · rw [concatLeft_map, ← Category.assoc, concatLeft_map, Category.assoc, concatLeft_map]
    change (Morphism.comp f.necklaceMap f'.necklaceMap).map ≫ _ = _
    rw [Morphism.map_comp, Category.assoc]
  · rw [concatRight_map, ← Category.assoc, concatRight_map, Category.assoc, concatRight_map]
    change (Morphism.comp g.necklaceMap g'.necklaceMap).map ≫ _ = _
    rw [Morphism.map_comp, Category.assoc]

/-- The genuine entire original concatenation functor, on the original full product category. -/
def concatenationFunctor (K : SSet.{u}) (x y z : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    Object K x y q × Object K y z q ⥤ Object K x z q where
  obj T := concat T.1 T.2
  map f := concatHom f.1 f.2
  map_id T := concatHom_id T.1 T.2
  map_comp f g := concatHom_comp f.1 g.1 f.2 g.2

/-- The whole original product object retains its same literal concatenated necklace. -/
theorem concatenationFunctor_obj (K : SSet.{u}) (x y z : K _⦋0⦌) (q : SimplexCategoryᵒᵖ)
    (T : Object K x y q) (U : Object K y z q) :
    (concatenationFunctor K x y z q).obj (T, U) = concat T U := rfl

/-- The genuine product functor keeps both same full native flagged maps. -/
theorem concatenationFunctor_map {T T' : Object K x y q} {U U' : Object K y z q}
    (f : T ⟶ T') (g : U ⟶ U') :
    (concatenationFunctor K x y z q).map (X := (T, U)) (Y := (T', U')) (f, g) = concatHom f g := rfl

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace
