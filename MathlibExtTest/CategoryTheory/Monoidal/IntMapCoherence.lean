/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import MathlibExt.CategoryTheory.Monoidal.IntMapCoherence
import MathlibExt.CategoryTheory.Monoidal.RelCat
open CategoryTheory MonoidalCategory
universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄
variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
  [SymmetricCategory C] [SymmetricCategory D] [SymmetricCategory E]
variable (T : SymmetricTrace C) (S : SymmetricTrace D) (R : SymmetricTrace E)
  (F : C ⥤ D) (G : D ⥤ E) [F.Braided] [G.Braided]
  (hF : T.Preserves S F) (hG : S.Preserves R G)
open IntConstruction
example : map T R (F ⋙ G) (hF.comp hG) ≅ map T S F hF ⋙ map S R G hG :=
  mapCompIso T S R F G hF hG

example : map T T (𝟭 C) T.preserves_id ≅ 𝟭 (IntConstruction T) := mapIdIso T
example : NatTrans.IsMonoidal (mapIdIso T).hom := inferInstance
example : NatTrans.IsMonoidal (mapIdIso T).inv := inferInstance
example : NatTrans.IsMonoidal (mapCompIso T S R F G hF hG).hom := inferInstance
example : NatTrans.IsMonoidal (mapCompIso T S R F G hF hG).inv := inferInstance
example (X : IntConstruction T) : (mapIdIso T).hom.app X = 𝟙 X := mapIdIso_hom_app T X
example (X : IntConstruction T) : (mapCompIso T S R F G hF hG).hom.app X =
    𝟙 ((map T S F hF ⋙ map S R G hG).obj X) := mapCompIso_hom_app T S R F G hF hG X
example {X Y : IntConstruction T} (f : X ⟶ Y) :
    (map T R (F ⋙ G) (hF.comp hG)).map f ≫ (mapCompIso T S R F G hF hG).hom.app Y =
      (mapCompIso T S R F G hF hG).hom.app X ≫ (map S R G hG).map ((map T S F hF).map f) :=
  (mapCompIso T S R F G hF hG).hom.naturality f
example {A U V W : C} (f : A ⊗ W ⟶ V ⊗ U) :
    mapCrossed (F ⋙ G) f = mapCrossed G (mapCrossed F f) := mapCrossed_compFunctor F G f
example (X Y : IntConstruction T) :
    Functor.LaxMonoidal.μ (map T R (F ⋙ G) (hF.comp hG)) X Y ≫
      (mapCompIso T S R F G hF hG).hom.app (X ⊗ Y) =
    ((mapCompIso T S R F G hF hG).hom.app X ⊗ₘ (mapCompIso T S R F G hF hG).hom.app Y) ≫
      Functor.LaxMonoidal.μ (map T S F hF ⋙ map S R G hG) X Y := NatTrans.IsMonoidal.tensor X Y
example : mapCompIso T T S (𝟭 C) F T.preserves_id hF ≪≫
    Functor.isoWhiskerRight (mapIdIso T) (map T S F hF) ≪≫ (map T S F hF).leftUnitor =
      mapIso T S (SymmetricTrace.Preserves.comp T.preserves_id hF) hF F.leftUnitor := mapCompIso_left_unit T S F hF
example : mapCompIso T S S F (𝟭 D) hF S.preserves_id ≪≫
    Functor.isoWhiskerLeft (map T S F hF) (mapIdIso S) ≪≫ (map T S F hF).rightUnitor =
      mapIso T S (SymmetricTrace.Preserves.comp hF S.preserves_id) hF F.rightUnitor := mapCompIso_right_unit T S F hF

-- Triple composition spans four independent categories and universes.
variable {B : Type u₄} [Category.{v₄} B] [MonoidalCategory B] [SymmetricCategory B]
  (Q : SymmetricTrace B) (H : E ⥤ B) [H.Braided] (hH : R.Preserves Q H)
example :
    mapCompIso T R Q (F ⋙ G) H (hF.comp hG) hH ≪≫
      Functor.isoWhiskerRight (mapCompIso T S R F G hF hG) (map R Q H hH) ≪≫
        Functor.associator (map T S F hF) (map S R G hG) (map R Q H hH) =
    mapIso T Q (SymmetricTrace.Preserves.comp (hF.comp hG) hH) (SymmetricTrace.Preserves.comp hF (hG.comp hH)) (Functor.associator F G H) ≪≫
      mapCompIso T S Q F (G ⋙ H) hF (hG.comp hH) ≪≫
      Functor.isoWhiskerLeft (map T S F hF) (mapCompIso S R Q G H hG hH) :=
  mapCompIso_assoc T S R F G hF hG Q H hH

-- Empty and universal crossed relations survive the identity comparison.
private abbrev relTrace := RelCat.symmetricTrace.{0}
example (P U B V : RelCat.{0}) :
    (hom relTrace ((map relTrace relTrace (𝟭 RelCat.{0}) relTrace.preserves_id).map
      (ofHom relTrace (X := ⟨P,U⟩) (Y := ⟨B,V⟩) (RelCat.Hom.ofRel ∅)))).rel = ∅ := by
  change (mapCrossed (𝟭 RelCat.{0}) (RelCat.Hom.ofRel ∅ : P ⊗ V ⟶ B ⊗ U)).rel = ∅
  rw [mapCrossed_idFunctor]
example (P U B V : RelCat.{0}) :
    (hom relTrace ((map relTrace relTrace (𝟭 RelCat.{0}) relTrace.preserves_id).map
      (ofHom relTrace (X := ⟨P,U⟩) (Y := ⟨B,V⟩) (RelCat.Hom.ofRel Set.univ)))).rel = Set.univ := by
  change (mapCrossed (𝟭 RelCat.{0}) (RelCat.Hom.ofRel Set.univ : P ⊗ V ⟶ B ⊗ U)).rel = Set.univ
  rw [mapCrossed_idFunctor]
