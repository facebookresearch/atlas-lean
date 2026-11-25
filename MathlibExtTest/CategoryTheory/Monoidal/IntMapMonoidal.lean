/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import MathlibExt.CategoryTheory.Monoidal.IntMapMonoidal
import MathlibExt.CategoryTheory.Monoidal.RelCat
import Mathlib.CategoryTheory.Monoidal.Braided.Opposite

open CategoryTheory MonoidalCategory
open scoped MonoidalCategory
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [MonoidalCategory C] [MonoidalCategory D] [SymmetricCategory C] [SymmetricCategory D]
variable (T : SymmetricTrace C) (S : SymmetricTrace D) (F : C ⥤ D) [F.Braided]
  (hF : T.Preserves S F)
example : (IntConstruction.map T S F hF).Monoidal := inferInstance
example : (IntConstruction.map T S F hF).Braided := inferInstance


open IntConstruction Functor.LaxMonoidal Functor.OplaxMonoidal

-- No source or target rigidity is assumed; all four universes are independent.
example (X Y : IntConstruction T) :
    μ (map T S F hF) X Y = mapPair S (μ F X.positive Y.positive)
      (δ F Y.negative X.negative) := map_μ T S F hF X Y
example : ε (map T S F hF) = mapPair S (ε F) (η F) := map_ε T S F hF
example (X Y : IntConstruction T) : IsIso (μ (map T S F hF) X Y) := inferInstance
example : IsIso (ε (map T S F hF)) := inferInstance
example {X Y : IntConstruction T} (a : X.positive ⟶ Y.positive)
    (b : Y.negative ⟶ X.negative) :
    (map T S F hF).map (mapPair T a b) = mapPair S (F.map a) (F.map b) :=
  map_mapPair T S F hF a b

-- Naturality covers arbitrary feedback maps, not only separated maps.
example {X₁ X₂ Y₁ Y₂ : IntConstruction T} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    ((map T S F hF).map f ⊗ₘ (map T S F hF).map g) ≫ μ (map T S F hF) Y₁ Y₂ =
      μ (map T S F hF) X₁ X₂ ≫ (map T S F hF).map (f ⊗ₘ g) :=
  Functor.LaxMonoidal.μ_natural _ f g
example (X Y : IntConstruction T) :
    μ (map T S F hF) X Y ≫ (map T S F hF).map (β_ X Y).hom =
      (β_ _ _).hom ≫ μ (map T S F hF) Y X := Functor.LaxBraided.braided X Y

example : embedding T ⋙ map T S F hF ≅ F ⋙ embedding S := embeddingMapIso T S F hF
example : NatTrans.IsMonoidal (embeddingMapIso T S F hF).hom := inferInstance
example : NatTrans.IsMonoidal (embeddingMapIso T S F hF).inv := inferInstance
example (X : C) : (embeddingMapIso T S F hF).hom.app X =
    mapPair S (𝟙 (F.obj X)) (ε F) := rfl
example (X : C) : (embeddingMapIso T S F hF).inv.app X =
    mapPair S (𝟙 (F.obj X)) (η F) := rfl
example {X Y : C} (f : X ⟶ Y) :
    (map T S F hF).map ((embedding T).map f) ≫ (embeddingMapIso T S F hF).hom.app Y =
      (embeddingMapIso T S F hF).hom.app X ≫ (embedding S).map (F.map f) :=
  (embeddingMapIso T S F hF).hom.naturality f

-- The identity functor introduces no additional feedback or comparison morphism.
example (X Y : IntConstruction T) :
    μ (map T T (𝟭 C) T.preserves_id) X Y = 𝟙 (X ⊗ Y) := by
  rw [map_μ]
  exact mapPair_id T _
example : ε (map T T (𝟭 C) T.preserves_id) = 𝟙 (𝟙_ (IntConstruction T)) := by
  rw [map_ε]
  exact mapPair_id T _

-- A nonidentity functor reverses tensor order, so both comparison maps matter.
open MonoidalOpposite
local instance : SymmetricCategory Cᴹᵒᵖ where
  symmetry X Y := by
    apply Quiver.Hom.unmop_inj
    exact SymmetricCategory.symmetry (unmop Y) (unmop X)

example (R : SymmetricTrace Cᴹᵒᵖ) (h : T.Preserves R (mopFunctor C))
    (X Y : IntConstruction T) :
    μ (map T R (mopFunctor C) h) X Y =
      mapPair R (β_ (mop X.positive) (mop Y.positive)).hom
        (β_ (mop Y.negative) (mop X.negative)).inv := rfl

-- Concrete relational data survives identity transport, including empty relations.
example {X Y : IntConstruction RelCat.symmetricTrace} (r : X ⟶ Y) :
    hom RelCat.symmetricTrace
      ((map RelCat.symmetricTrace RelCat.symmetricTrace (𝟭 RelCat)
        RelCat.symmetricTrace.preserves_id).map r) = hom RelCat.symmetricTrace r := by
  change 𝟙 _ ≫ hom RelCat.symmetricTrace r ≫ 𝟙 _ = hom RelCat.symmetricTrace r
  rw [Category.id_comp, Category.comp_id]
example (A B U V : RelCat) :
    (hom RelCat.symmetricTrace
      ((map RelCat.symmetricTrace RelCat.symmetricTrace (𝟭 RelCat)
        RelCat.symmetricTrace.preserves_id).map
        (ofHom RelCat.symmetricTrace (X := ⟨A, U⟩) (Y := ⟨B, V⟩)
          (RelCat.Hom.ofRel ∅)))).rel = ∅ := by
  change (𝟙 (A ⊗ V) ≫ (RelCat.Hom.ofRel ∅ : A ⊗ V ⟶ B ⊗ U) ≫ 𝟙 _).rel = ∅
  rw [Category.id_comp, Category.comp_id]
