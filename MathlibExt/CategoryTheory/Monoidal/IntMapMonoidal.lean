/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import MathlibExt.CategoryTheory.Monoidal.IntMonoidal
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-!
# Strong symmetric monoidal functoriality of Int

A trace-preserving strong symmetric monoidal functor induces a strong symmetric
monoidal functor between Int constructions. The negative component uses the
inverse tensor comparison, in the reversed order of the Int tensor.

Source: Joyal, Street and Verity, Traced monoidal categories (1996), Sections 4–5,
https://doi.org/10.1017/S0305004100074338, specialized to symmetric categories.
-/

@[expose] public section
universe v₁ v₂ u₁ u₂
namespace CategoryTheory
open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal
open scoped MonoidalCategory
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [MonoidalCategory C] [MonoidalCategory D] [SymmetricCategory C] [SymmetricCategory D]
namespace IntConstruction
variable (T : SymmetricTrace C) (S : SymmetricTrace D) (F : C ⥤ D) [F.Braided]
variable (hF : T.Preserves S F)

/-- The induced functor acts componentwise on separated morphisms. -/
@[simp] theorem map_mapPair {X Y : IntConstruction T}
    (f : X.positive ⟶ Y.positive) (g : Y.negative ⟶ X.negative) :
    (map T S F hF).map (mapPair T f g) = mapPair S (F.map f) (F.map g) := by
  apply hom_ext S
  change μ F _ _ ≫ F.map (f ⊗ₘ g) ≫ δ F _ _ = _
  rw [Functor.Monoidal.map_tensor]
  simp only [Category.assoc, μ_δ_assoc, μ_δ, Category.comp_id]
  rfl

/-- The unit comparison uses the unit isomorphism in opposite directions. -/
def mapUnitIso : 𝟙_ (IntConstruction S) ≅ (map T S F hF).obj (𝟙_ (IntConstruction T)) :=
  pairIso S (εIso F) (εIso F).symm

/-- The negative tensor comparison reverses the factors and its direction. -/
def mapTensorIso (X Y : IntConstruction T) :
    (map T S F hF).obj X ⊗ (map T S F hF).obj Y ≅ (map T S F hF).obj (X ⊗ Y) :=
  pairIso S (μIso F X.positive Y.positive) (μIso F Y.negative X.negative).symm

@[reassoc] private theorem map_tensorShuffle (A B U V : C) :
    μ F (A ⊗ B) (V ⊗ U) ≫ F.map (tensorShuffle A B U V).hom ≫
      δ F (A ⊗ U) (B ⊗ V) =
    (δ F A B ⊗ₘ δ F V U) ≫
      (tensorShuffle (F.obj A) (F.obj B) (F.obj U) (F.obj V)).hom ≫
        (μ F A U ⊗ₘ μ F B V) := by
  simp only [tensorShuffle, Iso.trans_hom, whiskerLeftIso_hom, tensorμ,
    Functor.map_comp, map_whiskerLeft, map_whiskerRight, map_associator,
    map_associator_inv, Functor.map_braiding, Category.assoc,
    μ_δ_assoc, whiskerLeft_comp, comp_whiskerRight, whiskerLeft_μ_δ_assoc]
  simp only [← whiskerLeft_comp_assoc, ← comp_whiskerRight_assoc,
    μ_δ, μ_δ_assoc, Category.comp_id]
  simp only [whiskerLeft_comp, Category.assoc]
  simp only [tensorHom_def, Category.assoc, whisker_exchange_assoc,
    associator_naturality_right_assoc, associator_inv_naturality_right_assoc,
    ← whiskerLeft_comp_assoc, μ_δ, whiskerLeft_id, Category.id_comp]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [whisker_exchange]



@[reassoc] private theorem map_tensorShuffle_inv (A B U V : C) :
    μ F (A ⊗ U) (B ⊗ V) ≫ F.map (tensorShuffle A B U V).inv ≫
      δ F (A ⊗ B) (V ⊗ U) =
    (δ F A U ⊗ₘ δ F B V) ≫
      (tensorShuffle (F.obj A) (F.obj B) (F.obj U) (F.obj V)).inv ≫
        (μ F A B ⊗ₘ μ F V U) := by
  have h : μIso F (A ⊗ B) (V ⊗ U) ≪≫ F.mapIso (tensorShuffle A B U V) ≪≫
      (μIso F (A ⊗ U) (B ⊗ V)).symm =
      ((μIso F A B).symm ⊗ᵢ (μIso F V U).symm) ≪≫
        tensorShuffle (F.obj A) (F.obj B) (F.obj U) (F.obj V) ≪≫
          (μIso F A U ⊗ᵢ μIso F B V) :=
    Iso.ext (map_tensorShuffle F A B U V)
  simpa only [Iso.trans_inv, Iso.symm_inv, tensorIso_inv, tensorIso_hom,
    Functor.mapIso_inv, μIso_inv, μIso_hom, Category.assoc] using congrArg Iso.inv h

set_option backward.defeqAttrib.useBackward true in
/-- Tensor comparison is natural in arbitrary crossed morphisms. -/
theorem mapTensorIso_hom_natural {X₁ X₂ Y₁ Y₂ : IntConstruction T}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    ((map T S F hF).map f ⊗ₘ (map T S F hF).map g) ≫ (mapTensorIso T S F hF Y₁ Y₂).hom =
      (mapTensorIso T S F hF X₁ X₂).hom ≫ (map T S F hF).map (f ⊗ₘ g) := by
  apply hom_ext S
  change compose S (hom S (tensorMap S ((map T S F hF).map f) ((map T S F hF).map g)))
      (μ F Y₁.positive Y₂.positive ⊗ₘ δ F Y₂.negative Y₁.negative) =
    compose S (μ F X₁.positive X₂.positive ⊗ₘ δ F X₂.negative X₁.negative)
      (mapCrossed F (hom T (tensorMap T f g)))
  dsimp only [map]
  rw [compose_tensor_right, compose_tensor_left]
  change _ = μ F _ _ ▷ _ ≫
    (μ F _ _ ≫ F.map ((tensorShuffle _ _ _ _).hom ≫ (hom T f ⊗ₘ hom T g) ≫
      (tensorShuffle _ _ _ _).inv) ≫ δ F _ _) ≫ _
  rw [Functor.map_comp, Functor.map_comp, Functor.Monoidal.map_tensor]
  simp only [Category.assoc]
  rw [map_tensorShuffle_assoc, map_tensorShuffle_inv_assoc]
  dsimp only [tensorMap, map, mapCrossed, hom, ofHom]
  simp only [Category.assoc, tensorHom_def, comp_whiskerRight, whiskerLeft_comp]
  simp only [whiskerRight_μ_δ_assoc, whiskerLeft_μ_δ, Category.comp_id,
    whisker_exchange_assoc]

set_option backward.defeqAttrib.useBackward true in
/-- Strong monoidal comparison maps for the induced Int functor. -/
def mapCoreMonoidal : (map T S F hF).CoreMonoidal where
  εIso := mapUnitIso T S F hF
  μIso := mapTensorIso T S F hF
  μIso_hom_natural_left f X := by
    simpa only [← tensorHom_id, Functor.map_id] using
      mapTensorIso_hom_natural T S F hF f (𝟙 X)
  μIso_hom_natural_right X f := by
    simpa only [← id_tensorHom, Functor.map_id] using
      mapTensorIso_hom_natural T S F hF (𝟙 X) f
  associativity X Y Z := by
    change tensorMap S (mapPair S _ _) (𝟙 _) ≫ mapPair S _ _ ≫
      (map T S F hF).map (mapPair T _ _) =
        mapPair S _ _ ≫ tensorMap S (𝟙 _) (mapPair S _ _) ≫ mapPair S _ _
    rw [map_mapPair]
    dsimp only [map]
    rw [← mapPair_id S, ← mapPair_id S, tensorMap_mapPair, tensorMap_mapPair]
    simp only [mapPair_comp]
    congr 1 <;> simp
  left_unitality X := by
    change mapPair S _ _ = tensorMap S (mapPair S _ _) (𝟙 _) ≫
      mapPair S _ _ ≫ (map T S F hF).map (mapPair T _ _)
    rw [map_mapPair]
    dsimp only [map]
    rw [← mapPair_id S, tensorMap_mapPair]
    simp only [mapPair_comp]
    congr 1 <;> simp
  right_unitality X := by
    change mapPair S _ _ = tensorMap S (𝟙 _) (mapPair S _ _) ≫
      mapPair S _ _ ≫ (map T S F hF).map (mapPair T _ _)
    rw [map_mapPair]
    dsimp only [map]
    rw [← mapPair_id S, tensorMap_mapPair]
    simp only [mapPair_comp]
    congr 1 <;> simp

/-- Trace-preserving strong symmetric monoidal functors induce strong monoidal Int functors. -/
instance mapMonoidal : (map T S F hF).Monoidal :=
  Functor.CoreMonoidal.toMonoidal (mapCoreMonoidal T S F hF)

/-- The induced tensor comparison acts covariantly on positives and contravariantly on negatives. -/
@[simp] theorem map_μ (X Y : IntConstruction T) :
    μ (map T S F hF) X Y = mapPair S (μ F X.positive Y.positive)
      (δ F Y.negative X.negative) := rfl

/-- The induced unit comparison uses the unit map and its inverse. -/
@[simp] theorem map_ε : ε (map T S F hF) = mapPair S (ε F) (η F) := rfl

set_option backward.defeqAttrib.useBackward true in
/-- The induced Int functor preserves the symmetry. -/
instance mapBraided : (map T S F hF).Braided where
  braided X Y := by
    change mapPair S _ _ ≫ (map T S F hF).map (mapPair T _ _) =
      mapPair S _ _ ≫ mapPair S _ _
    rw [map_mapPair]
    dsimp only [map]
    simp only [mapPair_comp]
    congr 1 <;> simp [Functor.map_braiding]

set_option backward.defeqAttrib.useBackward true in
/-- Applying a functor before or after the canonical embedding gives isomorphic functors. -/
def embeddingMapIso : embedding T ⋙ map T S F hF ≅ F ⋙ embedding S :=
  NatIso.ofComponents (fun X => pairIso S (Iso.refl (F.obj X)) (εIso F)) (by
    intro X Y f
    change (map T S F hF).map ((embedding T).map f) ≫ mapPair S _ _ =
      mapPair S _ _ ≫ (embedding S).map (F.map f)
    simp only [embedding_map_eq_mapPair]
    dsimp only [embedding]
    rw [map_mapPair]
    dsimp only [map]
    simp only [mapPair_comp, Functor.map_id, Iso.refl_hom, εIso_hom,
      Category.comp_id, Category.id_comp])

private theorem map_unit_diagonal :
    ε F ≫ F.map (λ_ (𝟙_ C)).inv ≫ δ F (𝟙_ C) (𝟙_ C) =
      (λ_ (𝟙_ D)).inv ≫ (ε F ⊗ₘ ε F) := by
  rw [map_leftUnitor_inv]
  simp only [Category.assoc, μ_δ, Category.comp_id]
  rw [leftUnitor_inv_naturality_assoc, ← tensorHom_def']

set_option backward.defeqAttrib.useBackward true in
/-- The embedding compatibility isomorphism is monoidal. -/
instance embeddingMapIso_hom_isMonoidal :
    NatTrans.IsMonoidal (embeddingMapIso T S F hF).hom where
  unit := by
    change ε (embedding T ⋙ map T S F hF) ≫ mapPair S _ _ = ε (F ⋙ embedding S)
    simp only [Functor.LaxMonoidal.comp_ε, map_ε, embedding_ε,
      embedding_map_eq_mapPair]
    dsimp only [embedding]
    rw [map_mapPair]
    dsimp only [map]
    simp only [mapPair_comp]
    congr 1 <;> simp
  tensor X Y := by
    change μ (embedding T ⋙ map T S F hF) X Y ≫ mapPair S _ _ =
      tensorMap S (mapPair S _ _) (mapPair S _ _) ≫ μ (F ⋙ embedding S) X Y
    simp only [Functor.LaxMonoidal.comp_μ, map_μ, embedding_μ,
      embedding_map_eq_mapPair]
    dsimp only [embedding]
    rw [map_mapPair]
    dsimp only [map]
    rw [tensorMap_mapPair]
    simp only [mapPair_comp]
    congr 1
    · simp
    · simpa using map_unit_diagonal F

end IntConstruction
end CategoryTheory
