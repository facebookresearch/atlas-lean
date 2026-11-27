/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.FGProjectiveCat.ConeRing.Absorption
public import MathlibExt.Algebra.Category.FGProjectiveCat.ScalarExtensionIntertwinerCoherence
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Original coefficient-ring naturality of projective cone absorption

The actual coefficient ring map preserves the original four partial-
permutation matrices and commutes with the original countable repeat.
The native scalar-composition isomorphisms therefore compare the two
actual infinity routes. The original coefficient intertwiners commute
with further scalar extension on their actual tensor representatives.
-/

public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open ModuleCat.RingHomScalarExtension

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

universe uR uS

private def actualSumComparison {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ C) (G : D ⥤ D) (L : C ⥤ D) [L.Additive] (e : F ⋙ L ≅ L ⋙ G) :
    (pointwiseBinaryBicone (𝟭 C) F).pt ⋙ L ≅ L ⋙ (pointwiseBinaryBicone (𝟭 D) G).pt :=
  NatIso.ofComponents
    (fun X => L.mapBiprod X (F.obj X) ≪≫
      biprod.mapIso (Iso.refl (L.obj X)) (e.app X))
    (by
      intro X Y a
      change L.map (biprod.map a (F.map a)) ≫
          ((L.mapBiprod Y (F.obj Y)).hom ≫ biprod.map (𝟙 _) (e.hom.app Y)) =
        ((L.mapBiprod X (F.obj X)).hom ≫ biprod.map (𝟙 _) (e.hom.app X)) ≫
          biprod.map (L.map a) (G.map (L.map a))
      dsimp only [Functor.comp_obj]
      apply biprod.hom_ext
      · simp only [Functor.mapBiprod_hom, Category.assoc,
          biprod.map_fst, biprod.lift_fst, Category.comp_id]
        rw [← L.map_comp, biprod.map_fst, L.map_comp]
        rw [biprod.map_fst_assoc, biprod.lift_fst_assoc, Category.id_comp]
      · simp only [Functor.mapBiprod_hom, Category.assoc, biprod.map_snd_assoc,
          biprod.map_snd, biprod.lift_snd_assoc]
        rw [← Category.assoc, ← L.map_comp, biprod.map_snd, L.map_comp, Category.assoc]
        exact congrArg (fun h => L.map biprod.snd ≫ h) (e.hom.naturality a))

private theorem actualSumComparison_hom_app {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ C) (G : D ⥤ D) (L : C ⥤ D) [L.Additive] (e : F ⋙ L ≅ L ⋙ G) (X : C) :
    (actualSumComparison F G L e).hom.app X =
      (L.mapBiprod X (F.obj X)).hom ≫ biprod.map (𝟙 (L.obj X)) (e.hom.app X) := by rfl

private theorem originalMappedInl {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] [HasBinaryBiproducts C]
    (L : C ⥤ D) [L.Additive] (X Y : C) :
    L.map (biprod.inl : X ⟶ X ⊞ Y) ≫ (L.mapBiprod X Y).hom = biprod.inl := by
  apply biprod.hom_ext
  · simp only [Functor.mapBiprod_hom, Category.assoc, biprod.lift_fst,
      ← L.map_comp, biprod.inl_fst, L.map_id]
  · simp only [Functor.mapBiprod_hom, Category.assoc, biprod.lift_snd,
      ← L.map_comp, biprod.inl_snd, L.map_zero]

private theorem originalMappedInr {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] [HasBinaryBiproducts C]
    (L : C ⥤ D) [L.Additive] (X Y : C) :
    L.map (biprod.inr : Y ⟶ X ⊞ Y) ≫ (L.mapBiprod X Y).hom = biprod.inr := by
  apply biprod.hom_ext
  · simp only [Functor.mapBiprod_hom, Category.assoc, biprod.lift_fst,
      ← L.map_comp, biprod.inr_fst, L.map_zero]
  · simp only [Functor.mapBiprod_hom, Category.assoc, biprod.lift_snd,
      ← L.map_comp, biprod.inr_snd, L.map_id]

private theorem actualSumComparison_inl {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ C) (G : D ⥤ D) (L : C ⥤ D) [L.Additive] (e : F ⋙ L ≅ L ⋙ G) (X : C) :
    L.map ((pointwiseBinaryBicone (𝟭 C) F).inl.app X) ≫
        (actualSumComparison F G L e).hom.app X =
      (pointwiseBinaryBicone (𝟭 D) G).inl.app (L.obj X) := by
  rw [actualSumComparison_hom_app]
  change L.map (biprod.inl : X ⟶ X ⊞ F.obj X) ≫
      (L.mapBiprod X (F.obj X)).hom ≫ biprod.map (𝟙 (L.obj X)) (e.hom.app X) =
    (biprod.inl : L.obj X ⟶ L.obj X ⊞ G.obj (L.obj X))
  dsimp only [Functor.comp_obj]
  rw [← Category.assoc, originalMappedInl, biprod.inl_map, Category.id_comp]

private theorem actualSumComparison_inr {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ C) (G : D ⥤ D) (L : C ⥤ D) [L.Additive] (e : F ⋙ L ≅ L ⋙ G) (X : C) :
    L.map ((pointwiseBinaryBicone (𝟭 C) F).inr.app X) ≫
        (actualSumComparison F G L e).hom.app X =
      e.hom.app X ≫ (pointwiseBinaryBicone (𝟭 D) G).inr.app (L.obj X) := by
  rw [actualSumComparison_hom_app]
  change L.map (biprod.inr : F.obj X ⟶ X ⊞ F.obj X) ≫
      (L.mapBiprod X (F.obj X)).hom ≫ biprod.map (𝟙 (L.obj X)) (e.hom.app X) =
    e.hom.app X ≫ (biprod.inr : G.obj (L.obj X) ⟶ L.obj X ⊞ G.obj (L.obj X))
  dsimp only [Functor.comp_obj]
  rw [← Category.assoc, originalMappedInr, biprod.inr_map]

private theorem originalMappedSumFst {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (L : C ⥤ D) [L.Additive] (X Y : C) {Z : D} (e : L.obj Y ≅ Z) :
    ((L.mapBiprod X Y).hom ≫ biprod.map (𝟙 (L.obj X)) e.hom) ≫ biprod.fst =
      L.map biprod.fst := by
  simp only [Category.assoc, biprod.map_fst, Category.comp_id,
    Functor.mapBiprod_hom, biprod.lift_fst]

private theorem originalMappedSumSnd {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (L : C ⥤ D) [L.Additive] (X Y : C) {Z : D} (e : L.obj Y ≅ Z) :
    ((L.mapBiprod X Y).hom ≫ biprod.map (𝟙 (L.obj X)) e.hom) ≫ biprod.snd =
      L.map biprod.snd ≫ e.hom := by
  rw [Category.assoc, biprod.map_snd, ← Category.assoc,
    Functor.mapBiprod_hom, biprod.lift_snd]

private theorem originalAbsorptionSquare {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (L : C ⥤ D) [L.Additive] (X Y : C) {Z : D} (e : L.obj Y ≅ Z)
    (l : X ⟶ Y) (t : Y ⟶ Y) (l' : L.obj X ⟶ Z) (t' : Z ⟶ Z)
    (h0 : L.map l ≫ e.hom = l') (h1 : L.map t ≫ e.hom = e.hom ≫ t') :
    L.map (biprod.fst ≫ l + biprod.snd ≫ t) ≫ e.hom =
      (L.mapBiprod X Y).hom ≫ biprod.map (𝟙 (L.obj X)) e.hom ≫
        (biprod.fst ≫ l' + biprod.snd ≫ t') := by
  rw [← biprod.desc_eq, ← biprod.desc_eq]
  apply (cancel_epi (L.mapBiprod X Y).inv).1
  rw [← Category.assoc, biprod.mapBiprod_inv_map_desc, Iso.inv_hom_id_assoc]
  apply biprod.hom_ext'
  · simpa only [Category.assoc, biprod.inl_desc_assoc, biprod.inl_map_assoc,
      Category.id_comp, biprod.inl_desc] using h0
  · simpa only [Category.assoc, biprod.inr_desc_assoc, biprod.inr_map_assoc,
      biprod.inr_desc] using h1

private theorem originalSquareReturn {C : Type*} [Category* C] {A B E Z : C}
    (a : A ≅ B) (b : B ≅ Z) (c : A ≅ E) (d : E ≅ Z)
    (h : a.hom ≫ b.hom = c.hom ≫ d.hom) : b.hom ≫ d.inv = a.inv ≫ c.hom := by
  apply (cancel_epi a.hom).1
  rw [← Category.assoc, h, Category.assoc, d.hom_inv_id, Category.comp_id,
    ← Category.assoc, a.hom_inv_id, Category.id_comp]

namespace FGProjectiveCat

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

private theorem nativeTwoCompose_ext (f : R →+* S) (X : FGProjectiveCat.{uR} R)
    {A Z : FGProjectiveCat.{uS} S}
    (a : (ringScalarExtension f).obj X ⟶ A) (b : A ⟶ Z)
    {c : (ringScalarExtension f).obj X ⟶ Z}
    (h : ∀ s x, b.hom.hom (a.hom.hom
      ((ringScalarExtensionCoordinates f X).symm (pure f X s x))) =
        c.hom.hom ((ringScalarExtensionCoordinates f X).symm (pure f X s x))) :
    a ≫ b = c := by
  apply ringScalarExtension_hom_ext f X
  exact h


end FGProjectiveCat

namespace FGProjectiveCat.ConeRing

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

/-- The actual scalar-extension functor of the original cone coefficient map. -/
abbrev coefficientFunctor (f : R →+* S) :
    category R ⥤ category S := ringScalarExtension (_root_.ConeRing.map f)

/-- The original additive scalar functor preserves its actual pointwise binary biproducts. -/
instance coefficientFunctorPreservesBinaryBiproducts (f : R →+* S) :
    PreservesBinaryBiproducts (coefficientFunctor f) :=
  preservesBinaryBiproducts_of_preservesBiproducts (coefficientFunctor f)

/-- The original first projection matrix is natural for the actual coefficient ring map. -/
theorem map_firstProjection (f : R →+* S) :
    _root_.ConeRing.map f (_root_.ConeRing.firstProjection R) =
      _root_.ConeRing.firstProjection S := by
  classical
  apply Matrix.LocallyFinite.ext
  intro i j
  change f (Matrix.LocallyFinite.projection _root_.ConeRing.firstEmbedding i j) =
    Matrix.LocallyFinite.projection _root_.ConeRing.firstEmbedding i j
  simp only [Matrix.LocallyFinite.projection_apply]
  split_ifs <;> simp

/-- The original tail projection matrix is natural for the actual coefficient ring map. -/
theorem map_tailProjection (f : R →+* S) :
    _root_.ConeRing.map f (_root_.ConeRing.tailProjection R) =
      _root_.ConeRing.tailProjection S := by
  classical
  apply Matrix.LocallyFinite.ext
  intro i j
  change f (Matrix.LocallyFinite.projection _root_.ConeRing.tailEmbedding i j) =
    Matrix.LocallyFinite.projection _root_.ConeRing.tailEmbedding i j
  simp only [Matrix.LocallyFinite.projection_apply]
  split_ifs <;> simp

/-- The original first inclusion matrix is natural for the actual coefficient ring map. -/
theorem map_firstInclusion (f : R →+* S) :
    _root_.ConeRing.map f (_root_.ConeRing.firstInclusion R) =
      _root_.ConeRing.firstInclusion S := by
  classical
  apply Matrix.LocallyFinite.ext
  intro i j
  change f (Matrix.LocallyFinite.inclusion _root_.ConeRing.firstEmbedding i j) =
    Matrix.LocallyFinite.inclusion _root_.ConeRing.firstEmbedding i j
  simp only [Matrix.LocallyFinite.inclusion_apply]
  split_ifs <;> simp

/-- The original tail inclusion matrix is natural for the actual coefficient ring map. -/
theorem map_tailInclusion (f : R →+* S) :
    _root_.ConeRing.map f (_root_.ConeRing.tailInclusion R) =
      _root_.ConeRing.tailInclusion S := by
  classical
  apply Matrix.LocallyFinite.ext
  intro i j
  change f (Matrix.LocallyFinite.inclusion _root_.ConeRing.tailEmbedding i j) =
    Matrix.LocallyFinite.inclusion _root_.ConeRing.tailEmbedding i j
  simp only [Matrix.LocallyFinite.inclusion_apply]
  split_ifs <;> simp

/-- The actual ring homomorphism equality underlying the original two infinity routes. -/
theorem coefficient_infinity_comp (f : R →+* S) :
    (_root_.ConeRing.map f).comp (_root_.ConeRing.infinityHom R) =
      (_root_.ConeRing.infinityHom S).comp (_root_.ConeRing.map f) := by
  apply RingHom.ext
  exact _root_.ConeRing.map_infinityHom f

/-- The original cone coefficient equality compares the actual combined scalar functors. -/
def infinityCompositionIso (f : R →+* S) :
    ringScalarExtension ((_root_.ConeRing.map f).comp (_root_.ConeRing.infinityHom R)) ≅
      ringScalarExtension ((_root_.ConeRing.infinityHom S).comp (_root_.ConeRing.map f)) :=
  ringScalarExtensionHomEqualityIso
    ((_root_.ConeRing.map f).comp (_root_.ConeRing.infinityHom R))
    ((_root_.ConeRing.infinityHom S).comp (_root_.ConeRing.map f))
    (coefficient_infinity_comp f)

/-- The intermediate comparison uses the actual equality of the original cone ring maps. -/
theorem infinityCompositionIso_eq (f : R →+* S) :
    infinityCompositionIso f =
      ringScalarExtensionHomEqualityIso
        ((_root_.ConeRing.map f).comp (_root_.ConeRing.infinityHom R))
        ((_root_.ConeRing.infinityHom S).comp (_root_.ConeRing.map f))
        (coefficient_infinity_comp f) := by rfl

/-- The actual combined-functor comparison keeps every original pure coefficient. -/
theorem infinityCompositionIso_hom_pure (f : R →+* S) (X : category R)
    (t : _root_.ConeRing S) (x : X) :
    ((infinityCompositionIso f).hom.app X).hom.hom
        ((ringScalarExtensionCoordinates
          ((_root_.ConeRing.map f).comp (_root_.ConeRing.infinityHom R)) X).symm
          (pure ((_root_.ConeRing.map f).comp (_root_.ConeRing.infinityHom R)) X t x)) =
      (ringScalarExtensionCoordinates
        ((_root_.ConeRing.infinityHom S).comp (_root_.ConeRing.map f)) X).symm
        (pure ((_root_.ConeRing.infinityHom S).comp (_root_.ConeRing.map f)) X t x) :=
  ringScalarExtensionHomEqualityIso_hom_pure
    ((_root_.ConeRing.map f).comp (_root_.ConeRing.infinityHom R))
    ((_root_.ConeRing.infinityHom S).comp (_root_.ConeRing.map f))
    (coefficient_infinity_comp f) X t x

/-- The inverse comparison retains the same original coefficient in the original source tensor. -/
theorem infinityCompositionIso_inv_pure (f : R →+* S) (X : category R)
    (t : _root_.ConeRing S) (x : X) :
    ((infinityCompositionIso f).inv.app X).hom.hom
        ((ringScalarExtensionCoordinates
          ((_root_.ConeRing.infinityHom S).comp (_root_.ConeRing.map f)) X).symm
          (pure ((_root_.ConeRing.infinityHom S).comp (_root_.ConeRing.map f)) X t x)) =
      (ringScalarExtensionCoordinates
        ((_root_.ConeRing.map f).comp (_root_.ConeRing.infinityHom R)) X).symm
        (pure ((_root_.ConeRing.map f).comp (_root_.ConeRing.infinityHom R)) X t x) :=
  ringScalarExtensionHomEqualityIso_inv_pure
    ((_root_.ConeRing.map f).comp (_root_.ConeRing.infinityHom R))
    ((_root_.ConeRing.infinityHom S).comp (_root_.ConeRing.map f))
    (coefficient_infinity_comp f) X t x

/-- Both original tensor-composition comparisons give the actual infinity naturality route. -/
def infinityNaturality (f : R →+* S) :
    infinityFunctor R ⋙ coefficientFunctor f ≅ coefficientFunctor f ⋙ infinityFunctor S :=
  ringScalarExtensionCompIso (_root_.ConeRing.infinityHom R) (_root_.ConeRing.map f) ≪≫
    infinityCompositionIso f ≪≫
      (ringScalarExtensionCompIso (_root_.ConeRing.map f) (_root_.ConeRing.infinityHom S)).symm

/-- The first original composition map is retained as the actual forward infinity route. -/
theorem infinityNaturality_hom (f : R →+* S) :
    (infinityNaturality f).hom =
      (ringScalarExtensionCompIso
        (_root_.ConeRing.infinityHom R) (_root_.ConeRing.map f)).hom ≫
          (infinityCompositionIso f).hom ≫
            (ringScalarExtensionCompIso
              (_root_.ConeRing.map f) (_root_.ConeRing.infinityHom S)).inv := by
  simp only [infinityNaturality, Iso.trans_hom, Iso.symm_hom]

/-- The inverse infinity route retains both original inverse tensor/shrink comparisons. -/
theorem infinityNaturality_inv (f : R →+* S) :
    (infinityNaturality f).inv =
      (ringScalarExtensionCompIso
        (_root_.ConeRing.map f) (_root_.ConeRing.infinityHom S)).hom ≫
          (infinityCompositionIso f).inv ≫
            (ringScalarExtensionCompIso
              (_root_.ConeRing.infinityHom R) (_root_.ConeRing.map f)).inv := by
  simp only [infinityNaturality, Iso.trans_inv, Iso.symm_inv, Category.assoc]

/-- The forward infinity route retains both original nested pure coordinates. -/
theorem infinityNaturality_hom_pure (f : R →+* S) (X : category R)
    (t : _root_.ConeRing S) (s : _root_.ConeRing R) (x : X) :
    ((infinityNaturality f).hom.app X).hom.hom
        ((ringScalarExtensionCoordinates (_root_.ConeRing.map f)
            ((infinityFunctor R).obj X)).symm
          (pure (_root_.ConeRing.map f) ((infinityFunctor R).obj X) t
            ((ringScalarExtensionCoordinates (_root_.ConeRing.infinityHom R) X).symm
              (pure (_root_.ConeRing.infinityHom R) X s x)))) =
      (ringScalarExtensionCoordinates (_root_.ConeRing.infinityHom S)
          ((coefficientFunctor f).obj X)).symm
        (pure (_root_.ConeRing.infinityHom S) ((coefficientFunctor f).obj X)
          (t * _root_.ConeRing.map f s)
          ((ringScalarExtensionCoordinates (_root_.ConeRing.map f) X).symm
            (pure (_root_.ConeRing.map f) X 1 x))) := by
  rw [infinityNaturality_hom, NatTrans.comp_app, NatTrans.comp_app,
    hom_hom_comp, hom_hom_comp, LinearMap.comp_apply, LinearMap.comp_apply,
    ringScalarExtensionCompIso_hom_apply_pure, infinityCompositionIso_hom_pure,
    ringScalarExtensionCompIso_inv_pure]

/-- The inverse infinity route retains the original outer coefficient and intermediate unit. -/
theorem infinityNaturality_inv_pure (f : R →+* S) (X : category R)
    (t s : _root_.ConeRing S) (x : X) :
    ((infinityNaturality f).inv.app X).hom.hom
        ((ringScalarExtensionCoordinates (_root_.ConeRing.infinityHom S)
            ((coefficientFunctor f).obj X)).symm
          (pure (_root_.ConeRing.infinityHom S) ((coefficientFunctor f).obj X) t
            ((ringScalarExtensionCoordinates (_root_.ConeRing.map f) X).symm
              (pure (_root_.ConeRing.map f) X s x)))) =
      (ringScalarExtensionCoordinates (_root_.ConeRing.map f)
          ((infinityFunctor R).obj X)).symm
        (pure (_root_.ConeRing.map f) ((infinityFunctor R).obj X)
          (t * _root_.ConeRing.infinityHom S s)
          ((ringScalarExtensionCoordinates (_root_.ConeRing.infinityHom R) X).symm
            (pure (_root_.ConeRing.infinityHom R) X 1 x))) := by
  rw [infinityNaturality_inv, NatTrans.comp_app, NatTrans.comp_app,
    hom_hom_comp, hom_hom_comp, LinearMap.comp_apply, LinearMap.comp_apply,
    ringScalarExtensionCompIso_hom_apply_pure, infinityCompositionIso_inv_pure,
    ringScalarExtensionCompIso_inv_pure]

private theorem insert_apply (R : Type uR) [Ring R] (X : category R) (x : X) :
    ((insert R).app X).hom.hom x =
      (ringScalarExtensionCoordinates (_root_.ConeRing.infinityHom R) X).symm
        (pure (_root_.ConeRing.infinityHom R) X (_root_.ConeRing.firstProjection R) x) := by
  apply (ringScalarExtensionCoordinates (_root_.ConeRing.infinityHom R) X).injective
  simpa only [LinearEquiv.apply_symm_apply] using insert_pure R X x

/-- Original insertion commutes with infinity comparison on each projective object. -/
theorem insertNaturality_app (f : R →+* S) (X : category R) :
    (coefficientFunctor f).map ((insert R).app X) ≫ (infinityNaturality f).hom.app X =
      (insert S).app ((coefficientFunctor f).obj X) := by
  apply nativeTwoCompose_ext (_root_.ConeRing.map f) X
    ((coefficientFunctor f).map ((insert R).app X)) ((infinityNaturality f).hom.app X)
  intro t x
  rw [ringScalarExtension_map_pure, insert_apply, infinityNaturality_hom_pure, map_firstProjection]
  apply (ringScalarExtensionCoordinates (_root_.ConeRing.infinityHom S)
    ((coefficientFunctor f).obj X)).injective
  rw [LinearEquiv.apply_symm_apply, insert_pure]
  have hscalar : (ringScalarExtensionCoordinates (_root_.ConeRing.map f) X).symm
      (pure (_root_.ConeRing.map f) X t x) =
      t • (ringScalarExtensionCoordinates (_root_.ConeRing.map f) X).symm
        (pure (_root_.ConeRing.map f) X 1 x) := by
    rw [← LinearEquiv.map_smul, smul_pure, mul_one]
  rw [hscalar]
  exact (congrArg (fun c => pure (_root_.ConeRing.infinityHom S)
      ((coefficientFunctor f).obj X) c
      ((ringScalarExtensionCoordinates (_root_.ConeRing.map f) X).symm
        (pure (_root_.ConeRing.map f) X 1 x))) (firstProjection_intertwines S t)).trans
    (pure_balance (_root_.ConeRing.infinityHom S) ((coefficientFunctor f).obj X) t
      (_root_.ConeRing.firstProjection S)
      ((ringScalarExtensionCoordinates (_root_.ConeRing.map f) X).symm
        (pure (_root_.ConeRing.map f) X 1 x)))

/-- Whole insertion naturality retains the original categorical identity unitor. -/
theorem insertNaturality (f : R →+* S) :
    Functor.whiskerRight (insert R) (coefficientFunctor f) ≫ (infinityNaturality f).hom =
      (Functor.leftUnitor (coefficientFunctor f)).hom ≫
        Functor.whiskerLeft (coefficientFunctor f) (insert S) := by
  apply NatTrans.ext
  funext X
  change (coefficientFunctor f).map ((insert R).app X) ≫ (infinityNaturality f).hom.app X =
    𝟙 ((coefficientFunctor f).obj X) ≫ (insert S).app ((coefficientFunctor f).obj X)
  simpa only [Category.id_comp] using insertNaturality_app f X

/-- Actual infinity coefficient transformations commute with further cone scalar extension. -/
theorem infinityIntertwinerNaturality (f : R →+* S)
    (cR : _root_.ConeRing R) (cS : _root_.ConeRing S)
    (hcR : Intertwines (_root_.ConeRing.infinityHom R) (_root_.ConeRing.infinityHom R) cR)
    (hcS : Intertwines (_root_.ConeRing.infinityHom S) (_root_.ConeRing.infinityHom S) cS)
    (hmap : _root_.ConeRing.map f cR = cS) :
    Functor.whiskerRight
        (ringScalarExtensionIntertwiner
          (_root_.ConeRing.infinityHom R) (_root_.ConeRing.infinityHom R) cR hcR)
        (coefficientFunctor f) ≫ (infinityNaturality f).hom =
      (infinityNaturality f).hom ≫ Functor.whiskerLeft (coefficientFunctor f)
        (ringScalarExtensionIntertwiner
          (_root_.ConeRing.infinityHom S) (_root_.ConeRing.infinityHom S) cS hcS) := by
  exact ringScalarExtensionIntertwiner_commuting_naturality
    (_root_.ConeRing.infinityHom R) (_root_.ConeRing.infinityHom S) (_root_.ConeRing.map f)
    (infinityNaturality f) (infinityNaturality_hom_pure f) cR cS hcR hcS hmap

/-- The original tail projection commutes with the actual whole infinity naturality route. -/
theorem tailProjectionNaturality (f : R →+* S) :
    Functor.whiskerRight (tailProjectionMap R) (coefficientFunctor f) ≫
        (infinityNaturality f).hom =
      (infinityNaturality f).hom ≫
        Functor.whiskerLeft (coefficientFunctor f) (tailProjectionMap S) :=
  infinityIntertwinerNaturality f (_root_.ConeRing.tailProjection R)
    (_root_.ConeRing.tailProjection S) (tailProjection_intertwines R)
    (tailProjection_intertwines S) (map_tailProjection f)

/-- The original tail inclusion commutes with the same actual whole infinity route. -/
theorem tailInclusionNaturality (f : R →+* S) :
    Functor.whiskerRight (tailInclusionMap R) (coefficientFunctor f) ≫
        (infinityNaturality f).hom =
      (infinityNaturality f).hom ≫
        Functor.whiskerLeft (coefficientFunctor f) (tailInclusionMap S) :=
  infinityIntertwinerNaturality f (_root_.ConeRing.tailInclusion R)
    (_root_.ConeRing.tailInclusion S) (tailInclusion_intertwines R)
    (tailInclusion_intertwines S) (map_tailInclusion f)

/-- The actual mapped pointwise biproduct, retaining its original tensor comparison. -/
def sumNaturality (f : R →+* S) :
    sumFunctor R ⋙ coefficientFunctor f ≅ coefficientFunctor f ⋙ sumFunctor S :=
  actualSumComparison (infinityFunctor R) (infinityFunctor S)
    (coefficientFunctor f) (infinityNaturality f)

/-- The comparison is the original biproduct map followed by the original infinity map. -/
theorem sumNaturality_hom_app (f : R →+* S) (X : category R) :
    (sumNaturality f).hom.app X =
      ((coefficientFunctor f).mapBiprod X ((infinityFunctor R).obj X)).hom ≫
        biprod.map (𝟙 ((coefficientFunctor f).obj X)) ((infinityNaturality f).hom.app X) :=
  actualSumComparison_hom_app (infinityFunctor R) (infinityFunctor S)
    (coefficientFunctor f) (infinityNaturality f) X

/-- The original first inclusion remains the first inclusion under the comparison. -/
theorem sumNaturality_inl_app (f : R →+* S) (X : category R) :
    (coefficientFunctor f).map ((sumBicone R).inl.app X) ≫ (sumNaturality f).hom.app X =
      (sumBicone S).inl.app ((coefficientFunctor f).obj X) :=
  actualSumComparison_inl (infinityFunctor R) (infinityFunctor S)
    (coefficientFunctor f) (infinityNaturality f) X

/-- The original second inclusion retains the original infinity comparison. -/
theorem sumNaturality_inr_app (f : R →+* S) (X : category R) :
    (coefficientFunctor f).map ((sumBicone R).inr.app X) ≫ (sumNaturality f).hom.app X =
      (infinityNaturality f).hom.app X ≫
        (sumBicone S).inr.app ((coefficientFunctor f).obj X) :=
  actualSumComparison_inr (infinityFunctor R) (infinityFunctor S)
    (coefficientFunctor f) (infinityNaturality f) X

/-- The actual original first projection is preserved by the mapped biproduct. -/
theorem sumNaturality_fst_app (f : R →+* S) (X : category R) :
    (sumNaturality f).hom.app X ≫ (sumBicone S).fst.app ((coefficientFunctor f).obj X) =
      (coefficientFunctor f).map ((sumBicone R).fst.app X) := by
  rw [sumNaturality_hom_app]
  exact originalMappedSumFst (coefficientFunctor f) X ((infinityFunctor R).obj X)
    ((infinityNaturality f).app X)

/-- The actual original second projection retains the same infinity route. -/
theorem sumNaturality_snd_app (f : R →+* S) (X : category R) :
    (sumNaturality f).hom.app X ≫ (sumBicone S).snd.app ((coefficientFunctor f).obj X) =
      (coefficientFunctor f).map ((sumBicone R).snd.app X) ≫
        (infinityNaturality f).hom.app X := by
  rw [sumNaturality_hom_app]
  exact originalMappedSumSnd (coefficientFunctor f) X ((infinityFunctor R).obj X)
    ((infinityNaturality f).app X)

/-- The whole original absorption square commutes for the actual coefficient ring functor. -/
theorem absorptionNaturality_hom (f : R →+* S) :
    (Functor.isoWhiskerRight (absorption R) (coefficientFunctor f) ≪≫
        infinityNaturality f).hom =
      (sumNaturality f ≪≫
        Functor.isoWhiskerLeft (coefficientFunctor f) (absorption S)).hom := by
  apply NatTrans.ext
  funext X
  change (coefficientFunctor f).map ((absorption R).hom.app X) ≫
      (infinityNaturality f).hom.app X =
    (sumNaturality f).hom.app X ≫ (absorption S).hom.app ((coefficientFunctor f).obj X)
  rw [absorption_hom_app, absorption_hom_app, sumNaturality_hom_app]
  exact originalAbsorptionSquare (coefficientFunctor f) X ((infinityFunctor R).obj X)
    ((infinityNaturality f).app X) ((insert R).app X) ((tailProjectionMap R).app X)
    ((insert S).app ((coefficientFunctor f).obj X))
    ((tailProjectionMap S).app ((coefficientFunctor f).obj X)) (insertNaturality_app f X)
    (congrArg (fun η => η.app X) (tailProjectionNaturality f))

/-- Both actual natural-isomorphism routes of the original absorption square agree. -/
theorem absorptionNaturality (f : R →+* S) :
    Functor.isoWhiskerRight (absorption R) (coefficientFunctor f) ≪≫ infinityNaturality f =
      sumNaturality f ≪≫ Functor.isoWhiskerLeft (coefficientFunctor f) (absorption S) :=
  Iso.ext (absorptionNaturality_hom f)

/-- The actual inverse routes retain both original tensor and biproduct inverses. -/
theorem absorptionNaturality_inv (f : R →+* S) :
    (infinityNaturality f).inv ≫
        Functor.whiskerRight (absorption R).inv (coefficientFunctor f) =
      Functor.whiskerLeft (coefficientFunctor f) (absorption S).inv ≫ (sumNaturality f).inv := by
  simpa only [Iso.trans_inv, Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv]
    using congrArg Iso.inv (absorptionNaturality f)

/-- The original return program commutes with the forward coefficient comparisons. -/
theorem absorptionNaturality_return_app (f : R →+* S) (X : category R) :
    (infinityNaturality f).hom.app X ≫ (absorption S).inv.app ((coefficientFunctor f).obj X) =
      (coefficientFunctor f).map ((absorption R).inv.app X) ≫ (sumNaturality f).hom.app X := by
  have h := congrArg (fun η => η.app X) (absorptionNaturality_hom f)
  exact originalSquareReturn
    ((coefficientFunctor f).mapIso ((absorption R).app X)) ((infinityNaturality f).app X)
    ((sumNaturality f).app X) ((absorption S).app ((coefficientFunctor f).obj X)) h

/-- Original first extraction commutes with the same actual coefficient comparison. -/
theorem extractNaturality_app (f : R →+* S) (X : category R) :
    (infinityNaturality f).hom.app X ≫ (extract S).app ((coefficientFunctor f).obj X) =
      (coefficientFunctor f).map ((extract R).app X) := by
  have hR := congrArg (fun η => η.app X) (absorption_fst R)
  have hS := congrArg (fun η => η.app ((coefficientFunctor f).obj X)) (absorption_fst S)
  simp only [NatTrans.comp_app] at hR hS
  calc
    _ = (infinityNaturality f).hom.app X ≫
        ((absorption S).inv.app ((coefficientFunctor f).obj X) ≫
          (sumBicone S).fst.app ((coefficientFunctor f).obj X)) :=
      congrArg (fun k => (infinityNaturality f).hom.app X ≫ k) hS.symm
    _ = ((coefficientFunctor f).map ((absorption R).inv.app X) ≫
        (sumNaturality f).hom.app X) ≫ (sumBicone S).fst.app ((coefficientFunctor f).obj X) := by
      rw [← Category.assoc, absorptionNaturality_return_app]
    _ = (coefficientFunctor f).map ((absorption R).inv.app X) ≫
        (coefficientFunctor f).map ((sumBicone R).fst.app X) := by
      rw [Category.assoc, sumNaturality_fst_app]
    _ = _ := by rw [← Functor.map_comp, hR]

end FGProjectiveCat.ConeRing

end
