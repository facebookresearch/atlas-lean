/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Category.ModuleCat.Bimodule.Over.MoritaCoordinates
public import Mathlib.CategoryTheory.Equivalence

/-!
# Morita equivalence of bimodule categories

The two tensor functors use coefficient orders `Q–M–P` and `P–N–Q`.
Their return isomorphisms contract the outer tensor pairs and respect the
supplied bimodule actions. The resulting equivalence retains this counit
and adjusts the unit to satisfy the triangle identity.

The maps preserve the supplied ground scalar actions. Tensor carrier
universes are independent, and the category equivalence uses a common
ambient universe.
-/

@[expose] public section

noncomputable section

open CategoryTheory MulOpposite TensorProduct.Balanced
open scoped TensorProduct

universe u r s p q v

namespace ModuleCat.Bimodule.Over.Morita

variable (k : Type u) [CommRing k]
  (R : Type r) [Ring R] [Algebra k R] (S : Type s) [Ring S] [Algebra k S]
  (P : Type p) [AddCommGroup P] [Module k P]
  [Module R P] [Module Sᵐᵒᵖ P] [SMulCommClass R Sᵐᵒᵖ P]
  [IsScalarTower k R P] [IsScalarTower k Sᵐᵒᵖ P]
  (Q : Type q) [AddCommGroup Q] [Module k Q]
  [Module S Q] [Module Rᵐᵒᵖ Q] [SMulCommClass S Rᵐᵒᵖ Q]
  [IsScalarTower k S Q] [IsScalarTower k Rᵐᵒᵖ Q]
  (u : letI := TensorProduct.Balanced.leftModule k S R P Q
    letI := TensorProduct.Balanced.rightModule k S R P Q
    TensorProduct.Balanced k S P Q ≃ₗ[Rᵐᵒᵖ] R)
  (hu : letI := TensorProduct.Balanced.leftModule k S R P Q
    letI := TensorProduct.Balanced.rightModule k S R P Q
    ∀ (r : R) (b : TensorProduct.Balanced k S P Q), u (r • b) = r * u b)

/-- The original native composite object, with its stored module fields. -/
def returnCompositeObject (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ) :=
  ((tensorFunctor k R S P Q) ⋙ (tensorFunctor k S R Q P)).obj X

/-- The original raw coefficient object under the extracted X actions. -/
def returnCoefficientObject (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ) := by
  letI := ModuleCat.Bimodule.Over.groundModule k R X
  letI := ModuleCat.Bimodule.Over.leftModule k R X
  letI := ModuleCat.Bimodule.Over.rightModule k R X
  letI := ModuleCat.Bimodule.Over.leftTower k R X
  letI := ModuleCat.Bimodule.Over.rightTower k R X
  letI := ModuleCat.Bimodule.Over.commute k R X
  exact rawReturnObject k R S P Q X

/-- The same earned coordinate iso with its native objects fixed once. -/
def returnCoordinateIso (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    returnCompositeObject k R S P Q X ≅ returnCoefficientObject k R S P Q X := by
  letI := ModuleCat.Bimodule.Over.groundModule k R X
  letI := ModuleCat.Bimodule.Over.leftModule k R X
  letI := ModuleCat.Bimodule.Over.rightModule k R X
  letI := ModuleCat.Bimodule.Over.leftTower k R X
  letI := ModuleCat.Bimodule.Over.rightTower k R X
  letI := ModuleCat.Bimodule.Over.commute k R X
  exact returnCoordinates k R S P Q X

/-- The actual coordinate hom, bundled from its typed native linear map. -/
def returnCoordinateHom (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    returnCompositeObject k R S P Q X ⟶ returnCoefficientObject k R S P Q X := by
  let D := returnCompositeObject k R S P Q X
  let A := returnCoefficientObject k R S P Q X
  let E : D ≅ A := returnCoordinateIso k R S P Q X
  let L : D →ₗ[R ⊗[k] Rᵐᵒᵖ] A :=
    @ModuleCat.Hom.hom (R ⊗[k] Rᵐᵒᵖ) _ D A E.hom
  exact @ModuleCat.ofHom (R ⊗[k] Rᵐᵒᵖ) _ D.carrier A.carrier
    D.isAddCommGroup D.isModule A.isAddCommGroup A.isModule L

/-- The original inverse coordinate hom, with the same native fields. -/
def returnCoordinateInv (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    returnCoefficientObject k R S P Q X ⟶ returnCompositeObject k R S P Q X := by
  let D := returnCompositeObject k R S P Q X
  let A := returnCoefficientObject k R S P Q X
  let E : D ≅ A := returnCoordinateIso k R S P Q X
  let L : A →ₗ[R ⊗[k] Rᵐᵒᵖ] D :=
    @ModuleCat.Hom.hom (R ⊗[k] Rᵐᵒᵖ) _ A D E.inv
  exact @ModuleCat.ofHom (R ⊗[k] Rᵐᵒᵖ) _ A.carrier D.carrier
    A.isAddCommGroup A.isModule D.isAddCommGroup D.isModule L

private theorem returnCoordinateHom_eq (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    returnCoordinateHom k R S P Q X = (returnCoordinateIso k R S P Q X).hom := by
  change ModuleCat.ofHom ((returnCoordinateIso k R S P Q X).hom.hom) = _
  exact ModuleCat.ofHom_hom (returnCoordinateIso k R S P Q X).hom

private theorem returnCoordinateInv_eq (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    returnCoordinateInv k R S P Q X = (returnCoordinateIso k R S P Q X).inv := by
  change ModuleCat.ofHom ((returnCoordinateIso k R S P Q X).inv.hom) = _
  exact ModuleCat.ofHom_hom (returnCoordinateIso k R S P Q X).inv

/-- The coordinate component retains its actual source inverse law. -/
theorem returnCoordinateHom_inv (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    returnCoordinateHom k R S P Q X ≫ returnCoordinateInv k R S P Q X =
      𝟙 (returnCompositeObject k R S P Q X) := by
  let D := returnCompositeObject k R S P Q X
  let A := returnCoefficientObject k R S P Q X
  exact (congrArg₂ (fun (f : D ⟶ A) (g : A ⟶ D) => f ≫ g)
    (returnCoordinateHom_eq k R S P Q X) (returnCoordinateInv_eq k R S P Q X)).trans
      (returnCoordinateIso k R S P Q X).hom_inv_id

/-- The coordinate component retains its actual target inverse law. -/
theorem returnCoordinateInv_hom (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    returnCoordinateInv k R S P Q X ≫ returnCoordinateHom k R S P Q X =
      𝟙 (returnCoefficientObject k R S P Q X) := by
  let D := returnCompositeObject k R S P Q X
  let A := returnCoefficientObject k R S P Q X
  exact (congrArg₂ (fun (f : A ⟶ D) (g : D ⟶ A) => f ≫ g)
    (returnCoordinateInv_eq k R S P Q X) (returnCoordinateHom_eq k R S P Q X)).trans
      (returnCoordinateIso k R S P Q X).inv_hom_id

include u hu in
/-- The original native contraction hom, using the already-proved linear map. -/
def returnContractionHom (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    returnCoefficientObject k R S P Q X ⟶ ModuleCat.Bimodule.Over.reconstructedObject k R X := by
  letI := ModuleCat.Bimodule.Over.groundModule k R X
  letI := ModuleCat.Bimodule.Over.leftModule k R X
  letI := ModuleCat.Bimodule.Over.rightModule k R X
  letI := ModuleCat.Bimodule.Over.leftTower k R X
  letI := ModuleCat.Bimodule.Over.rightTower k R X
  letI := ModuleCat.Bimodule.Over.commute k R X
  let A := returnCoefficientObject k R S P Q X
  let B := ModuleCat.Bimodule.Over.reconstructedObject k R X
  let L : A →ₗ[R ⊗[k] Rᵐᵒᵖ] B := rawReturnLinear k R S P Q X u hu
  exact @ModuleCat.ofHom (R ⊗[k] Rᵐᵒᵖ) _ A.carrier B.carrier
    A.isAddCommGroup A.isModule B.isAddCommGroup B.isModule L

include u hu in
/-- The original native contraction inverse, using its proved linear map. -/
def returnContractionInv (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    ModuleCat.Bimodule.Over.reconstructedObject k R X ⟶ returnCoefficientObject k R S P Q X := by
  letI := ModuleCat.Bimodule.Over.groundModule k R X
  letI := ModuleCat.Bimodule.Over.leftModule k R X
  letI := ModuleCat.Bimodule.Over.rightModule k R X
  letI := ModuleCat.Bimodule.Over.leftTower k R X
  letI := ModuleCat.Bimodule.Over.rightTower k R X
  letI := ModuleCat.Bimodule.Over.commute k R X
  let A := returnCoefficientObject k R S P Q X
  let B := ModuleCat.Bimodule.Over.reconstructedObject k R X
  let L : B →ₗ[R ⊗[k] Rᵐᵒᵖ] A := rawReturnInverseLinear k R S P Q X u hu
  exact @ModuleCat.ofHom (R ⊗[k] Rᵐᵒᵖ) _ B.carrier A.carrier
    B.isAddCommGroup B.isModule A.isAddCommGroup A.isModule L

include u hu in
/-- The passed native contraction iso with its actual objects fixed. -/
def returnContractionIso (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    returnCoefficientObject k R S P Q X ≅ ModuleCat.Bimodule.Over.reconstructedObject k R X := by
  letI := ModuleCat.Bimodule.Over.groundModule k R X
  letI := ModuleCat.Bimodule.Over.leftModule k R X
  letI := ModuleCat.Bimodule.Over.rightModule k R X
  letI := ModuleCat.Bimodule.Over.leftTower k R X
  letI := ModuleCat.Bimodule.Over.rightTower k R X
  letI := ModuleCat.Bimodule.Over.commute k R X
  exact rawReturnModuleIso k R S P Q X u hu

include u hu in
private theorem returnContractionHom_eq (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    returnContractionHom k R S P Q u hu X = (returnContractionIso k R S P Q u hu X).hom := by
  let := ModuleCat.Bimodule.Over.groundModule k R X
  let := ModuleCat.Bimodule.Over.leftModule k R X
  let := ModuleCat.Bimodule.Over.rightModule k R X
  let := ModuleCat.Bimodule.Over.leftTower k R X
  let := ModuleCat.Bimodule.Over.rightTower k R X
  let := ModuleCat.Bimodule.Over.commute k R X
  let A := returnCoefficientObject k R S P Q X
  let B := ModuleCat.Bimodule.Over.reconstructedObject k R X
  let L : A →ₗ[R ⊗[k] Rᵐᵒᵖ] B := rawReturnLinear k R S P Q X u hu
  apply ModuleCat.hom_ext
  exact (ModuleCat.hom_ofHom L).trans (ModuleCat.hom_ofHom L).symm

include u hu in
private theorem returnContractionInv_eq (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    returnContractionInv k R S P Q u hu X = (returnContractionIso k R S P Q u hu X).inv := by
  let := ModuleCat.Bimodule.Over.groundModule k R X
  let := ModuleCat.Bimodule.Over.leftModule k R X
  let := ModuleCat.Bimodule.Over.rightModule k R X
  let := ModuleCat.Bimodule.Over.leftTower k R X
  let := ModuleCat.Bimodule.Over.rightTower k R X
  let := ModuleCat.Bimodule.Over.commute k R X
  let A := returnCoefficientObject k R S P Q X
  let B := ModuleCat.Bimodule.Over.reconstructedObject k R X
  let L : B →ₗ[R ⊗[k] Rᵐᵒᵖ] A := rawReturnInverseLinear k R S P Q X u hu
  apply ModuleCat.hom_ext
  exact (ModuleCat.hom_ofHom L).trans (ModuleCat.hom_ofHom L).symm

include u hu in
/-- The contraction maps retain their passed native source inverse law. -/
theorem returnContractionHom_inv (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    returnContractionHom k R S P Q u hu X ≫ returnContractionInv k R S P Q u hu X =
      𝟙 (returnCoefficientObject k R S P Q X) := by
  let A := returnCoefficientObject k R S P Q X
  let B := ModuleCat.Bimodule.Over.reconstructedObject k R X
  exact (congrArg₂ (fun (f : A ⟶ B) (g : B ⟶ A) => f ≫ g)
    (returnContractionHom_eq k R S P Q u hu X)
    (returnContractionInv_eq k R S P Q u hu X)).trans
      (returnContractionIso k R S P Q u hu X).hom_inv_id

include u hu in
/-- The contraction maps retain their passed native target inverse law. -/
theorem returnContractionInv_hom (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    returnContractionInv k R S P Q u hu X ≫ returnContractionHom k R S P Q u hu X =
      𝟙 (ModuleCat.Bimodule.Over.reconstructedObject k R X) := by
  let A := returnCoefficientObject k R S P Q X
  let B := ModuleCat.Bimodule.Over.reconstructedObject k R X
  exact (congrArg₂ (fun (f : B ⟶ A) (g : A ⟶ B) => f ≫ g)
    (returnContractionInv_eq k R S P Q u hu X)
    (returnContractionHom_eq k R S P Q u hu X)).trans
      (returnContractionIso k R S P Q u hu X).inv_hom_id

private theorem threeHom_inverse {𝒞 : Type*} [Category 𝒞] {A B C D : 𝒞}
    (c : A ⟶ B) (f : B ⟶ C) (h : C ⟶ D)
    (ci : B ⟶ A) (fi : C ⟶ B) (hi : D ⟶ C)
    (hc : c ≫ ci = 𝟙 A) (hf : f ≫ fi = 𝟙 B) (hh : h ≫ hi = 𝟙 C) :
    (c ≫ (f ≫ h)) ≫ ((hi ≫ fi) ≫ ci) = 𝟙 A := by
  calc
    (c ≫ (f ≫ h)) ≫ ((hi ≫ fi) ≫ ci) =
        c ≫ (f ≫ ((h ≫ hi) ≫ (fi ≫ ci))) := by simp only [Category.assoc]
    _ = c ≫ (f ≫ (fi ≫ ci)) := by rw [hh, Category.id_comp]
    _ = c ≫ ((f ≫ fi) ≫ ci) := by simp only [Category.assoc]
    _ = c ≫ ci := by rw [hf, Category.id_comp]
    _ = 𝟙 A := hc

include u hu in
/-- The actual composite hom, stored independently of its inverse and laws. -/
def returnHom (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    returnCompositeObject k R S P Q X ⟶ X :=
  returnCoordinateHom k R S P Q X ≫
    (returnContractionHom k R S P Q u hu X ≫
      (ModuleCat.Bimodule.Over.reconstructedIso k R X).hom)

include u hu in
/-- The stored hom is exactly the original three native homs. -/
theorem returnHom_parts (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    returnHom k R S P Q u hu X = returnCoordinateHom k R S P Q X ≫
      (returnContractionHom k R S P Q u hu X ≫
        (ModuleCat.Bimodule.Over.reconstructedIso k R X).hom) := rfl

include u hu in
/-- The original inverse grouping of the same three native maps. -/
def returnInverse (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    X ⟶ returnCompositeObject k R S P Q X :=
  ((ModuleCat.Bimodule.Over.reconstructedIso k R X).inv ≫
    returnContractionInv k R S P Q u hu X) ≫ returnCoordinateInv k R S P Q X

include u hu in
/-- The whole source inverse law follows from the three earned component laws. -/
theorem returnHom_inverse (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    returnHom k R S P Q u hu X ≫ returnInverse k R S P Q u hu X =
      𝟙 (returnCompositeObject k R S P Q X) := by
  exact threeHom_inverse (returnCoordinateHom k R S P Q X)
    (returnContractionHom k R S P Q u hu X)
    (ModuleCat.Bimodule.Over.reconstructedIso k R X).hom
    (returnCoordinateInv k R S P Q X) (returnContractionInv k R S P Q u hu X)
    (ModuleCat.Bimodule.Over.reconstructedIso k R X).inv
    (returnCoordinateHom_inv k R S P Q X) (returnContractionHom_inv k R S P Q u hu X)
    (ModuleCat.Bimodule.Over.reconstructedIso k R X).hom_inv_id

include u hu in
/-- The whole target inverse law uses the original reverse component laws. -/
theorem returnInverse_hom (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    returnInverse k R S P Q u hu X ≫ returnHom k R S P Q u hu X = 𝟙 X := by
  have h := threeHom_inverse (ModuleCat.Bimodule.Over.reconstructedIso k R X).inv
    (returnContractionInv k R S P Q u hu X) (returnCoordinateInv k R S P Q X)
    (ModuleCat.Bimodule.Over.reconstructedIso k R X).hom
    (returnContractionHom k R S P Q u hu X) (returnCoordinateHom k R S P Q X)
    (ModuleCat.Bimodule.Over.reconstructedIso k R X).inv_hom_id
    (returnContractionInv_hom k R S P Q u hu X) (returnCoordinateInv_hom k R S P Q X)
  simpa only [returnHom, returnInverse, Category.assoc] using h

include u hu in
/-- The complete return on the same stored native source. -/
def returnObjectIso (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    returnCompositeObject k R S P Q X ≅ X where
  hom := returnHom k R S P Q u hu X
  inv := returnInverse k R S P Q u hu X
  hom_inv_id := returnHom_inverse k R S P Q u hu X
  inv_hom_id := returnInverse_hom k R S P Q u hu X

/-- The identity view between the definitionally identical native objects. -/
def returnObjectViewIso (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    ((tensorFunctor k R S P Q) ⋙ (tensorFunctor k S R Q P)).obj X ≅
      returnCompositeObject k R S P Q X :=
  Iso.refl (returnCompositeObject k R S P Q X)

include u hu in
/-- The earned complete return to the original native enveloping-module object. -/
def returnIso (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    ((tensorFunctor k R S P Q) ⋙ (tensorFunctor k S R Q P)).obj X ≅ X :=
  (returnObjectViewIso k R S P Q X).trans (returnObjectIso k R S P Q u hu X)

/-- The original composite functor through its identical native object view. -/
def returnCompositeViewFunctor :
    ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ) ⥤ ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ) :=
  ((tensorFunctor k R S P Q) ⋙ (tensorFunctor k S R Q P)).copyObj
    (returnCompositeObject k R S P Q) (returnObjectViewIso k R S P Q)

/-- The original native composite map on the same stored source and target objects. -/
def returnCompositeMap {X Y : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)} (f : X ⟶ Y) :
    returnCompositeObject k R S P Q X ⟶ returnCompositeObject k R S P Q Y :=
  ((tensorFunctor k R S P Q) ⋙ (tensorFunctor k S R Q P)).map f

/-- The direct map retains its original native composite-map expression. -/
theorem returnCompositeMap_eq {X Y : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)} (f : X ⟶ Y) :
    returnCompositeMap k R S P Q f =
      (show returnCompositeObject k R S P Q X ⟶ returnCompositeObject k R S P Q Y from
        ((tensorFunctor k R S P Q) ⋙ (tensorFunctor k S R Q P)).map f) := by
  rfl

private theorem abstractCopyObj_map {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
    (F : 𝒞 ⥤ 𝒟) (obj : 𝒞 → 𝒟) (e : ∀ X, F.obj X ≅ obj X)
    {X Y : 𝒞} (f : X ⟶ Y) :
    (F.copyObj obj e).map f = (e X).inv ≫ F.map f ≫ (e Y).hom := rfl

private def abstractViewMap {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
    (F : 𝒞 ⥤ 𝒟) (obj : 𝒞 → 𝒟) (e : ∀ Z, F.obj Z ≅ obj Z)
    {X Y : 𝒞} (f : X ⟶ Y) : obj X ⟶ obj Y :=
  (e X).inv ≫ F.map f ≫ (e Y).hom

private theorem abstractViewMap_eq {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
    (F : 𝒞 ⥤ 𝒟) (obj : 𝒞 → 𝒟) (e : ∀ Z, F.obj Z ≅ obj Z)
    {X Y : 𝒞} (f : X ⟶ Y) :
    (F.copyObj obj e).map f = abstractViewMap F obj e f :=
  abstractCopyObj_map F obj e f

private theorem abstractIdentityViewMap_eq {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
    (F : 𝒞 ⥤ 𝒟) {X Y : 𝒞} (f : X ⟶ Y) :
    abstractViewMap F F.obj (fun Z => Iso.refl (F.obj Z)) f = F.map f := by
  simp only [abstractViewMap, Iso.refl_hom, Iso.refl_inv,
    Category.id_comp, Category.comp_id]

private def returnViewMap {X Y : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)}
    (f : X ⟶ Y) :
    returnCompositeObject k R S P Q X ⟶ returnCompositeObject k R S P Q Y := by
  let H : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ) ⥤
      ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ) :=
    (tensorFunctor k R S P Q) ⋙ (tensorFunctor k S R Q P)
  exact abstractViewMap H (returnCompositeObject k R S P Q)
    (returnObjectViewIso k R S P Q) (X := X) (Y := Y) f

private theorem returnViewMap_eq {X Y : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)}
    (f : X ⟶ Y) :
    returnViewMap k R S P Q f = returnCompositeMap k R S P Q f := by
  let H : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ) ⥤
      ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ) :=
    (tensorFunctor k R S P Q) ⋙ (tensorFunctor k S R Q P)
  exact abstractIdentityViewMap_eq H (X := X) (Y := Y) f

private def returnCoordinateValue (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    P → returnIntermediateCarrier k R S P Q X → Q →
      (returnCoefficientObject k R S P Q X).carrier := by
  let D := returnCompositeObject k R S P Q X
  let A := returnCoefficientObject k R S P Q X
  let L : D →ₗ[R ⊗[k] Rᵐᵒᵖ] A :=
    @ModuleCat.Hom.hom (R ⊗[k] Rᵐᵒᵖ) _ D A (returnCoordinateHom k R S P Q X)
  exact fun p₀ c q₁ => L (returnOuterMk k R S P Q X p₀ c q₁)

private def returnCoordinateTargetValue (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    P → returnIntermediateCarrier k R S P Q X → Q →
      (returnCoefficientObject k R S P Q X).carrier := by
  letI := ModuleCat.Bimodule.Over.groundModule k R X
  letI := ModuleCat.Bimodule.Over.leftModule k R X
  letI := ModuleCat.Bimodule.Over.rightModule k R X
  letI := ModuleCat.Bimodule.Over.leftTower k R X
  letI := ModuleCat.Bimodule.Over.rightTower k R X
  letI := ModuleCat.Bimodule.Over.commute k R X
  exact fun p₀ c q₁ => rawReturnOuterMk k R S P Q X p₀ c q₁

private theorem returnCoordinateValue_eq (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    returnCoordinateValue k R S P Q X = returnCoordinateTargetValue k R S P Q X := by
  let := ModuleCat.Bimodule.Over.groundModule k R X
  let := ModuleCat.Bimodule.Over.leftModule k R X
  let := ModuleCat.Bimodule.Over.rightModule k R X
  let := ModuleCat.Bimodule.Over.leftTower k R X
  let := ModuleCat.Bimodule.Over.rightTower k R X
  let := ModuleCat.Bimodule.Over.commute k R X
  let D := returnCompositeObject k R S P Q X
  let A := returnCoefficientObject k R S P Q X
  funext p₀ c q₁
  let z : D := returnOuterMk k R S P Q X p₀ c q₁
  have h := congrArg
    (fun f : D ⟶ A => (@ModuleCat.Hom.hom (R ⊗[k] Rᵐᵒᵖ) _ D A f) z)
    (returnCoordinateHom_eq k R S P Q X)
  exact h.trans (returnCoordinates_mk k R S P Q X p₀ c q₁)

private theorem returnCoordinateHom_mk (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ))
    (p₀ : P) (c : returnIntermediateCarrier k R S P Q X) (q₁ : Q) :
    returnCoordinateValue k R S P Q X p₀ c q₁ =
      returnCoordinateTargetValue k R S P Q X p₀ c q₁ :=
  congrFun (congrFun (congrFun (returnCoordinateValue_eq k R S P Q X) p₀) c) q₁

include u hu in
private def returnContractionValue (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    (returnCoefficientObject k R S P Q X).carrier → X := by
  let A := returnCoefficientObject k R S P Q X
  let B := ModuleCat.Bimodule.Over.reconstructedObject k R X
  let L : A →ₗ[R ⊗[k] Rᵐᵒᵖ] B :=
    @ModuleCat.Hom.hom (R ⊗[k] Rᵐᵒᵖ) _ A B (returnContractionHom k R S P Q u hu X)
  exact fun b => L b

private theorem ofHomFunction_heq {R' : Type*} [Ring R']
    {A B : ModuleCat R'} (L : A →ₗ[R'] B) :
    HEq (fun x : A.carrier =>
      (@ModuleCat.Hom.hom R' _ A B
        (@ModuleCat.ofHom R' _ A.carrier B.carrier
          A.isAddCommGroup A.isModule B.isAddCommGroup B.isModule L)) x) L.toFun :=
  heq_of_eq (congrArg (fun f : A →ₗ[R'] B => f.toFun) (ModuleCat.hom_ofHom L))

private theorem applyFunctionHEq (A B : Type v) (M : Type*)
    (f : A → M) (g : B → M)
    (x : A) (y : B) (hf : HEq f g) (hx : HEq x y) : f x = g y := by
  cases hx
  exact congrFun (eq_of_heq hf) x

include u hu in
private theorem rawReturnLinearFunction_heq
    (M : Type (max p q v)) [gM : AddCommGroup M] [dK : Module k M]
    [dR : Module R M] [dRop : Module Rᵐᵒᵖ M]
    [cM : SMulCommClass R Rᵐᵒᵖ M]
    [tL : IsScalarTower k R M] [tR : IsScalarTower k Rᵐᵒᵖ M] :
    letI : Module (R ⊗[k] Rᵐᵒᵖ) M := TensorProduct.Algebra.module
    HEq (rawReturnLinear k R S P Q M u hu).toFun
      (rawReturnModuleHom.{u, r, s, p, q, v} k R S P Q M u hu) := by
  let : Module (R ⊗[k] Rᵐᵒᵖ) M := TensorProduct.Algebra.module
  have hField : HEq (rawReturnLinear k R S P Q M u hu).toFun
      (rawReturnIso k R S P Q M u hu).toFun := HEq.rfl
  exact hField.trans (rawReturnModuleHom_heq.{u, r, s, p, q, v} k R S P Q M u hu).symm

include u hu in
private theorem returnContractionValue_eq (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    letI := ModuleCat.Bimodule.Over.groundModule k R X
    letI := ModuleCat.Bimodule.Over.leftModule k R X
    letI := ModuleCat.Bimodule.Over.rightModule k R X
    letI := ModuleCat.Bimodule.Over.leftTower k R X
    letI := ModuleCat.Bimodule.Over.rightTower k R X
    letI := ModuleCat.Bimodule.Over.commute k R X
    HEq (returnContractionValue k R S P Q u hu X)
      (rawReturnModuleHom k R S P Q X u hu) := by
  let := ModuleCat.Bimodule.Over.groundModule k R X
  let := ModuleCat.Bimodule.Over.leftModule k R X
  let := ModuleCat.Bimodule.Over.rightModule k R X
  let := ModuleCat.Bimodule.Over.leftTower k R X
  let := ModuleCat.Bimodule.Over.rightTower k R X
  let := ModuleCat.Bimodule.Over.commute k R X
  let A := returnCoefficientObject k R S P Q X
  let B := ModuleCat.Bimodule.Over.reconstructedObject k R X
  let rawDomain : Type (max p q v) := (rawReturnObject k R S P Q X).carrier
  let L : A →ₗ[R ⊗[k] Rᵐᵒᵖ] B := rawReturnLinear k R S P Q X u hu
  have hSame : returnContractionValue k R S P Q u hu X =
      (fun b : A.carrier => (@ModuleCat.Hom.hom (R ⊗[k] Rᵐᵒᵖ) _ A B
        (returnContractionIso k R S P Q u hu X).hom) b) :=
    congrArg (fun f : A ⟶ B => fun b : A.carrier =>
      (@ModuleCat.Hom.hom (R ⊗[k] Rᵐᵒᵖ) _ A B f) b)
      (returnContractionHom_eq k R S P Q u hu X)
  have hField : HEq
      (fun b : A.carrier => (@ModuleCat.Hom.hom (R ⊗[k] Rᵐᵒᵖ) _ A B
        (returnContractionIso k R S P Q u hu X).hom) b) L.toFun :=
    ofHomFunction_heq L
  have hRaw := rawReturnLinearFunction_heq.{u, r, s, p, q, v}
    (k := k) (R := R) (S := S) (P := P) (Q := Q) (u := u) (hu := hu)
    (M := X.carrier) (gM := X.isAddCommGroup)
    (dK := ModuleCat.Bimodule.Over.groundModule k R X)
    (dR := ModuleCat.Bimodule.Over.leftModule k R X)
    (dRop := ModuleCat.Bimodule.Over.rightModule k R X)
    (cM := ModuleCat.Bimodule.Over.commute k R X)
    (tL := ModuleCat.Bimodule.Over.leftTower k R X)
    (tR := ModuleCat.Bimodule.Over.rightTower k R X)
  exact (heq_of_eq hSame).trans (hField.trans hRaw)

include u hu in
private def returnOrderedValue (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    P → Q → X → P → Q → X :=
  fun p₀ q₀ x p₁ q₁ => X.isModule.smul
    (contractionScalar k R S P Q u p₀ q₀ ⊗ₜ[k]
      op (contractionScalar k R S P Q u p₁ q₁)) x

include u hu in
/-- The actual return hom evaluated on its original five factors. -/
private def returnIsoValue (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    P → Q → X → P → Q → X := by
  let T := returnCompositeObject k R S P Q X
  let L : T →ₗ[R ⊗[k] Rᵐᵒᵖ] X :=
    @ModuleCat.Hom.hom (R ⊗[k] Rᵐᵒᵖ) _ T X (returnHom k R S P Q u hu X)
  exact fun p₀ q₀ x p₁ q₁ =>
    L (returnOuterMk k R S P Q X p₀ (tensorMk k R S P Q X q₀ x p₁) q₁)

include u hu in
/-- The original three constituent homs give the existing ordered return value. -/
private theorem returnIsoValue_eq (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    returnIsoValue k R S P Q u hu X = returnOrderedValue (k := k) (R := R) (S := S) (P := P)
        (Q := Q) (u := u) X := by
  let := ModuleCat.Bimodule.Over.groundModule k R X
  let := ModuleCat.Bimodule.Over.leftModule k R X
  let := ModuleCat.Bimodule.Over.rightModule k R X
  let := ModuleCat.Bimodule.Over.leftTower k R X
  let := ModuleCat.Bimodule.Over.rightTower k R X
  let := ModuleCat.Bimodule.Over.commute k R X
  let T := returnCompositeObject k R S P Q X
  let A := returnCoefficientObject k R S P Q X
  let B := ModuleCat.Bimodule.Over.reconstructedObject k R X
  let cMap : T →ₗ[R ⊗[k] Rᵐᵒᵖ] A :=
    @ModuleCat.Hom.hom (R ⊗[k] Rᵐᵒᵖ) _ T A (returnCoordinateHom k R S P Q X)
  let fMap : A →ₗ[R ⊗[k] Rᵐᵒᵖ] B :=
    @ModuleCat.Hom.hom (R ⊗[k] Rᵐᵒᵖ) _ A B (returnContractionHom k R S P Q u hu X)
  let hMap : B →ₗ[R ⊗[k] Rᵐᵒᵖ] X :=
    @ModuleCat.Hom.hom (R ⊗[k] Rᵐᵒᵖ) _ B X
      (ModuleCat.Bimodule.Over.reconstructedIso k R X).hom
  have hIso : returnHom k R S P Q u hu X = returnCoordinateHom k R S P Q X ≫
      (returnContractionHom k R S P Q u hu X ≫
        (ModuleCat.Bimodule.Over.reconstructedIso k R X).hom) :=
    returnHom_parts k R S P Q u hu X
  funext p₀ q₀ x p₁ q₁
  let c : tensorObj k R S P Q X := tensorMk k R S P Q X q₀ x p₁
  let z : T := returnOuterMk k R S P Q X p₀ c q₁
  let b : A := rawReturnModuleMk k R S P Q X p₀ q₀ x p₁ q₁
  have hC : cMap z = b := returnCoordinateHom_mk k R S P Q X p₀ c q₁
  have hF : fMap b = orderedReturnValue k R S P Q X u p₀ q₀ x p₁ q₁ := by
    let rawPoint : rawReturnObject k R S P Q X :=
      rawReturnModuleMk k R S P Q X p₀ q₀ x p₁ q₁
    have hPoint : HEq b rawPoint := HEq.rfl
    have hNative : fMap b = rawReturnModuleHom k R S P Q X u hu rawPoint :=
      applyFunctionHEq A.carrier (rawReturnObject k R S P Q X).carrier X.carrier
        (returnContractionValue k R S P Q u hu X) (rawReturnModuleHom k R S P Q X u hu)
        b rawPoint (returnContractionValue_eq k R S P Q u hu X) hPoint
    exact hNative.trans
      ((nativeReturnValue_apply k R S P Q X u hu p₀ q₀ x p₁ q₁).symm.trans
        (rawReturnModuleIso_hom_mk k R S P Q X u hu p₀ q₀ x p₁ q₁))
  have hApply : returnIsoValue k R S P Q u hu X p₀ q₀ x p₁ q₁ =
      hMap (fMap (cMap z)) := by
    have h := congrArg
      (fun f : T ⟶ X => (@ModuleCat.Hom.hom (R ⊗[k] Rᵐᵒᵖ) _ T X f) z) hIso
    exact h
  exact hApply.trans
    ((congrArg (fun y : A => hMap (fMap y)) hC).trans
      ((ModuleCat.Bimodule.Over.reconstructedIso_hom_apply k R X (fMap b)).trans
        (hF.trans ((orderedReturnValue_apply k R S P Q X u p₀ q₀ x p₁ q₁).trans
          (ModuleCat.Bimodule.Over.smul_tmul k R X
            (contractionScalar k R S P Q u p₀ q₀)
            (op (contractionScalar k R S P Q u p₁ q₁)) x)))))

/-- The actual return contracts the two outer pairs and uses the original stored R-bimodule
action. -/
-- keeps the actual composite-object getter for rw; Functor.comp_obj simplifies its source
@[simp, nolint simpNF]
theorem returnIso_mk (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ))
    (p₀ : P) (q₀ : Q) (x : X) (p₁ : P) (q₁ : Q) :
    letI := ModuleCat.Bimodule.Over.groundModule k R X
    letI := ModuleCat.Bimodule.Over.leftModule k R X
    letI := ModuleCat.Bimodule.Over.rightModule k R X
    letI := ModuleCat.Bimodule.Over.leftTower k R X
    letI := ModuleCat.Bimodule.Over.rightTower k R X
    letI := ModuleCat.Bimodule.Over.commute k R X
    letI := TensorProduct.Balanced.rightModule k R R Q X
    let T : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ) :=
      ((tensorFunctor k R S P Q) ⋙ (tensorFunctor k S R Q P)).obj X
    (@ModuleCat.Hom.hom (R ⊗[k] Rᵐᵒᵖ) _ T X
      (show T ⟶ X from (returnIso k R S P Q u hu X).hom))
        (returnOuterMk k R S P Q X p₀ (tensorMk k R S P Q X q₀ x p₁) q₁) =
      X.isModule.smul
        (contractionScalar k R S P Q u p₀ q₀ ⊗ₜ[k]
          op (contractionScalar k R S P Q u p₁ q₁)) x := by
  let := ModuleCat.Bimodule.Over.groundModule k R X
  let := ModuleCat.Bimodule.Over.leftModule k R X
  let := ModuleCat.Bimodule.Over.rightModule k R X
  let := ModuleCat.Bimodule.Over.leftTower k R X
  let := ModuleCat.Bimodule.Over.rightTower k R X
  let := ModuleCat.Bimodule.Over.commute k R X
  let := TensorProduct.Balanced.rightModule k R R Q X
  change returnIsoValue k R S P Q u hu X p₀ q₀ x p₁ q₁ =
    returnOrderedValue (k := k) (R := R) (S := S) (P := P) (Q := Q) (u := u) X p₀ q₀ x p₁ q₁
  exact congrFun (congrFun (congrFun (congrFun (congrFun
    (returnIsoValue_eq k R S P Q u hu X) p₀) q₀) x) p₁) q₁

include u hu in
private def returnNaturalityHomLeft {X Y : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)}
    (f : X ⟶ Y) : returnCompositeObject k R S P Q X ⟶ Y :=
  returnCompositeMap k R S P Q f ≫ returnHom k R S P Q u hu Y

include u hu in
private def returnNaturalityHomRight {X Y : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)}
    (f : X ⟶ Y) : returnCompositeObject k R S P Q X ⟶ Y :=
  returnHom k R S P Q u hu X ≫ f

include u hu in
private def returnNaturalityLeft {X Y : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)}
    (f : X ⟶ Y) : P → Q → X → P → Q → Y := by
  let D := returnCompositeObject k R S P Q X
  let E := returnCompositeObject k R S P Q Y
  let F : D →ₗ[R ⊗[k] Rᵐᵒᵖ] E :=
    @ModuleCat.Hom.hom (R ⊗[k] Rᵐᵒᵖ) _ D E (returnCompositeMap k R S P Q f)
  let G : E →ₗ[R ⊗[k] Rᵐᵒᵖ] Y :=
    @ModuleCat.Hom.hom (R ⊗[k] Rᵐᵒᵖ) _ E Y (returnHom k R S P Q u hu Y)
  exact fun p₀ q₀ x p₁ q₁ => G (F
    (returnOuterMk k R S P Q X p₀ (tensorMk k R S P Q X q₀ x p₁) q₁))

include u hu in
private def returnNaturalityRight {X Y : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)}
    (f : X ⟶ Y) : P → Q → X → P → Q → Y :=
  fun p₀ q₀ x p₁ q₁ => f.hom (returnIsoValue k R S P Q u hu X p₀ q₀ x p₁ q₁)

private def returnCompositePureValue
    {X Y : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)} (f : X ⟶ Y) :
    P → Q → X → P → Q → returnCompositeCarrier k R S P Q Y := by
  let D := returnCompositeObject k R S P Q X
  let E := returnCompositeObject k R S P Q Y
  let L : D →ₗ[R ⊗[k] Rᵐᵒᵖ] E :=
    @ModuleCat.Hom.hom (R ⊗[k] Rᵐᵒᵖ) _ D E (returnCompositeMap k R S P Q f)
  exact fun p₀ q₀ x p₁ q₁ =>
    L (returnOuterMk k R S P Q X p₀ (tensorMk k R S P Q X q₀ x p₁) q₁)

private def returnCompositeMappedPureValue
    {X Y : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)} (f : X ⟶ Y) :
    P → Q → X → P → Q → returnCompositeCarrier k R S P Q Y :=
  fun p₀ q₀ x p₁ q₁ =>
    returnOuterMk k R S P Q Y p₀ (tensorMk k R S P Q Y q₀ (f.hom x) p₁) q₁

private theorem returnCompositeMapValues_eq
    {X Y : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)} (f : X ⟶ Y) :
    (returnCompositePureValue.{u, r, s, p, q, v} k R S P Q (X := X) (Y := Y) f :
      P → Q → X → P → Q → returnCompositeCarrier k R S P Q Y) =
      returnCompositeMappedPureValue.{u, r, s, p, q, v} k R S P Q (X := X) (Y := Y) f := by
  let F : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ) ⥤
      ModuleCat.{max p q v} (S ⊗[k] Sᵐᵒᵖ) := tensorFunctor k R S P Q
  let G : ModuleCat.{max p q v} (S ⊗[k] Sᵐᵒᵖ) ⥤
      ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ) := tensorFunctor k S R Q P
  let D := returnCompositeObject k R S P Q X
  let E := returnCompositeObject k R S P Q Y
  let pre (h : P → returnIntermediateCarrier k R S P Q X → Q →
      returnCompositeCarrier k R S P Q Y) :
      P → Q → X → P → Q → returnCompositeCarrier k R S P Q Y :=
    fun p₀ q₀ x p₁ q₁ => h p₀ (tensorMk k R S P Q X q₀ x p₁) q₁
  have hArrow : returnCompositeMap k R S P Q f =
      (show D ⟶ E from tensorMap k S R Q P (F.map f)) :=
    (returnCompositeMap_eq k R S P Q f).trans
      (returnComposite_map.{u, r, s, p, q, v} k R S P Q (X := X) (Y := Y) f)
  have hArrowValues := congrArg
    (fun a : D ⟶ E => fun (p₀ : P)
      (c : returnIntermediateCarrier k R S P Q X) (q₁ : Q) =>
      (@ModuleCat.Hom.hom (R ⊗[k] Rᵐᵒᵖ) _ D E a)
        (returnOuterMk k R S P Q X p₀ c q₁)) hArrow
  have hNative : returnCompositePureValue k R S P Q f =
      pre (returnOuterMapValue k R S P Q f) :=
    congrArg pre hArrowValues
  have hOuter := congrArg pre
    (returnOuterMapValue_eq.{u, r, s, p, q, v} k R S P Q (X := X) (Y := Y) f)
  let innerActual : Q → X → P → returnIntermediateCarrier k R S P Q Y :=
    fun q₀ x p₁ => (tensorMap k R S P Q f).hom (tensorMk k R S P Q X q₀ x p₁)
  let innerExpected : Q → X → P → returnIntermediateCarrier k R S P Q Y :=
    fun q₀ x p₁ => tensorMk k R S P Q Y q₀ (f.hom x) p₁
  have hInner : innerActual = innerExpected := by
    funext q₀ x p₁
    exact tensorMap_mk k R S P Q f q₀ x p₁
  let put (h : Q → X → P → returnIntermediateCarrier k R S P Q Y) :
      P → Q → X → P → Q → returnCompositeCarrier k R S P Q Y :=
    fun p₀ q₀ x p₁ q₁ => returnOuterMk k R S P Q Y p₀ (h q₀ x p₁) q₁
  exact hNative.trans (hOuter.trans (congrArg put hInner))

include u hu in
private theorem returnHom_pure_value (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ))
    (p₀ : P) (q₀ : Q) (x : X) (p₁ : P) (q₁ : Q) :
    (returnHom k R S P Q u hu X).hom
      (returnOuterMk k R S P Q X p₀ (tensorMk k R S P Q X q₀ x p₁) q₁) =
    X.isModule.smul
      (contractionScalar k R S P Q u p₀ q₀ ⊗ₜ[k]
        op (contractionScalar k R S P Q u p₁ q₁)) x := by
  exact congrFun (congrFun (congrFun (congrFun (congrFun
    (returnIsoValue_eq.{u, r, s, p, q, v} k R S P Q u hu X) p₀) q₀) x) p₁) q₁

include u hu in
private theorem returnNaturalityValue_eq
    {X Y : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)} (f : X ⟶ Y) :
    (returnNaturalityLeft.{u, r, s, p, q, v} k R S P Q u hu (X := X) (Y := Y) f :
      P → Q → X → P → Q → Y) =
      returnNaturalityRight.{u, r, s, p, q, v} k R S P Q u hu (X := X) (Y := Y) f := by
  let E := returnCompositeObject k R S P Q Y
  let L : E →ₗ[R ⊗[k] Rᵐᵒᵖ] Y :=
    @ModuleCat.Hom.hom (R ⊗[k] Rᵐᵒᵖ) _ E Y (returnHom k R S P Q u hu Y)
  let post (h : P → Q → X → P → Q → returnCompositeCarrier k R S P Q Y) :
      P → Q → X → P → Q → Y := fun p₀ q₀ x p₁ q₁ => L (h p₀ q₀ x p₁ q₁)
  have hMap := congrArg post
    (returnCompositeMapValues_eq.{u, r, s, p, q, v} k R S P Q (X := X) (Y := Y) f)
  let inY (h : P → Q → Y → P → Q → Y) : P → Q → X → P → Q → Y :=
    fun p₀ q₀ x p₁ q₁ => h p₀ q₀ (f.hom x) p₁ q₁
  let outX (h : P → Q → X → P → Q → X) : P → Q → X → P → Q → Y :=
    fun p₀ q₀ x p₁ q₁ => f.hom (h p₀ q₀ x p₁ q₁)
  have hY := congrArg inY (returnIsoValue_eq.{u, r, s, p, q, v} k R S P Q u hu Y)
  have hX := congrArg outX (returnIsoValue_eq.{u, r, s, p, q, v} k R S P Q u hu X)
  have hScalar :
      inY (returnOrderedValue.{u, r, s, p, q, v} k R S P Q u Y) =
      outX (returnOrderedValue.{u, r, s, p, q, v} k R S P Q u X) := by
    funext p₀ q₀ x p₁ q₁
    exact (f.hom.map_smul
      (contractionScalar k R S P Q u p₀ q₀ ⊗ₜ[k]
        op (contractionScalar k R S P Q u p₁ q₁)) x).symm
  exact hMap.trans (hY.trans (hScalar.trans hX.symm))

private theorem abstractCompositionAdditive_apply {T : Type*} [Ring T]
    {A B C : ModuleCat T} (f : A ⟶ B) (g : B ⟶ C) (x : A.carrier) :
    ((f ≫ g).hom.toAddMonoidHom) x = g.hom (f.hom x) :=
  congrArg (fun L : A →ₗ[T] C => L.toAddMonoidHom x) (ModuleCat.hom_comp f g)

include u hu in
/-- Naturality of the actual return hom, proved independently of packaging. -/
private theorem returnIso_naturality
    {X Y : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)} (f : X ⟶ Y) :
    returnNaturalityHomLeft.{u, r, s, p, q, v} k R S P Q u hu (X := X) (Y := Y) f =
      returnNaturalityHomRight.{u, r, s, p, q, v} k R S P Q u hu (X := X) (Y := Y) f := by

  let := ModuleCat.Bimodule.Over.groundModule k R X
  let := ModuleCat.Bimodule.Over.leftModule k R X
  let := ModuleCat.Bimodule.Over.rightModule k R X
  let := ModuleCat.Bimodule.Over.leftTower k R X
  let := ModuleCat.Bimodule.Over.rightTower k R X
  let := ModuleCat.Bimodule.Over.commute k R X
  let := ModuleCat.Bimodule.Over.groundModule k R Y
  let := ModuleCat.Bimodule.Over.leftModule k R Y
  let := ModuleCat.Bimodule.Over.rightModule k R Y
  let := ModuleCat.Bimodule.Over.leftTower k R Y
  let := ModuleCat.Bimodule.Over.rightTower k R Y
  let := ModuleCat.Bimodule.Over.commute k R Y
  let := TensorProduct.Balanced.rightModule k R R Q X
  let := TensorProduct.Balanced.rightModule k R R Q Y
  let H : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ) ⥤
      ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ) :=
    (tensorFunctor k R S P Q) ⋙ (tensorFunctor k S R Q P)
  let left : H.obj X ⟶ Y :=
    show H.obj X ⟶ Y from
      returnNaturalityHomLeft.{u, r, s, p, q, v} k R S P Q u hu (X := X) (Y := Y) f
  let right : H.obj X ⟶ Y :=
    show H.obj X ⟶ Y from
      returnNaturalityHomRight.{u, r, s, p, q, v} k R S P Q u hu (X := X) (Y := Y) f
  let L : H.obj X →+ Y.carrier :=
    (@ModuleCat.Hom.hom (R ⊗[k] Rᵐᵒᵖ) _ (H.obj X) Y left).toAddMonoidHom
  let R' : H.obj X →+ Y.carrier :=
    (@ModuleCat.Hom.hom (R ⊗[k] Rᵐᵒᵖ) _ (H.obj X) Y right).toAddMonoidHom
  have hAdd : L = R' := by
    refine returnHom_ext.{u, r, s, p, q, v} k R S P Q X
      (C' := Y.carrier) (f := L) (g := R') ?_
    intro p₀ q₀ x p₁ q₁
    let z : H.obj X := returnOuterMk k R S P Q X p₀
      (TensorProduct.Balanced.mk k R (TensorProduct.Balanced k R Q X) P
        (TensorProduct.Balanced.mk k R Q X q₀ x) p₁) q₁
    have hLeft := abstractCompositionAdditive_apply
      (returnCompositeMap k R S P Q f) (returnHom k R S P Q u hu Y) z
    have hRight := abstractCompositionAdditive_apply
      (returnHom k R S P Q u hu X) f z
    have hPoint := congrFun (congrFun (congrFun (congrFun (congrFun
      (returnNaturalityValue_eq.{u, r, s, p, q, v} k R S P Q u hu
        (X := X) (Y := Y) f) p₀) q₀) x) p₁) q₁
    exact hLeft.trans (hPoint.trans hRight.symm)
  exact ModuleCat.hom_ext (LinearMap.toAddMonoidHom_injective hAdd)

/-- Construct the natural isomorphism on copied objects from its actual transported maps. -/
def abstractViewComponents {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
    (F G : 𝒞 ⥤ 𝒟) (obj : 𝒞 → 𝒟) (e : ∀ Z, F.obj Z ≅ obj Z)
    (app : ∀ Z, obj Z ≅ G.obj Z)
    (naturality : ∀ {X Y : 𝒞} (f : X ⟶ Y),
      ((e X).inv ≫ F.map f ≫ (e Y).hom) ≫ (app Y).hom =
        (app X).hom ≫ G.map f) :
    F.copyObj obj e ≅ G :=
  NatIso.ofComponents (F := F.copyObj obj e) (G := G) app
    (fun {X Y} f => by
      have hMap : (F.copyObj obj e).map f =
          (e X).inv ≫ F.map f ≫ (e Y).hom := rfl
      exact (congrArg (fun g : obj X ⟶ obj Y => g ≫ (app Y).hom) hMap).trans
        (naturality f))

include u hu in
private theorem returnObjectIso_hom (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    (returnObjectIso.{u, r, s, p, q, v} k R S P Q u hu X).hom =
      returnHom.{u, r, s, p, q, v} k R S P Q u hu X := rfl

include u hu in
/-- The same actual naturality on the stored native object view. -/
def returnTypedNatIso :
    returnCompositeViewFunctor k R S P Q ≅
      𝟭 (ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) := by
  let H : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ) ⥤
      ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ) :=
    (tensorFunctor.{u, r, s, p, q, max p q v} k R S P Q) ⋙
      (tensorFunctor.{u, s, r, q, p, max p q v} k S R Q P)
  exact abstractViewComponents H
    (𝟭 (ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)))
    (returnCompositeObject.{u, r, s, p, q, v} k R S P Q)
    (returnObjectViewIso.{u, r, s, p, q, v} k R S P Q)
    (returnObjectIso.{u, r, s, p, q, v} k R S P Q u hu)
    (fun {X Y} f => by
      have hNative := returnIso_naturality.{u, r, s, p, q, v}
        k R S P Q u hu (X := X) (Y := Y) f
      change returnCompositeMap k R S P Q f ≫ returnHom k R S P Q u hu Y =
        returnHom k R S P Q u hu X ≫ f at hNative
      have hAccessor := congrArg
        (fun g : returnCompositeObject k R S P Q X ⟶ returnCompositeObject k R S P Q Y =>
          g ≫ returnHom k R S P Q u hu Y)
        (returnViewMap_eq.{u, r, s, p, q, v} k R S P Q (X := X) (Y := Y) f)
      have hReal := hAccessor.trans hNative
      calc
        _ = returnViewMap k R S P Q f ≫ returnHom k R S P Q u hu Y :=
          congrArg
            (fun g : returnCompositeObject k R S P Q Y ⟶ Y =>
              returnViewMap k R S P Q f ≫ g)
            (returnObjectIso_hom.{u, r, s, p, q, v} k R S P Q u hu Y)
        _ = returnHom k R S P Q u hu X ≫ f := hReal
        _ = _ := congrArg
          (fun g : returnCompositeObject k R S P Q X ⟶ X => g ≫ f)
          (returnObjectIso_hom.{u, r, s, p, q, v} k R S P Q u hu X).symm)

include u hu in
/-- The actual composite contraction is natural in the original native bimodule morphism. -/
def returnNatIso :
    (tensorFunctor k R S P Q) ⋙ (tensorFunctor k S R Q P) ≅
      𝟭 (ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :=
  (((tensorFunctor k R S P Q) ⋙ (tensorFunctor k S R Q P)).isoCopyObj
    (returnCompositeObject k R S P Q) (returnObjectViewIso k R S P Q)).trans
      (returnTypedNatIso k R S P Q u hu)

variable
  (w : letI := TensorProduct.Balanced.leftModule k R S Q P
    letI := TensorProduct.Balanced.rightModule k R S Q P
    TensorProduct.Balanced k R Q P ≃ₗ[Sᵐᵒᵖ] S)
  (hw : letI := TensorProduct.Balanced.leftModule k R S Q P
    letI := TensorProduct.Balanced.rightModule k R S Q P
    ∀ (s : S) (b : TensorProduct.Balanced k R Q P), w (s • b) = s * w b)

include u hu w hw in
/-- The actual bimodule-category equivalence from the two invertible contractions. -/
def equivalence :
    ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ) ≌ ModuleCat.{max p q v} (S ⊗[k] Sᵐᵒᵖ) :=
  CategoryTheory.Equivalence.mk (tensorFunctor k R S P Q) (tensorFunctor k S R Q P)
    (returnNatIso k R S P Q u hu).symm (returnNatIso k S R Q P w hw)

@[simp]
theorem equivalence_functor : (equivalence k R S P Q u hu w hw).functor =
    tensorFunctor k R S P Q := rfl

@[simp]
theorem equivalence_inverse : (equivalence k R S P Q u hu w hw).inverse =
    tensorFunctor k S R Q P := rfl

/-- Native adjointification keeps the actual symmetric return counit. -/
theorem equivalence_counitIso : (equivalence k R S P Q u hu w hw).counitIso =
    returnNatIso k S R Q P w hw := rfl

/-- The actual chosen unit is the native adjointified unit, not an assumed normalized
contraction. -/
theorem equivalence_unitIso : (equivalence k R S P Q u hu w hw).unitIso =
    Equivalence.adjointifyη (returnNatIso k R S P Q u hu).symm
      (returnNatIso k S R Q P w hw) := rfl

/-- The retained counit has the original two-contraction coefficient value. -/
-- keeps the actual equivalence counit formula for rw; functor-object and quotient getters
-- simplify its input
@[simp, nolint simpNF]
theorem equivalence_counitIso_mk (Y : ModuleCat.{max p q v} (S ⊗[k] Sᵐᵒᵖ))
    (q₀ : Q) (p₀ : P) (y : Y) (q₁ : Q) (p₁ : P) :
    letI := ModuleCat.Bimodule.Over.groundModule k S Y
    letI := ModuleCat.Bimodule.Over.leftModule k S Y
    letI := ModuleCat.Bimodule.Over.rightModule k S Y
    letI := ModuleCat.Bimodule.Over.leftTower k S Y
    letI := ModuleCat.Bimodule.Over.rightTower k S Y
    letI := ModuleCat.Bimodule.Over.commute k S Y
    letI := TensorProduct.Balanced.rightModule k S S P Y
    ((equivalence k R S P Q u hu w hw).counitIso.hom.app Y).hom
        (returnOuterMk k S R Q P Y q₀
          (TensorProduct.Balanced.mk k S (TensorProduct.Balanced k S P Y) Q
              (TensorProduct.Balanced.mk k S P Y p₀ y) q₁) p₁) =
      (w (TensorProduct.Balanced.mk k R Q P q₀ p₀) ⊗ₜ[k] op
          (w (TensorProduct.Balanced.mk k R Q P q₁ p₁))) • y :=
  returnIso_mk k S R Q P w hw Y q₀ p₀ y q₁ p₁

end ModuleCat.Bimodule.Over.Morita
