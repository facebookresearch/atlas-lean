/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.FGProjectiveCat.ConeRing.InfinityFunctor
public import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts
public import MathlibExt.CategoryTheory.Waldhausen.Exact

/-!
# The original projective cone absorption isomorphism

The actual pointwise identity-plus-infinity functor is isomorphic to the
original infinity scalar extension. Its forward and inverse maps are the
original projection and inclusion coefficient maps, composed with the
original tensor unitor. Both inverse equations retain those exact maps.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open ModuleCat.RingHomScalarExtension

universe uR

private theorem originalInlDesc {D : Type*} [Category* D] [Preadditive D]
    [HasBinaryBiproducts D] {A B Z : D} (f : A ⟶ Z) (g : B ⟶ Z) :
    biprod.inl ≫ (biprod.fst ≫ f + biprod.snd ≫ g) = f := by
  rw [← biprod.desc_eq]
  exact biprod.inl_desc f g

private theorem originalInrDesc {D : Type*} [Category* D] [Preadditive D]
    [HasBinaryBiproducts D] {A B Z : D} (f : A ⟶ Z) (g : B ⟶ Z) :
    biprod.inr ≫ (biprod.fst ≫ f + biprod.snd ≫ g) = g := by
  rw [← biprod.desc_eq]
  exact biprod.inr_desc f g

private theorem originalLiftFst {D : Type*} [Category* D] [Preadditive D]
    [HasBinaryBiproducts D] {A B Z : D} (f : Z ⟶ A) (g : Z ⟶ B) :
    (f ≫ biprod.inl + g ≫ biprod.inr) ≫ biprod.fst = f := by
  rw [← biprod.lift_eq]
  exact biprod.lift_fst f g

private theorem originalLiftSnd {D : Type*} [Category* D] [Preadditive D]
    [HasBinaryBiproducts D] {A B Z : D} (f : Z ⟶ A) (g : Z ⟶ B) :
    (f ≫ biprod.inl + g ≫ biprod.inr) ≫ biprod.snd = g := by
  rw [← biprod.lift_eq]
  exact biprod.lift_snd f g

private theorem originalMatrixHomInv {D : Type*} [Category* D] [Preadditive D]
    [HasBinaryBiproducts D] {A B : D} (l : A ⟶ B) (r : B ⟶ A) (t u : B ⟶ B)
    (h00 : l ≫ r = 𝟙 A) (h01 : l ≫ u = 0) (h10 : t ≫ r = 0) (h11 : t ≫ u = 𝟙 B) :
    (biprod.fst ≫ l + biprod.snd ≫ t) ≫ (r ≫ biprod.inl + u ≫ biprod.inr) = 𝟙 (A ⊞ B) := by
  rw [← biprod.desc_eq, ← biprod.lift_eq]
  apply biprod.hom_ext'
  · apply biprod.hom_ext
    · simpa only [Category.assoc, biprod.inl_desc_assoc, biprod.lift_fst,
        Category.id_comp, Category.comp_id, biprod.inl_fst] using h00
    · simpa only [Category.assoc, biprod.inl_desc_assoc, biprod.lift_snd,
        Category.id_comp, Category.comp_id, biprod.inl_snd] using h01
  · apply biprod.hom_ext
    · simpa only [Category.assoc, biprod.inr_desc_assoc, biprod.lift_fst,
        Category.id_comp, Category.comp_id, biprod.inr_fst] using h10
    · simpa only [Category.assoc, biprod.inr_desc_assoc, biprod.lift_snd,
        Category.id_comp, Category.comp_id, biprod.inr_snd] using h11

private theorem originalMatrixInvHom {D : Type*} [Category* D] [Preadditive D]
    [HasBinaryBiproducts D] {A B : D} (l : A ⟶ B) (r : B ⟶ A) (t u : B ⟶ B)
    (h : r ≫ l + u ≫ t = 𝟙 B) :
    (r ≫ biprod.inl + u ≫ biprod.inr) ≫ (biprod.fst ≫ l + biprod.snd ≫ t) = 𝟙 B := by
  rw [← biprod.desc_eq, ← biprod.lift_eq, biprod.lift_desc]
  exact h


namespace FGProjectiveCat.ConeRing

variable (R : Type uR) [Ring R]

local notation "C" => _root_.ConeRing R
local notation "P" => category R
local notation "V" => infinityFunctor R

/-- The actual original pointwise binary bicone of identity and infinity. -/
abbrev sumBicone : BinaryBicone (𝟭 P) V := pointwiseBinaryBicone (𝟭 P) V

/-- The actual original identity-plus-infinity functor. -/
abbrev sumFunctor : P ⥤ P := (sumBicone R).pt

instance sumFunctorAdditive : (sumFunctor R).Additive where
  map_add {X Y f g} := by
    change biprod.map (f + g) ((V).map (f + g)) =
      biprod.map f ((V).map f) + biprod.map g ((V).map g)
    apply biprod.hom_ext <;>
      simp only [biprod.map_fst, biprod.map_snd, Functor.map_add,
        Preadditive.add_comp, Preadditive.comp_add]

instance sumFunctorExact : (sumFunctor R).IsExact := ExactCategory.isExact_splitSource _

/-- The original categorical forward program from the pointwise biproduct to infinity. -/
def absorptionHom : sumFunctor R ⟶ V :=
  (sumBicone R).fst ≫ insert R + (sumBicone R).snd ≫ tailProjectionMap R

/-- The original categorical return program to both pointwise biproduct summands. -/
def absorptionInv : V ⟶ sumFunctor R :=
  extract R ≫ (sumBicone R).inl + tailInclusionMap R ≫ (sumBicone R).inr

private theorem absorptionHomInv_app (X : P) :
    (absorptionHom R).app X ≫ (absorptionInv R).app X = 𝟙 ((sumFunctor R).obj X) := by
  have h00 := congrArg (fun η : (𝟭 P) ⟶ (𝟭 P) => η.app X) (insert_extract R)
  have h01 := congrArg (fun η : (𝟭 P) ⟶ V => η.app X) (insert_tailInclusionMap R)
  have h10 := congrArg (fun η : V ⟶ (𝟭 P) => η.app X) (tailProjectionMap_extract R)
  have h11 := congrArg (fun η : V ⟶ V => η.app X) (tailProjectionMap_tailInclusionMap R)
  change (biprod.fst ≫ (insert R).app X + biprod.snd ≫ (tailProjectionMap R).app X) ≫
    ((extract R).app X ≫ biprod.inl + (tailInclusionMap R).app X ≫ biprod.inr) =
      𝟙 (X ⊞ (V).obj X)
  exact originalMatrixHomInv ((insert R).app X) ((extract R).app X)
    ((tailProjectionMap R).app X) ((tailInclusionMap R).app X) h00 h01 h10 h11

private theorem absorptionInvHom_app (X : P) :
    (absorptionInv R).app X ≫ (absorptionHom R).app X = 𝟙 ((V).obj X) := by
  have h := congrArg (fun η : V ⟶ V => η.app X) (extract_insert_tail_maps R)
  change ((extract R).app X ≫ biprod.inl + (tailInclusionMap R).app X ≫ biprod.inr) ≫
    (biprod.fst ≫ (insert R).app X + biprod.snd ≫ (tailProjectionMap R).app X) = _
  exact originalMatrixInvHom ((insert R).app X) ((extract R).app X)
    ((tailProjectionMap R).app X) ((tailInclusionMap R).app X) h

/-- The original identity-plus-infinity natural isomorphism with both literal return programs. -/
def absorption : sumFunctor R ≅ V where
  hom := absorptionHom R
  inv := absorptionInv R
  hom_inv_id := NatTrans.ext (funext (absorptionHomInv_app R))
  inv_hom_id := NatTrans.ext (funext (absorptionInvHom_app R))

/-- The whole forward is the original projection/unitor coefficient program. -/
theorem absorption_hom : (absorption R).hom = absorptionHom R := by rfl

/-- The whole inverse retains both original inclusion coefficient maps. -/
theorem absorption_inv : (absorption R).inv = absorptionInv R := by rfl

/-- The original forward component keeps both actual biproduct projection maps. -/
theorem absorption_hom_app (X : P) :
    (absorption R).hom.app X =
      biprod.fst ≫ (insert R).app X + biprod.snd ≫ (tailProjectionMap R).app X := by rfl

/-- The original inverse component keeps both actual biproduct inclusion maps. -/
theorem absorption_inv_app (X : P) :
    (absorption R).inv.app X =
      (extract R).app X ≫ biprod.inl + (tailInclusionMap R).app X ≫ biprod.inr := by rfl

/-- The actual original forward followed by inverse is the pointwise biproduct identity. -/
theorem absorption_hom_inv : (absorption R).hom ≫ (absorption R).inv = 𝟙 (sumFunctor R) :=
  (absorption R).hom_inv_id

/-- The actual original inverse followed by forward is the infinity identity. -/
theorem absorption_inv_hom : (absorption R).inv ≫ (absorption R).hom = 𝟙 V :=
  (absorption R).inv_hom_id

/-- The actual forward on the original first summand is the original insertion. -/
theorem absorption_inl : (sumBicone R).inl ≫ (absorption R).hom = insert R := by
  apply NatTrans.ext
  funext X
  change biprod.inl ≫ (biprod.fst ≫ (insert R).app X +
    biprod.snd ≫ (tailProjectionMap R).app X) = (insert R).app X
  exact originalInlDesc ((insert R).app X) ((tailProjectionMap R).app X)

/-- The actual forward on the original second summand is the original tail projection. -/
theorem absorption_inr : (sumBicone R).inr ≫ (absorption R).hom = tailProjectionMap R := by
  apply NatTrans.ext
  funext X
  change biprod.inr ≫ (biprod.fst ≫ (insert R).app X +
    biprod.snd ≫ (tailProjectionMap R).app X) = (tailProjectionMap R).app X
  exact originalInrDesc ((insert R).app X) ((tailProjectionMap R).app X)

/-- The original first inverse component is exactly the original extraction map. -/
theorem absorption_fst : (absorption R).inv ≫ (sumBicone R).fst = extract R := by
  apply NatTrans.ext
  funext X
  change ((extract R).app X ≫ biprod.inl + (tailInclusionMap R).app X ≫ biprod.inr) ≫
    biprod.fst = (extract R).app X
  exact originalLiftFst ((extract R).app X) ((tailInclusionMap R).app X)

/-- The original second inverse component is exactly the original tail inclusion map. -/
theorem absorption_snd : (absorption R).inv ≫ (sumBicone R).snd = tailInclusionMap R := by
  apply NatTrans.ext
  funext X
  change ((extract R).app X ≫ biprod.inl + (tailInclusionMap R).app X ≫ biprod.inr) ≫
    biprod.snd = (tailInclusionMap R).app X
  exact originalLiftSnd ((extract R).app X) ((tailInclusionMap R).app X)

/-- The original first input has the original first-projection pure coefficient. -/
theorem absorption_inl_pure (X : P) (x : X) :
    ringScalarExtensionCoordinates (_root_.ConeRing.infinityHom R) X
      (((absorption R).hom.app X).hom.hom (((sumBicone R).inl.app X).hom.hom x)) =
        pure (_root_.ConeRing.infinityHom R) X (_root_.ConeRing.firstProjection R) x := by
  have h := congrArg (fun η : (𝟭 P) ⟶ V => η.app X) (absorption_inl R)
  have hx := ConcreteCategory.congr_hom h x
  exact (congrArg (ringScalarExtensionCoordinates (_root_.ConeRing.infinityHom R) X) hx).trans
    (insert_pure R X x)

/-- The original second input retains its tail-projection coefficient on every pure class. -/
theorem absorption_inr_pure (X : P) (s : C) (x : X) :
    let t := (ringScalarExtensionCoordinates (_root_.ConeRing.infinityHom R) X).symm
      (pure (_root_.ConeRing.infinityHom R) X s x)
    ringScalarExtensionCoordinates (_root_.ConeRing.infinityHom R) X
      (((absorption R).hom.app X).hom.hom (((sumBicone R).inr.app X).hom.hom t)) =
        pure (_root_.ConeRing.infinityHom R) X (s * _root_.ConeRing.tailProjection R) x := by
  dsimp only
  have h := congrArg (fun η : V ⟶ V => η.app X) (absorption_inr R)
  have hx := ConcreteCategory.congr_hom h
    ((ringScalarExtensionCoordinates (_root_.ConeRing.infinityHom R) X).symm
      (pure (_root_.ConeRing.infinityHom R) X s x))
  exact (congrArg (ringScalarExtensionCoordinates (_root_.ConeRing.infinityHom R) X) hx).trans
    (tailProjectionMap_pure R X s x)

/-- The original first inverse reader returns the first-inclusion module action. -/
theorem absorption_fst_pure (X : P) (s : C) (x : X) :
    let t := (ringScalarExtensionCoordinates (_root_.ConeRing.infinityHom R) X).symm
      (pure (_root_.ConeRing.infinityHom R) X s x)
    (((sumBicone R).fst.app X).hom.hom (((absorption R).inv.app X).hom.hom t)) =
      (s * _root_.ConeRing.firstInclusion R) • x := by
  dsimp only
  have h := congrArg (fun η : V ⟶ (𝟭 P) => η.app X) (absorption_fst R)
  have hx := ConcreteCategory.congr_hom h
    ((ringScalarExtensionCoordinates (_root_.ConeRing.infinityHom R) X).symm
      (pure (_root_.ConeRing.infinityHom R) X s x))
  exact hx.trans (extract_pure R X s x)

/-- The original second inverse reader returns the tail-inclusion pure coefficient. -/
theorem absorption_snd_pure (X : P) (s : C) (x : X) :
    let t := (ringScalarExtensionCoordinates (_root_.ConeRing.infinityHom R) X).symm
      (pure (_root_.ConeRing.infinityHom R) X s x)
    ringScalarExtensionCoordinates (_root_.ConeRing.infinityHom R) X
      (((sumBicone R).snd.app X).hom.hom (((absorption R).inv.app X).hom.hom t)) =
        pure (_root_.ConeRing.infinityHom R) X (s * _root_.ConeRing.tailInclusion R) x := by
  dsimp only
  have h := congrArg (fun η : V ⟶ V => η.app X) (absorption_snd R)
  have hx := ConcreteCategory.congr_hom h
    ((ringScalarExtensionCoordinates (_root_.ConeRing.infinityHom R) X).symm
      (pure (_root_.ConeRing.infinityHom R) X s x))
  exact (congrArg (ringScalarExtensionCoordinates (_root_.ConeRing.infinityHom R) X) hx).trans
    (tailInclusionMap_pure R X s x)

/-- The original first inclusion of the pointwise functor cofiber sequence. -/
abbrev sumInclusion : 𝟭 P ⟶ sumFunctor R := (sumBicone R).inl

/-- The original quotient projection of the pointwise functor cofiber sequence. -/
abbrev sumProjection : sumFunctor R ⟶ V := (sumBicone R).snd

/-- The canonical exact-category structure earns the original pointwise cofiber rows. -/
theorem sum_cofiber_sequence (X : P) :
    letI : WaldhausenCategoryWithoutGluing P := ExactCategory.waldhausenCategory P
    IsCofiberSequence ((sumInclusion R).app X) ((sumProjection R).app X) := by
  let : WaldhausenCategoryWithoutGluing P := ExactCategory.waldhausenCategory P
  exact ExactCategory.isCofibrationSequence_of_isAdmissibleExact
    (ExactCategory.isAdmissibleExact_split X ((V).obj X))

end FGProjectiveCat.ConeRing

end
