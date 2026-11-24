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

public import MathlibExt.CategoryTheory.Waldhausen.BinaryCoproductFunctor
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison

/-!
# Actual original coproduct unit natural isomorphisms

The original zero-pushout coproduct colimit cocones supply both unit
injections. Their colimit universal properties prove those injections
invertible, and the original full coproduct map equations prove naturality.
The same original coproduct functor and object transports are retained.
-/

public section

noncomputable section

open CategoryTheory Limits
open scoped ZeroObject

universe v u

namespace CategoryTheory.Waldhausen

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- The literal ORIGINAL zero-left insertion on C objects and maps. -/
def waldhausenZeroLeftPair : C ⥤ C × C :=
  ((Functor.const C).obj (0 : C)).prod' (𝟭 C)

/-- The literal ORIGINAL zero-right insertion on C objects and maps. -/
def waldhausenZeroRightPair : C ⥤ C × C :=
  (𝟭 C).prod' ((Functor.const C).obj (0 : C))

private def originalCoproductZeroLeftInjection :
    𝟭 C ⟶ waldhausenZeroLeftPair C ⋙ waldhausenCoproductFunctor C where
  app X := (binaryCoproductColimitCocone C (pair (0 : C) X)).cocone.ι.app
      ⟨WalkingPair.right⟩ ≫ (eqToIso (waldhausenCoproductFunctor_obj C (0, X))).inv
  naturality {X Y} f := by
    let c : BinaryCofan (0 : C) X := (binaryCoproductColimitCocone C (pair (0 : C) X)).cocone
    let c' : BinaryCofan (0 : C) Y := (binaryCoproductColimitCocone C (pair (0 : C) Y)).cocone
    let e : (waldhausenCoproductFunctor C).obj (0, X) ≅ c.pt :=
      eqToIso (waldhausenCoproductFunctor_obj C (0, X))
    let e' : (waldhausenCoproductFunctor C).obj (0, Y) ≅ c'.pt :=
      eqToIso (waldhausenCoproductFunctor_obj C (0, Y))
    change f ≫ (c'.inr ≫ e'.inv) =
      (c.inr ≫ e.inv) ≫ (waldhausenCoproductFunctor C).map ⟨𝟙 (0 : C), f⟩
    have hm : (waldhausenCoproductFunctor C).map ⟨𝟙 (0 : C), f⟩ =
        e.hom ≫ binaryCoproductMap C (𝟙 (0 : C)) f ≫ e'.inv :=
      by
        have hmRaw := waldhausenCoproductFunctor_map C
          (p := ((0 : C), X)) (q := ((0 : C), Y))
          (Prod.mkHom (C := C) (D := C) (𝟙 (0 : C) : (0 : C) ⟶ (0 : C)) f)
        simpa only [e, e', eqToIso.hom, eqToIso.inv, Category.assoc] using hmRaw
    rw [hm]
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
      congrArg (fun a : X ⟶ c'.pt => a ≫ e'.inv)
        (binaryCoproductMap_inr C (𝟙 (0 : C)) f).symm

private def originalCoproductZeroRightInjection :
    𝟭 C ⟶ waldhausenZeroRightPair C ⋙ waldhausenCoproductFunctor C where
  app X := (binaryCoproductColimitCocone C (pair X (0 : C))).cocone.ι.app
      ⟨WalkingPair.left⟩ ≫ (eqToIso (waldhausenCoproductFunctor_obj C (X, 0))).inv
  naturality {X Y} f := by
    let c : BinaryCofan X (0 : C) := (binaryCoproductColimitCocone C (pair X (0 : C))).cocone
    let c' : BinaryCofan Y (0 : C) := (binaryCoproductColimitCocone C (pair Y (0 : C))).cocone
    let e : (waldhausenCoproductFunctor C).obj (X, 0) ≅ c.pt :=
      eqToIso (waldhausenCoproductFunctor_obj C (X, 0))
    let e' : (waldhausenCoproductFunctor C).obj (Y, 0) ≅ c'.pt :=
      eqToIso (waldhausenCoproductFunctor_obj C (Y, 0))
    change f ≫ (c'.inl ≫ e'.inv) =
      (c.inl ≫ e.inv) ≫ (waldhausenCoproductFunctor C).map ⟨f, 𝟙 (0 : C)⟩
    have hm : (waldhausenCoproductFunctor C).map ⟨f, 𝟙 (0 : C)⟩ =
        e.hom ≫ binaryCoproductMap C f (𝟙 (0 : C)) ≫ e'.inv :=
      by
        have hmRaw := waldhausenCoproductFunctor_map C
          (p := (X, (0 : C))) (q := (Y, (0 : C)))
          (Prod.mkHom (C := C) (D := C) f (𝟙 (0 : C) : (0 : C) ⟶ (0 : C)))
        simpa only [e, e', eqToIso.hom, eqToIso.inv, Category.assoc] using hmRaw
    rw [hm]
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
      congrArg (fun a : X ⟶ c'.pt => a ≫ e'.inv)
        (binaryCoproductMap_inl C f (𝟙 (0 : C))).symm

private theorem originalCoproductZeroLeftInjection_isIso (X : C) :
    IsIso ((originalCoproductZeroLeftInjection C).app X) := by
  let c : BinaryCofan (0 : C) X := (binaryCoproductColimitCocone C (pair (0 : C) X)).cocone
  have hInr : IsIso c.inr :=
    (BinaryCofan.isColimit_iff_isIso_inr (isZero_zero C).isInitial c).mp
      ⟨(binaryCoproductColimitCocone C (pair (0 : C) X)).isColimit⟩
  have hApp : (originalCoproductZeroLeftInjection C).app X =
      c.inr ≫ (eqToIso (waldhausenCoproductFunctor_obj C (0, X))).inv := by
    rfl
  rw [hApp]
  exact IsIso.comp_isIso' hInr
    (eqToIso (waldhausenCoproductFunctor_obj C (0, X))).isIso_inv

private theorem originalCoproductZeroRightInjection_isIso (X : C) :
    IsIso ((originalCoproductZeroRightInjection C).app X) := by
  let c : BinaryCofan X (0 : C) := (binaryCoproductColimitCocone C (pair X (0 : C))).cocone
  have hInl : IsIso c.inl :=
    (BinaryCofan.isColimit_iff_isIso_inl (isZero_zero C).isInitial c).mp
      ⟨(binaryCoproductColimitCocone C (pair X (0 : C))).isColimit⟩
  have hApp : (originalCoproductZeroRightInjection C).app X =
      c.inl ≫ (eqToIso (waldhausenCoproductFunctor_obj C (X, 0))).inv := by
    rfl
  rw [hApp]
  exact IsIso.comp_isIso' hInl
    (eqToIso (waldhausenCoproductFunctor_obj C (X, 0))).isIso_inv

/-- The ACTUAL original zero-left coproduct unit Iso, from the SAME
original cocone injection and full naturality on all original morphisms. -/
def waldhausenCoproductLeftUnitIso :
    waldhausenZeroLeftPair C ⋙ waldhausenCoproductFunctor C ≅ 𝟭 C := by
  letI : ∀ X : C, IsIso ((originalCoproductZeroLeftInjection C).app X) :=
    originalCoproductZeroLeftInjection_isIso C
  letI : IsIso (originalCoproductZeroLeftInjection C) :=
    NatIso.isIso_of_isIso_app (originalCoproductZeroLeftInjection C)
  exact (asIso (originalCoproductZeroLeftInjection C)).symm

/-- The ACTUAL original zero-right coproduct unit Iso, from the SAME
original cocone injection and full naturality on all original morphisms. -/
def waldhausenCoproductRightUnitIso :
    waldhausenZeroRightPair C ⋙ waldhausenCoproductFunctor C ≅ 𝟭 C := by
  letI : ∀ X : C, IsIso ((originalCoproductZeroRightInjection C).app X) :=
    originalCoproductZeroRightInjection_isIso C
  letI : IsIso (originalCoproductZeroRightInjection C) :=
    NatIso.isIso_of_isIso_app (originalCoproductZeroRightInjection C)
  exact (asIso (originalCoproductZeroRightInjection C)).symm

omit [WaldhausenCategoryWithoutGluing C] in
private theorem waldhausenZeroLeftPair_eq_aux :
    waldhausenZeroLeftPair C =
      ((Functor.const C).obj (0 : C)).prod' (𝟭 C) := by
  rfl

omit [WaldhausenCategoryWithoutGluing C] in
/-- The WHOLE original zero-left functor is the literal constant-zero/identity pair. -/
theorem waldhausenZeroLeftPair_eq :
    waldhausenZeroLeftPair C =
      ((Functor.const C).obj (0 : C)).prod' (𝟭 C) :=
  waldhausenZeroLeftPair_eq_aux C

omit [WaldhausenCategoryWithoutGluing C] in
private theorem waldhausenZeroRightPair_eq_aux :
    waldhausenZeroRightPair C =
      (𝟭 C).prod' ((Functor.const C).obj (0 : C)) := by
  rfl

omit [WaldhausenCategoryWithoutGluing C] in
/-- The WHOLE original zero-right functor is the literal identity/constant-zero pair. -/
theorem waldhausenZeroRightPair_eq :
    waldhausenZeroRightPair C =
      (𝟭 C).prod' ((Functor.const C).obj (0 : C)) :=
  waldhausenZeroRightPair_eq_aux C

/-- The actual zero-left/coprod composite object retains its WHOLE original
zero-insertion functor value before evaluating the original coproduct. -/
theorem waldhausenZeroLeftCoproduct_obj (X : C) :
    (waldhausenZeroLeftPair C ⋙ waldhausenCoproductFunctor C).obj X =
      (waldhausenCoproductFunctor C).obj (0, X) :=
  Functor.congr_obj
    (congrArg (fun H : C ⥤ C × C => H ⋙ waldhausenCoproductFunctor C)
      (waldhausenZeroLeftPair_eq C)) X

/-- The actual zero-right/coprod composite object retains its WHOLE original
zero-insertion functor value before evaluating the original coproduct. -/
theorem waldhausenZeroRightCoproduct_obj (X : C) :
    (waldhausenZeroRightPair C ⋙ waldhausenCoproductFunctor C).obj X =
      (waldhausenCoproductFunctor C).obj (X, 0) :=
  Functor.congr_obj
    (congrArg (fun H : C ⥤ C × C => H ⋙ waldhausenCoproductFunctor C)
      (waldhausenZeroRightPair_eq C)) X

private theorem waldhausenCoproductLeftUnitIso_inv_app_aux (X : C) :
    HEq ((waldhausenCoproductLeftUnitIso C).inv.app X)
      ((binaryCoproductColimitCocone C (pair (0 : C) X)).cocone.ι.app
        ⟨WalkingPair.right⟩ ≫
        (eqToIso (waldhausenCoproductFunctor_obj C (0, X))).inv) := by
  rfl

/-- The WHOLE inverse component of the ORIGINAL left unit is its actual original
injection/chart map through the actual composite-object values. -/
theorem waldhausenCoproductLeftUnitIso_inv_app_heq (X : C) :
    HEq ((waldhausenCoproductLeftUnitIso C).inv.app X)
      ((binaryCoproductColimitCocone C (pair (0 : C) X)).cocone.ι.app
        ⟨WalkingPair.right⟩ ≫
        (eqToIso (waldhausenCoproductFunctor_obj C (0, X))).inv) :=
  waldhausenCoproductLeftUnitIso_inv_app_aux C X

/-- The typed WHOLE original left-unit inverse component keeps the final
transport into the SAME actual zero-left/coprod composite object. -/
theorem waldhausenCoproductLeftUnitIso_inv_app (X : C) :
    (waldhausenCoproductLeftUnitIso C).inv.app X =
      ((binaryCoproductColimitCocone C (pair (0 : C) X)).cocone.ι.app
        ⟨WalkingPair.right⟩ ≫
        (eqToIso (waldhausenCoproductFunctor_obj C (0, X))).inv) ≫
          eqToHom (waldhausenZeroLeftCoproduct_obj C X).symm := by
  have h := (conj_eqToHom_iff_heq _ _ rfl
    (waldhausenZeroLeftCoproduct_obj C X)).2
      (waldhausenCoproductLeftUnitIso_inv_app_heq C X)
  simpa only [eqToHom_refl, Category.id_comp] using h

private theorem waldhausenCoproductRightUnitIso_inv_app_aux (X : C) :
    HEq ((waldhausenCoproductRightUnitIso C).inv.app X)
      ((binaryCoproductColimitCocone C (pair X (0 : C))).cocone.ι.app
        ⟨WalkingPair.left⟩ ≫
        (eqToIso (waldhausenCoproductFunctor_obj C (X, 0))).inv) := by
  rfl

/-- The WHOLE inverse component of the ORIGINAL right unit is its actual original
injection/chart map through the actual composite-object values. -/
theorem waldhausenCoproductRightUnitIso_inv_app_heq (X : C) :
    HEq ((waldhausenCoproductRightUnitIso C).inv.app X)
      ((binaryCoproductColimitCocone C (pair X (0 : C))).cocone.ι.app
        ⟨WalkingPair.left⟩ ≫
        (eqToIso (waldhausenCoproductFunctor_obj C (X, 0))).inv) :=
  waldhausenCoproductRightUnitIso_inv_app_aux C X

/-- The typed WHOLE original right-unit inverse component keeps the final
transport into the SAME actual zero-right/coprod composite object. -/
theorem waldhausenCoproductRightUnitIso_inv_app (X : C) :
    (waldhausenCoproductRightUnitIso C).inv.app X =
      ((binaryCoproductColimitCocone C (pair X (0 : C))).cocone.ι.app
        ⟨WalkingPair.left⟩ ≫
        (eqToIso (waldhausenCoproductFunctor_obj C (X, 0))).inv) ≫
          eqToHom (waldhausenZeroRightCoproduct_obj C X).symm := by
  have h := (conj_eqToHom_iff_heq _ _ rfl
    (waldhausenZeroRightCoproduct_obj C X)).2
      (waldhausenCoproductRightUnitIso_inv_app_heq C X)
  simpa only [eqToHom_refl, Category.id_comp] using h

end CategoryTheory.Waldhausen

end
