/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.NormNum
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.SquareCoherence

/-!
# Derived comparison squares for restriction from ZMod 6 to the integers

Restriction along the integer quotient is exact. The directional derived-square API
therefore applies without requiring this restriction functor to preserve projectives.
The source and target changes here are this actual restriction, and the underlying
coefficient square multiplies by two. Its degree-zero map has a nonzero class whose
image is killed by three.

Canonical augmentations give coordinates for that class. Coefficient naturality in every
nonnegative degree identifies tripling after the doubled square with the sextuple square.
All coordinates and torsion identities follow from canonical augmentations and the square laws.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MathlibExtTest.CategoryTheory.Abelian.LeftDerived.ExactSquareRestrictionTests

private abbrev IntegerModules := ModuleCat.{0} ℤ
private abbrev ResidueModules := ModuleCat.{0} (ZMod 6)

private abbrev restriction : ResidueModules ⥤ IntegerModules :=
  ModuleCat.restrictScalars (Int.castRingHom (ZMod 6))

private abbrev integerIdentity : IntegerModules ⥤ IntegerModules := 𝟭 _
private abbrev residueIdentity : ResidueModules ⥤ ResidueModules := 𝟭 _

private instance : restriction.PreservesHomology :=
  Functor.preservesHomologyOfExact restriction

private def coefficient (b : ℤ) : residueIdentity ⟶ residueIdentity where
  app X := b • 𝟙 X
  naturality X Y f := by
    change f ≫ (b • 𝟙 Y) = (b • 𝟙 X) ≫ f
    simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp,
      Category.comp_id, Category.id_comp]

private def scalarSquare (a : ℤ) :
    restriction ⋙ integerIdentity ⟶ residueIdentity ⋙ restriction where
  app X := a • 𝟙 (restriction.obj X)
  naturality X Y f := by
    change restriction.map f ≫ (a • 𝟙 (restriction.obj Y)) =
      (a • 𝟙 (restriction.obj X)) ≫ restriction.map f
    simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp,
      Category.comp_id, Category.id_comp]

private theorem scalarSquare_coefficient (a b : ℤ) :
    scalarSquare a ≫ Functor.whiskerRight (coefficient b) restriction = scalarSquare (b * a) := by
  ext X
  change (a • 𝟙 (restriction.obj X)) ≫ restriction.map (b • 𝟙 X) =
    (b * a) • 𝟙 (restriction.obj X)
  simp only [Functor.map_zsmul, Functor.map_id, Preadditive.comp_zsmul,
    Category.comp_id, smul_smul]

private abbrev derivedSquare (a : ℤ) (n : ℕ) :
    restriction ⋙ integerIdentity.leftDerived n ⟶ residueIdentity.leftDerived n ⋙ restriction :=
  Functor.leftDerivedSquareHom restriction restriction integerIdentity residueIdentity
    (scalarSquare a) n

private def sourceAugmentation (X : ResidueModules) :
    (integerIdentity.leftDerived 0).obj (restriction.obj X) ≅ restriction.obj X :=
  asIso (integerIdentity.fromLeftDerivedZero.app (restriction.obj X))

private def targetAugmentation (X : ResidueModules) :
    restriction.obj ((residueIdentity.leftDerived 0).obj X) ≅ restriction.obj X :=
  restriction.mapIso (asIso (residueIdentity.fromLeftDerivedZero.app X))

private def coordinateSquare (a : ℤ) (X : ResidueModules) :
    restriction.obj X ⟶ restriction.obj X :=
  (sourceAugmentation X).inv ≫ (derivedSquare a 0).app X ≫ (targetAugmentation X).hom

private theorem coordinateSquare_eq (a : ℤ) (X : ResidueModules) :
    coordinateSquare a X = a • 𝟙 (restriction.obj X) := by
  have h := congrArg
    (fun η : restriction ⋙ integerIdentity.leftDerived 0 ⟶ residueIdentity ⋙ restriction =>
      η.app X)
    (Functor.leftDerivedSquareHom_zero_augmentation restriction restriction
      integerIdentity residueIdentity (scalarSquare a))
  change (derivedSquare a 0).app X ≫ (targetAugmentation X).hom =
    (sourceAugmentation X).hom ≫ (scalarSquare a).app X at h
  simpa only [coordinateSquare, Category.assoc, Iso.inv_hom_id_assoc] using
    congrArg (fun f => (sourceAugmentation X).inv ≫ f) h

private abbrev residueObject : ResidueModules := ModuleCat.of (ZMod 6) (ZMod 6)

private def unitClass :
    (integerIdentity.leftDerived 0).obj (restriction.obj residueObject) :=
  (sourceAugmentation residueObject).inv.hom (1 : ZMod 6)

private def transportedValue (a : ℤ) : ZMod 6 :=
  (coordinateSquare a residueObject).hom (1 : ZMod 6)

private theorem transportedTwo_value : transportedValue 2 = (2 : ZMod 6) := by
  dsimp only [transportedValue]
  rw [coordinateSquare_eq]
  norm_num

private theorem transportedValue_description (a : ℤ) :
    (targetAugmentation residueObject).hom.hom
      (((derivedSquare a 0).app residueObject).hom unitClass) = transportedValue a :=
  rfl

private theorem transportedTwo_ne_zero : transportedValue 2 ≠ 0 := by
  rw [transportedTwo_value]
  norm_num

example : transportedValue 2 = (2 : ZMod 6) := transportedTwo_value

example : (3 : ℤ) • transportedValue 2 = 0 := by
  rw [transportedTwo_value]
  norm_num

example : transportedValue 6 = 0 := by
  dsimp only [transportedValue]
  rw [coordinateSquare_eq]
  norm_num

private theorem derivedImage_ne_zero :
    ((derivedSquare 2 0).app residueObject).hom unitClass ≠ 0 := by
  intro hZero
  have h := transportedValue_description 2
  rw [hZero, map_zero] at h
  exact transportedTwo_ne_zero h.symm

example : unitClass ≠ 0 := by
  intro hZero
  apply derivedImage_ne_zero
  rw [hZero, map_zero]

example : coordinateSquare 2 residueObject ≠ 𝟙 (restriction.obj residueObject) := by
  intro hId
  have h : transportedValue 2 = (1 : ZMod 6) := by
    change (coordinateSquare 2 residueObject).hom (1 : ZMod 6) = 1
    rw [hId]
    simp only [ModuleCat.hom_id, LinearMap.id_apply]
  rw [transportedTwo_value] at h
  norm_num at h

example (n : ℕ) :
    derivedSquare 2 n ≫ Functor.whiskerRight (NatTrans.leftDerived (coefficient 3) n) restriction =
      derivedSquare 6 n := by
  have h := Functor.leftDerivedSquareHom_naturality_target_functor restriction restriction
    integerIdentity residueIdentity (scalarSquare 2) (coefficient 3) n
  rw [scalarSquare_coefficient] at h
  simpa only [derivedSquare, show (3 : ℤ) * 2 = 6 by norm_num] using h

end MathlibExtTest.CategoryTheory.Abelian.LeftDerived.ExactSquareRestrictionTests
