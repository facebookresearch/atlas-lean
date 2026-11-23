/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteBGLTelescopeRowScalarRoot
public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteBGLTelescopeRowScalarNatIso

/-!
# Original zero-component roots of telescope scalar naturality

The proper full zero inclusion transports the original Pair root isomorphisms
to the actual zero categories. Its earned component computation and the original
Pair root square give the same square in the zero category by faithfulness.
The chosen endpoint remains the original diagonal-zero object in the common
projective carrier universe. No trace or equivalence witness is an input.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe uR uS uC vC

namespace AlgebraicKTheory.StableGL

private theorem inverseRootSquare
    {C : Type uC} [Category.{vC} C] {A B X Y Z : C}
    (p : A ≅ X) (q : B ≅ Y) (e : X ≅ Y) (r : X ≅ Z) (s : Y ≅ Z)
    (h : e ≪≫ s = r) : (p ≪≫ e ≪≫ q.symm) ≪≫ (q ≪≫ s) = p ≪≫ r := by
  apply Iso.ext
  have hh := congrArg Iso.hom h
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  exact congrArg (fun k : X ⟶ Z => p.hom ≫ k) hh

private theorem fullInclusionIsoSquare
    {C : Type uC} [Category.{vC} C] (P : ObjectProperty C)
    {A B Z : P.FullSubcategory} (e : A ≅ B) (s : B ≅ Z) (r : A ≅ Z)
    (h : P.ι.mapIso e ≪≫ P.ι.mapIso s = P.ι.mapIso r) : e ≪≫ s = r := by
  apply Iso.ext
  apply P.ι.map_injective
  have hh := congrArg Iso.hom h
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp] using hh

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

/-- The source root lifts the original Pair root through the proper zero inclusion. -/
public def finiteBGLTelescopeScalarSourceRootZeroIso (f : R →+* S) :
    (finiteBGLTelescopeToRowZeroComponent R ⋙
      SInverseS.zeroComponentFunctor ((FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
        FGProjectiveCat.scalarExtension.{uR, uS, uR} f)).obj (finiteBGLTelescopeBaseObject R) ≅
      SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.{max uS uR} S) :=
  (SInverseS.zeroComponentProperty (C := FGProjectiveCat.{max uS uR} S)).isoMk
    ((finiteBGLTelescopeScalarSourceZeroInclusionIso f).app (finiteBGLTelescopeBaseObject R) ≪≫
      finiteBGLTelescopeScalarSourceRootIso f)

/-- The target root lifts the same original mapped stage-zero Pair root. -/
public def finiteBGLTelescopeScalarTargetRootZeroIso (f : R →+* S) :
    ((finiteBGLTelescopeScalarFunctor f ⋙ finiteBGLTelescopeToRowZeroComponent S) ⋙
      SInverseS.zeroComponentFunctor ((FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
        (FGProjectiveCat.universeEquivalence.{uS, uR} S).inverse)).obj
        (finiteBGLTelescopeBaseObject R) ≅
      SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.{max uS uR} S) :=
  (SInverseS.zeroComponentProperty (C := FGProjectiveCat.{max uS uR} S)).isoMk
    ((finiteBGLTelescopeScalarTargetZeroInclusionIso f).app (finiteBGLTelescopeBaseObject R) ≪≫
      finiteBGLTelescopeScalarTargetRootIso f)

/-- Source-root inclusion retains the exact original Pair route and object transports. -/
public theorem finiteBGLTelescopeScalarSourceRootZeroIso_inclusion (f : R →+* S) :
    (SInverseS.zeroComponentProperty (C := FGProjectiveCat.{max uS uR} S)).ι.mapIso
        (finiteBGLTelescopeScalarSourceRootZeroIso f) =
      (finiteBGLTelescopeScalarSourceZeroInclusionIso f).app (finiteBGLTelescopeBaseObject R) ≪≫
        finiteBGLTelescopeScalarSourceRootIso f := by
  apply Iso.ext
  rfl

/-- Target-root inclusion retains the exact original Pair route and object transports. -/
public theorem finiteBGLTelescopeScalarTargetRootZeroIso_inclusion (f : R →+* S) :
    (SInverseS.zeroComponentProperty (C := FGProjectiveCat.{max uS uR} S)).ι.mapIso
        (finiteBGLTelescopeScalarTargetRootZeroIso f) =
      (finiteBGLTelescopeScalarTargetZeroInclusionIso f).app (finiteBGLTelescopeBaseObject R) ≪≫
        finiteBGLTelescopeScalarTargetRootIso f := by
  apply Iso.ext
  rfl

/-- The actual scalar zero-component Iso commutes with both original chosen-zero root routes. -/
public theorem finiteBGLTelescopeRowScalarZeroIso_original_root (f : R →+* S) :
    (finiteBGLTelescopeRowScalarZeroIso f).app (finiteBGLTelescopeBaseObject R) ≪≫
        finiteBGLTelescopeScalarTargetRootZeroIso f = finiteBGLTelescopeScalarSourceRootZeroIso f :=
            by
  let X := finiteBGLTelescopeBaseObject R
  let P := SInverseS.zeroComponentProperty (C := FGProjectiveCat.{max uS uR} S)
  let e := (finiteBGLTelescopeRowScalarZeroIso f).app X
  let r := finiteBGLTelescopeScalarSourceRootZeroIso f
  let s := finiteBGLTelescopeScalarTargetRootZeroIso f
  let p := (finiteBGLTelescopeScalarSourceZeroInclusionIso f).app X
  let q := (finiteBGLTelescopeScalarTargetZeroInclusionIso f).app X
  let c := (finiteBGLTelescopeRowScalarPairIso f).app X
  let rp := finiteBGLTelescopeScalarSourceRootIso f
  let sp := finiteBGLTelescopeScalarTargetRootIso f
  have hComponents : P.ι.mapIso e = p ≪≫ c ≪≫ q.symm :=
    finiteBGLTelescopeRowScalarZeroIso_inclusion_app f X
  have hSource : P.ι.mapIso r = p ≪≫ rp := finiteBGLTelescopeScalarSourceRootZeroIso_inclusion f
  have hTarget : P.ι.mapIso s = q ≪≫ sp := finiteBGLTelescopeScalarTargetRootZeroIso_inclusion f
  have hPair : c ≪≫ sp = rp := finiteBGLTelescopeRowScalarPairIso_original_root f
  have hLeft : P.ι.mapIso e ≪≫ P.ι.mapIso s = (p ≪≫ c ≪≫ q.symm) ≪≫ (q ≪≫ sp) :=
    congrArg₂ (fun a b => a ≪≫ b) hComponents hTarget
  have hMiddle : (p ≪≫ c ≪≫ q.symm) ≪≫ (q ≪≫ sp) = p ≪≫ rp :=
    inverseRootSquare p q c rp sp hPair
  exact fullInclusionIsoSquare P e s r (hLeft.trans (hMiddle.trans hSource.symm))

end AlgebraicKTheory.StableGL
