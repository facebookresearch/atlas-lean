/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.PrincipalizationModels
public import MathlibExt.AlgebraicGeometry.BirationalDualityReferences
public import MathlibExt.AlgebraicGeometry.RationalResolution

/-!
# Embedded Du Bois degree-zero model and its fixed unit

The exceptional scheme is the actual reduced inverse image of an actual
closed ideal in a smooth ambient scheme. The degree-zero Du Bois model is
Rf_* O_E for the actual induced map E→X. Its unit is computed from the
ordinary structure-module unit, single-complex comparison and native
right-derived unit. There is no freely supplied Du Bois complex or map.

This supplies the embedded degree-zero model; a full filtered de Rham
hyperresolution and canonical-sheaf duality comparison are separate
interfaces, not consequences asserted here. Resolution/principalization
constructors are already present and are not requested again.

Source: Kovács--Schwede--Smith, arXiv0801.1541v3, §2.B and Theorem 1.1.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.EmbeddedDuBoisZero

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.PrincipalizationModels
open MathlibExt.AlgebraicGeometry.NormalCrossingsModels
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.FourierMukai
open MathlibExt.AlgebraicGeometry.BirationalDualityReferences

attribute [local instance] HasDerivedCategory.standard

variable {k : Type} [Field k]

/-- Actual reduced exceptional scheme of an embedded principalization. -/
abbrev exceptional {S : Over (Spec (.of k))} {I : S.left.IdealSheafData}
    (R : Principalization S I) :=
  (reducedPullbackBoundary R.map.left I).subscheme

/-- The factor map is normalized against the actual closed-subscheme inclusion.
That inclusion is a monomorphism, so this condition fixes the map uniquely. -/
structure ExceptionalMap {S : Over (Spec (.of k))} {I : S.left.IdealSheafData}
    (R : Principalization S I) where
  map : exceptional R ⟶ I.subscheme
  normalized : map ≫ I.subschemeι =
    (reducedPullbackBoundary R.map.left I).subschemeι ≫ R.map.left

variable [HasDerivedPushforwards.{0}]

/-- The literal embedded degree-zero Du Bois object Rf_* O_E. -/
def duBoisZero {S : Over (Spec (.of k))} {I : S.left.IdealSheafData}
    {R : Principalization S I} (F : ExceptionalMap R) : D I.subscheme :=
  (derivedPushforward F.map).obj (derivedUnit (exceptional R))

/-- The exact ordinary/derived unit O_X→Rf_* O_E. -/
def duBoisUnit {S : Over (Spec (.of k))} {I : S.left.IdealSheafData}
    {R : Principalization S I} (F : ExceptionalMap R) :
    derivedUnit I.subscheme ⟶ duBoisZero F :=
  DerivedCategory.Q.map
    ((CochainComplex.singleFunctor I.subscheme.Modules 0).map
      (RationalResolution.structureUnit F.map)) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex
        (Scheme.Modules.pushforward F.map) (.up ℤ) 0).inv.app
          (structureModule (exceptional R))) ≫
    (derivedPushforwardUnit F.map).app
      ((CochainComplex.singleFunctor (exceptional R).Modules 0).obj
        (structureModule (exceptional R)))

/-- Du Bois degree-zero condition on this fixed embedded model/unit. -/
def IsEmbeddedDuBois {S : Over (Spec (.of k))} {I : S.left.IdealSheafData}
    {R : Principalization S I} (F : ExceptionalMap R) : Prop :=
  IsIso (duBoisUnit F)

end MathlibExt.AlgebraicGeometry.EmbeddedDuBoisZero
