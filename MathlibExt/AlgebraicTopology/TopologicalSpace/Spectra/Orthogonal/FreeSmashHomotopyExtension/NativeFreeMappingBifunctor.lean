/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.SourceNativeMappingBifunctor
import MathlibExt.CategoryTheory.Equivalence.FunctorFamily
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.CanonicalSourceRightModuleFreeEvaluation

/-!
# Free-source internal Hom under the orthogonal carrier equivalence

Compares internal Hom from a free orthogonal spectrum with the free-source module-Hom
family transported through the canonical carrier equivalence. The natural isomorphism
uses the free-object comparison and the complete transported internal-Hom bifunctor,
retaining both coefficient and target variances.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
noncomputable section
universe u v
open CategoryTheory MonoidalCategory Limits
open CategoryTheory.Enriched CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open PointedCGWH.Spectra.Orthogonal
open CategoryTheory.Spectra.OrthogonalSourceRightModule
open scoped MonoidalClosed CategoryTheory.MonObj

universe uCmpA vCmpA uCmpC vCmpC uCmpD vCmpD

private def restrictFamily {A : Type uCmpA} [Category.{vCmpA} A]
    {C : Type uCmpC} [Category.{vCmpC} C] {D : Type uCmpD} [Category.{vCmpD} D]
    (E : C ≌ D) {Q : Dᵒᵖ ⥤ (D ⥤ D)} {R : Cᵒᵖ ⥤ (C ⥤ C)}
    (eR : Q ≅ E.inverse.op ⋙ R ⋙ ((E.congrLeft (E := C)).trans
      (E.congrRight (E := D))).functor)
    (F : A ⥤ D) (G : A ⥤ C) (eF : G ≅ F ⋙ E.inverse) :
    F.op ⋙ Q ≅ G.op ⋙ R ⋙ ((E.congrLeft (E := C)).trans
      (E.congrRight (E := D))).functor :=
  Functor.isoWhiskerLeft F.op eR ≪≫
    Functor.isoWhiskerRight (NatIso.op eF)
      (R ⋙ ((E.congrLeft (E := C)).trans (E.congrRight (E := D))).functor)

attribute [local instance] SphereSmashStructure.indexCategory
  SphereSmashStructure.indexMonoidalCategory SphereSmashStructure.indexEnrichedOrdinaryCategory
  SphereSmashStructure.indexSymmetricCategory SphereSmashStructure.dayMonoidalCategory
  SphereSmashStructure.daySymmetricCategory SphereSmashStructure.sphereMonoid
  SphereSmashStructure.sphereCommutativeMonoid SphereSmashStructure.spaceCoequalizers
  Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
  CanonicalSourceSmash.monoidalCategory CanonicalSourceSmashClosed.monoidalClosed
local instance : HasLimitsOfSize.{0, 0} PointedCGWH.{u, v} :=
  PointedCGWH.EnrichedMapping.hasSmallLimits.{u, v}

namespace OrthogonalIGeneratorProbe.FreeSourceBif

private abbrev q := SphereSmash.sourceData.{u, v}
private abbrev c := CanonicalSourceSmash.sourceContext.{u, v}

/-- The free right-module functor at `r` in the canonical source presentation. -/
def sourceFree (r : OrthogonalIndex) : PointedCGWH.{u, v} ⥤ CanonicalSourceRightModuleActions.SourceModule.{u, v} :=
  CanonicalSourceRightModuleFreeEvaluation.freeFunctor.{u, v} r

/-- The native free orthogonal-spectrum functor at the operator corresponding to `r`. -/
def nativeFree (r : OrthogonalIndex) : PointedCGWH.{u, v} ⥤ CanonicalSourceSmash.Carrier.{u, v} :=
  Free.functor (OrthogonalOperatorIndex.ofIndex.{u, v} r)

/-- The free right-module functor compared with the inverse image of the native free-spectrum
functor. -/
def freeComparison (r : OrthogonalIndex) : sourceFree.{u, v} r ≅ nativeFree.{u, v} r ⋙ c.{u, v}.equivalence.inverse :=
  CanonicalSourceRightModuleFreeEvaluation.freeComparison.{u, v} r

/-- The free-source module-Hom family transported to native spectra in both endofunctor variables. -/
def sourceMapping (r : OrthogonalIndex) : PointedCGWH.{u, v}ᵒᵖ ⥤
    (CanonicalSourceSmash.Carrier.{u, v} ⥤ CanonicalSourceSmash.Carrier.{u, v}) :=
  (sourceFree.{u, v} r).op ⋙ SelectedNativeBif.sourceBif q.{u, v} ⋙
    (c.{u, v}.equivalence.congrLeft.trans c.{u, v}.equivalence.congrRight).functor

/-- The native internal Hom family with source the free orthogonal spectrum at `r`. -/
def nativeMapping (r : OrthogonalIndex) : PointedCGWH.{u, v}ᵒᵖ ⥤
    (CanonicalSourceSmash.Carrier.{u, v} ⥤ CanonicalSourceSmash.Carrier.{u, v}) :=
  (nativeFree.{u, v} r).op ⋙ MonoidalClosed.internalHom

set_option maxHeartbeats 500000 in
-- Compose the whole parameter comparisons before resolving the native source dictionary.
/-- The native free-source internal Hom family compared with the transported free-source
module-Hom family. -/
def comparison (r : OrthogonalIndex) :=
  restrictFamily c.{u, v}.equivalence
    (SelectedNativeBif.comparison q.{u, v} c.{u, v})
    (nativeFree.{u, v} r) (sourceFree.{u, v} r) (freeComparison.{u, v} r)








end OrthogonalIGeneratorProbe.FreeSourceBif
