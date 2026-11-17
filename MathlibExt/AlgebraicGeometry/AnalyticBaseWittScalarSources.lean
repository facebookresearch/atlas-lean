/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AnalyticProperSmoothSources
public import MathlibExt.CategoryTheory.NativeRingInverseImages
public import MathlibExt.CategoryTheory.WittStructuralScalarBindings

/-!
# Actual base-field normalization of original positive Witt scalars

The Cohen embedding uses the ACTUAL residue field and ring of integers
of the general complete discretely valued base. Every original etale
scalar is fixed by native Gamma of its actual map to Spa(K,O_K), with the
actual affinoid base coordinates. Its pro-site scalar is the native
inverse-image map and constant inverse-image mate. No completed O_X is
substituted for the original regular or positive ring.

Reference: Scholze, arXiv:1205.3463v2, Definition 6.8;
native Mathlib, Apache 2.0, revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AnalyticBaseWittScalarSources

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open AnalyticTateAdicModels AnalyticProperSmoothSources GeneralPadicCoefficientFields
open AnalyticProEtaleCoefficientSources
open MathlibExt.CategoryTheory.NativeRingInverseImages
open MathlibExt.CategoryTheory.WittStructuralScalarBindings
open MathlibExt.CategoryTheory.StructuralDeRhamPeriodSources
open MathlibExt.CategoryTheory.SheafScalarQuotients

variable (p : ℕ) [Fact p.Prime] (K : BaseField p) (B : BaseRealization p K)

/-- Native original coordinates of the ACTUAL affinoid base, fixed by its whole-space isomorphism. -/
def baseCoordinates : BaseField.carrier p K ≃+*
    (_root_.AlgebraicGeometry.LocallyRingedSpace.Γ.obj (op B.analytic.obj.space)) :=
  (B.ring.trans B.model.globalRing).trans
    ((_root_.AlgebraicGeometry.LocallyRingedSpace.Γ.mapIso
      ((forgetValuations.mapIso B.whole).op)).symm.commRingCatIsoToRingEquiv)

variable (X : Over B.analytic) (P : AnalyticProObjectSites.PointRealization p X.left)
  (I : IntegralStructure p X.left)
  (hI : Presheaf.IsSheaf (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) (I.presheaf ⋙ liftRings))
  [HasSheafify (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) CommRingCat.{1}]
  [HasSheafify (proTopology p X.left P) CommRingCat.{1}]
  [(etaleInclusion p X.left).IsContinuous
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) (proTopology p X.left P)]
  [((etaleInclusion p X.left).sheafPushforwardContinuous CommRingCat.{1}
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) (proTopology p X.left P)).IsRightAdjoint]
  (C : CohenWittSource p K)

structure CohenEtaleSource where
  map : constantWitt (J := AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) p K ⟶
    IntegralStructure.positiveEtale (p := p) (X := X.left) (A := I) hI
  original_source : ∀ (U : (AnalyticProObjectSites.Etale p X.left)ᵒᵖ)
    (w : WittVector p (BaseField.residueField p K)),
    (((map.hom.app U).hom)
      (((toSheafify (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left)
        ((Functor.const (AnalyticProObjectSites.Etale p X.left)ᵒᵖ).obj
          (CommRingCat.of (ULift.{1} (WittVector p (BaseField.residueField p K)))))).app U).hom
            (ULift.up w))).down.val =
      ((_root_.AlgebraicGeometry.LocallyRingedSpace.Γ.map
        ((U.unop.obj.hom ≫ X.hom).hom.val).op).hom)
          (baseCoordinates p K B ((C.embedding w : BaseField.integralRing p K) : BaseField.carrier p K))

variable [IsIso (constantInverseMap
  (J := AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) (T := proTopology p X.left P)
  (etaleInclusion p X.left) (WittVector p (BaseField.residueField p K)))]

/-- Original positive Cohen scalars on the FULL formal pro-site, by the native inverse-image maps. -/
def positiveCohenScalars (S : CohenEtaleSource p K B X I hI C) :
    constantWitt (J := proTopology p X.left P) p K ⟶ originalPositive p X.left P I hI :=
  inv (constantInverseMap (J := AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left)
    (T := proTopology p X.left P) (etaleInclusion p X.left)
      (WittVector p (BaseField.residueField p K))) ≫
    ((etaleInclusion p X.left).sheafPullback CommRingCat.{1}
      (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) (proTopology p X.left P)).map S.map

/-- The tilt scalar source must use exactly these original positive Cohen scalars. -/
structure QualifiedResidueSource (S : CohenEtaleSource p K B X I hI C) where
  residue : ResidueScalarSource p (originalPositive p X.left P I hI) K
  positive_source : residue.positive = positiveCohenScalars p K B X P I hI C S

/-- The native inclusion of the ORIGINAL positive inverse image into the ORIGINAL regular inverse image. -/
def positiveInclusion
    (hO : Presheaf.IsSheaf (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left)
      (etaleRingsLarge p X.left)) :
    originalPositive p X.left P I hI ⟶ originalStructure p X.left P hO :=
  ((etaleInclusion p X.left).sheafPullback CommRingCat.{1}
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) (proTopology p X.left P)).map
      (ObjectProperty.homMk (Functor.whiskerRight I.inclusion liftRings))

end MathlibExt.AlgebraicGeometry.AnalyticBaseWittScalarSources
