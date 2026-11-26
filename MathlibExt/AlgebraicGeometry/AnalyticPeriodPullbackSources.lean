/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.QualifiedStructuralPeriodSites
public import MathlibExt.AlgebraicGeometry.AnalyticRelativeDeRhamSources
public import MathlibExt.CategoryTheory.RingedComplexInverseImageSources
public import MathlibExt.CategoryTheory.RingSheafMapOperations

/-!
# Actual analytic original and continuous coefficient pullback sources

The original ring map is the native inverse-image adjunction mate of
Gamma of every original analytic pullback. The point projection is
fixed on EVERY full formal pro-object presentation and every original
finite-stage projection. Continuous integral/rational coefficient maps
are constructed from that actual point projection and TARGET native
sheafification, with no global integral rational-system lattice.

Reference: Scholze, arXiv:1205.3463v2, Sections 3, 6 and 8;
Bhatt--Morrow--Scholze, arXiv:1602.03148v3, Section 5.1.
Native Mathlib, Apache 2.0, revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AnalyticPeriodPullbackSources

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.CategoryTheory.Functor
open AnalyticTateAdicModels AnalyticProperSmoothSources GeneralPadicCoefficientFields
open AnalyticProEtaleCoefficientSources QualifiedStructuralPeriodSites
open MathlibExt.CategoryTheory.NativeRingInverseImages
open MathlibExt.CategoryTheory.RingedComplexInverseImageSources
open MathlibExt.CategoryTheory.SheafKernelCompletion
open MathlibExt.CategoryTheory.SheafScalarQuotients
open MathlibExt.CategoryTheory.UntiltingSheafSources
open MathlibExt.CategoryTheory.SheafLocalGeneratorLocalization

variable (p : ℕ) [Fact p.Prime]

/-- Every original presentation projection is a FULL native formal pro-morphism. -/
def formalProjection (X : AnalyticAdicSpace p) {F : AnalyticProObjectSites.Presheaves p X}
    (P : AnalyticProObjectSites.ProEtalePresentation p X F) (i : P.ind.I) :
    AnalyticProObjectSites.presentedObject p X P ⟶ (etaleInclusion p X).obj (P.ind.F.obj i).unop :=
  (ObjectProperty.homMk (P.ind.ι.app i)).op

def etaleForgetIso (X : AnalyticAdicSpace p) :
    etaleInclusion p X ⋙ AnalyticProObjectSites.forget p X ≅ AnalyticProObjectSites.representable p X :=
  Iso.refl _

def etalePointIso (X : AnalyticAdicSpace p) (P : AnalyticProObjectSites.PointRealization p X) :
    etaleInclusion p X ⋙ P.functor ≅ AnalyticProObjectSites.etaleSpaces p X :=
  isoWhiskerLeft (etaleInclusion p X) P.restriction ≪≫
    (Functor.associator (etaleInclusion p X) (AnalyticProObjectSites.forget p X) P.realization).symm ≪≫
    isoWhiskerRight (etaleForgetIso p X) P.realization ≪≫ P.original

variable (K : BaseField p) (B : BaseRealization p K) (X Y : Over B.analytic) (f : X ⟶ Y)
  (PX : AnalyticProObjectSites.PointRealization p X.left)
  (PY : AnalyticProObjectSites.PointRealization p Y.left)
  [HasSheafify (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) CommRingCat.{1}]
  [HasSheafify (AnalyticDiamondEtaleSites.analyticEtaleTopology p Y.left) CommRingCat.{1}]
  [HasSheafify (proTopology p X.left PX) CommRingCat.{1}]
  [HasSheafify (proTopology p Y.left PY) CommRingCat.{1}]
  [(etaleInclusion p X.left).IsContinuous
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) (proTopology p X.left PX)]
  [(etaleInclusion p Y.left).IsContinuous
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p Y.left) (proTopology p Y.left PY)]
  [((etaleInclusion p X.left).sheafPushforwardContinuous CommRingCat.{1}
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) (proTopology p X.left PX)).IsRightAdjoint]
  [((etaleInclusion p Y.left).sheafPushforwardContinuous CommRingCat.{1}
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p Y.left) (proTopology p Y.left PY)).IsRightAdjoint]
  [IsIso (constantInverseMap
    (J := AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) (T := proTopology p X.left PX)
    (etaleInclusion p X.left) (WittVector p (BaseField.residueField p K)))]
  [IsIso (constantInverseMap
    (J := AnalyticDiamondEtaleSites.analyticEtaleTopology p Y.left) (T := proTopology p Y.left PY)
    (etaleInclusion p Y.left) (WittVector p (BaseField.residueField p K)))]
  (SX : Source p K B X PX) (SY : Source p K B Y PY)
  (E : EtaleBaseChangeSource p f.left) (Q : ProBaseChangeSource p f.left E)
  [E.functor.IsContinuous
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p Y.left) (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left)]
  [(E.functor.sheafPushforwardContinuous CommRingCat.{1}
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p Y.left)
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left)).IsRightAdjoint]
  [Q.functor.IsContinuous (proTopology p Y.left PY) (proTopology p X.left PX)]
  [(Q.functor.sheafPushforwardContinuous CommRingCat.{1}
    (proTopology p Y.left PY) (proTopology p X.left PX)).IsRightAdjoint]
  (N : RingSquare
    (J₁ := AnalyticDiamondEtaleSites.analyticEtaleTopology p Y.left)
    (T₁ := AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left)
    (J₂ := proTopology p Y.left PY) (T₂ := proTopology p X.left PX)
    E.functor Q.functor (etaleInclusion p Y.left) (etaleInclusion p X.left))

abbrev push := Q.functor.sheafPushforwardContinuous CommRingCat.{1}
  (proTopology p Y.left PY) (proTopology p X.left PX)

/-- Native original ring inverse-image map of the actual original analytic Gamma scalar. -/
def originalMap : SY.regular ⟶ (push p K B X Y f PX PY E Q).obj SX.regular :=
  (Q.functor.sheafAdjunctionContinuous CommRingCat.{1}
    (proTopology p Y.left PY) (proTopology p X.left PX)).homEquiv SY.regular SX.regular
      (N.ordinary.hom.app (regularEtale p Y.left SY.regularSheaf) ≫
        ((etaleInclusion p X.left).sheafPullback CommRingCat.{1}
          (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) (proTopology p X.left PX)).map
            (inverseScalar E.functor (regularEtale p Y.left SY.regularSheaf) (regularEtale p X.left SX.regularSheaf)
              (AnalyticRelativeDeRhamSources.regularScalar p f.left E SX.regularSheaf SY.regularSheaf)))

/-- The condition that pullback along $f$ preserves integral functions: for every object $U$ of the
small étale site of $Y$, pullback along the projection $U \times_Y X \to U$ maps the functions $a$
on $U$ with $|a(x)| \le 1$ at every point $x$ (for the valuation at $x$) to functions on
$U \times_Y X$ with the same property. -/
def PositivePreservation : Prop :=
  ∀ (U : (AnalyticProObjectSites.Etale p Y.left)ᵒᵖ) (a : SY.integral.rings U),
    ((E.regularScalar.app U).hom a.val) ∈ SX.integral.rings (E.functor.op.obj U)

def positiveEtaleRaw (h : PositivePreservation p K B X Y f PX PY SX SY E) :
    SY.integral.presheaf ⟶ E.functor.op ⋙ SX.integral.presheaf where
  app U := CommRingCat.ofHom
    { toFun := fun (a : SY.integral.rings U) => ⟨(E.regularScalar.app U).hom a.val, h U a⟩
      map_one' := by apply Subtype.ext; exact map_one _
      map_mul' a b := by apply Subtype.ext; exact map_mul _ _ _
      map_zero' := by apply Subtype.ext; exact map_zero _
      map_add' a b := by apply Subtype.ext; exact map_add _ _ _ }
  naturality {U V} a := by
    ext x
    apply Subtype.ext
    exact congrArg (fun g => g.hom (Subtype.val x)) (E.regularScalar.naturality a)

def positiveEtaleMap (h : PositivePreservation p K B X Y f PX PY SX SY E) :
    IntegralStructure.positiveEtale (p := p) (X := Y.left) (A := SY.integral) SY.positiveSheaf ⟶
    (E.functor.sheafPushforwardContinuous CommRingCat.{1}
      (AnalyticDiamondEtaleSites.analyticEtaleTopology p Y.left)
      (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left)).obj
        (IntegralStructure.positiveEtale (p := p) (X := X.left) (A := SX.integral) SX.positiveSheaf) :=
  ObjectProperty.homMk (whiskerRight (positiveEtaleRaw p K B X Y f PX PY SX SY E h) liftRings)

def positiveMap (h : PositivePreservation p K B X Y f PX PY SX SY E) :
    SY.positive ⟶ (push p K B X Y f PX PY E Q).obj SX.positive :=
  (Q.functor.sheafAdjunctionContinuous CommRingCat.{1}
    (proTopology p Y.left PY) (proTopology p X.left PX)).homEquiv SY.positive SX.positive
      (N.ordinary.hom.app
        (IntegralStructure.positiveEtale (p := p) (X := Y.left) (A := SY.integral) SY.positiveSheaf) ≫
        ((etaleInclusion p X.left).sheafPullback CommRingCat.{1}
          (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) (proTopology p X.left PX)).map
            (inverseScalar E.functor
              (IntegralStructure.positiveEtale (p := p) (X := Y.left) (A := SY.integral) SY.positiveSheaf)
              (IntegralStructure.positiveEtale (p := p) (X := X.left) (A := SX.integral) SX.positiveSheaf)
              (positiveEtaleMap p K B X Y f PX PY SX SY E h)))

structure PointProjectionSource where
  point : Q.functor ⋙ PX.functor ⟶ PY.functor
  original_projection : ∀ {F : AnalyticProObjectSites.Presheaves p Y.left}
    (P : AnalyticProObjectSites.ProEtalePresentation p Y.left F) (i : P.ind.I),
    PX.functor.map (Q.functor.map (formalProjection p Y.left P i) ≫ N.site.hom.app (P.ind.F.obj i).unop) ≫
      (etalePointIso p X.left PX).hom.app (E.functor.obj (P.ind.F.obj i).unop) ≫
      (E.projection.app (P.ind.F.obj i).unop).hom.val.base =
    point.app (AnalyticProObjectSites.presentedObject p Y.left P) ≫ (PY.iso P).hom ≫
      limit.π (AnalyticProObjectSites.diagram p Y.left P ⋙ AnalyticProObjectSites.etaleSpaces p Y.left) (op i)

variable (P : PointProjectionSource p K B X Y f PX PY E Q N)

def rawContinuousPull (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    (continuousRings p Y.left PY A ⋙ liftRings) ⟶ Q.functor.op ⋙ (continuousRings p X.left PX A ⋙ liftRings) where
  app U := CommRingCat.ofHom
    { toFun := fun (a : ULift.{1} C(PY.functor.obj U.unop, A)) =>
        ULift.up (a.down.comp (P.point.app U.unop).hom)
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }
  naturality {U V} a := by
    ext s
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    exact congrArg (ContinuousMap.toFun (s.down : C(PY.functor.obj U.unop, A)))
      (congrArg (fun g => g.hom x) (P.point.naturality a.unop)).symm

/-- Actual continuous coefficient sheaf pullback map, after TARGET sheafification. -/
def coefficientMap (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    continuousCoefficientSheaf p Y.left PY A ⟶ (push p K B X Y f PX PY E Q).obj
      (continuousCoefficientSheaf p X.left PX A) :=
  ((sheafificationAdjunction (proTopology p Y.left PY) CommRingCat.{1}).homEquiv
    (continuousRings p Y.left PY A ⋙ liftRings)
    ((push p K B X Y f PX PY E Q).obj (continuousCoefficientSheaf p X.left PX A))).symm
      (rawContinuousPull p K B X Y f PX PY E Q N P A ≫
        whiskerLeft Q.functor.op (toSheafify (proTopology p X.left PX) (continuousRings p X.left PX A ⋙ liftRings)))

section PeriodMaps

variable (h : PositivePreservation p K B X Y f PX PY SX SY E)

def modMap : modP p SY.positive ⟶ (push p K B X Y f PX PY E Q).obj (modP p SX.positive) :=
  MathlibExt.CategoryTheory.RingSheafMapOperations.modPMap Q.functor p SY.positive SX.positive
    (positiveMap p K B X Y f PX PY SX SY E Q N h)

def positiveQuotientMap (n : ℕ) :
    quotientSheaf SY.positive (modP p SY.positive) (modPUnit p SY.positive) n ⟶
    (push p K B X Y f PX PY E Q).obj
      (quotientSheaf SX.positive (modP p SX.positive) (modPUnit p SX.positive) n) :=
  MathlibExt.CategoryTheory.RingSheafMapOperations.quotientMap Q.functor
    SY.positive (modP p SY.positive) (modPUnit p SY.positive)
    SX.positive (modP p SX.positive) (modPUnit p SX.positive)
    (positiveMap p K B X Y f PX PY SX SY E Q N h) (modMap p K B X Y f PX PY SX SY E Q N h)
    (by simpa [modMap] using
      (MathlibExt.CategoryTheory.RingSheafMapOperations.modPMap_unit Q.functor p SY.positive SX.positive
        (positiveMap p K B X Y f PX PY SX SY E Q N h)).symm) n

def infMap (a : tilt p SY.positive ⟶ (push p K B X Y f PX PY E Q).obj (tilt p SX.positive)) :
    inf p SY.positive ⟶ (push p K B X Y f PX PY E Q).obj (inf p SX.positive) :=
  MathlibExt.CategoryTheory.RingSheafMapOperations.wittMap Q.functor p (tilt p SY.positive) (tilt p SX.positive) a

def binfMap (a : tilt p SY.positive ⟶ (push p K B X Y f PX PY E Q).obj (tilt p SX.positive)) :
    rationalInf p SY.positive ⟶ (push p K B X Y f PX PY E Q).obj (rationalInf p SX.positive) :=
  MathlibExt.CategoryTheory.RingSheafMapOperations.localizePMap Q.functor p (inf p SY.positive) (inf p SX.positive)
    (infMap p K B X Y f PX PY SX SY E Q a)

def hatMap (a : positiveCompletion p SY.positive ⟶ (push p K B X Y f PX PY E Q).obj (positiveCompletion p SX.positive)) :
    completedRegular p SY.positive ⟶ (push p K B X Y f PX PY E Q).obj (completedRegular p SX.positive) :=
  MathlibExt.CategoryTheory.RingSheafMapOperations.localizePMap Q.functor p
    (positiveCompletion p SY.positive) (positiveCompletion p SX.positive) a

/-- Maps of period sheaves along $f$, from the period sheaves of $Y$ to the pushforwards along $f$
of those of $X$: maps on the completed integral structure sheaf $\widehat{\mathcal{O}}^+$, on its
tilt, on $\mathbb{B}^+_{\mathrm{dR}}$ and on the naive structural sheaves
$\mathcal{O}\mathbb{B}_{\mathrm{inf}}$ and $\mathcal{O}\mathbb{B}^+_{\mathrm{dR}}$. Each of these
maps commutes with the projections to the finite quotient levels, on which it induces the maps
given by the integral pullback `h` (for $\widehat{\mathcal{O}}^+$ and the tilt) or by the maps on
$\mathbb{B}_{\mathrm{inf}}$ and $\mathcal{O}\mathbb{B}_{\mathrm{inf}}$ (for
$\mathbb{B}^+_{\mathrm{dR}}$ and $\mathcal{O}\mathbb{B}^+_{\mathrm{dR}}$). The maps commute with
$\theta$, with the structure maps from $\mathcal{O}$ and $\mathbb{B}_{\mathrm{inf}}$ to
$\mathcal{O}\mathbb{B}_{\mathrm{inf}}$ and with the map from $\mathbb{B}^+_{\mathrm{dR}}$ to
$\mathcal{O}\mathbb{B}^+_{\mathrm{dR}}$, and the map on $\mathbb{B}^+_{\mathrm{dR}}$ sends local
generators of $\ker\theta$ to local generators of $\ker\theta$. -/
structure NaturalPeriodMaps where
  completedPositive : positiveCompletion p SY.positive ⟶
    (push p K B X Y f PX PY E Q).obj (positiveCompletion p SX.positive)
  completedPositive_source : ∀ n : ℕ,
    completedPositive ≫ (push p K B X Y f PX PY E Q).map (positiveProjection p SX.positive n) =
      positiveProjection p SY.positive n ≫ positiveQuotientMap p K B X Y f PX PY SX SY E Q N h n
  tilt : MathlibExt.CategoryTheory.UntiltingSheafSources.tilt p SY.positive ⟶
    (push p K B X Y f PX PY E Q).obj (MathlibExt.CategoryTheory.UntiltingSheafSources.tilt p SX.positive)
  tilt_source : ∀ n : ℕ, tilt ≫ (push p K B X Y f PX PY E Q).map (tiltProjection p SX.positive n) =
    tiltProjection p SY.positive n ≫ modMap p K B X Y f PX PY SX SY E Q N h
  absoluteThetaSquare : binfMap p K B X Y f PX PY SX SY E Q tilt ≫
    (push p K B X Y f PX PY E Q).map SX.untilting.rationalTheta =
      SY.untilting.rationalTheta ≫ hatMap p K B X Y f PX PY SX SY E Q completedPositive
  absolutePositive : SY.absolutePositive ⟶ (push p K B X Y f PX PY E Q).obj SX.absolutePositive
  absolutePositive_source : ∀ n : ℕ,
    absolutePositive ≫ (push p K B X Y f PX PY E Q).map
      (projection (rationalInf p SX.positive) (completedRegular p SX.positive) SX.untilting.rationalTheta n) =
    projection (rationalInf p SY.positive) (completedRegular p SY.positive) SY.untilting.rationalTheta n ≫
      MathlibExt.CategoryTheory.RingSheafMapOperations.quotientMap Q.functor
        (rationalInf p SY.positive) (completedRegular p SY.positive) SY.untilting.rationalTheta
        (rationalInf p SX.positive) (completedRegular p SX.positive) SX.untilting.rationalTheta
        (binfMap p K B X Y f PX PY SX SY E Q tilt)
        (hatMap p K B X Y f PX PY SX SY E Q completedPositive) absoluteThetaSquare n
  naiveStructuralInf : SY.scalars.naiveStructuralInf ⟶ (push p K B X Y f PX PY E Q).obj SX.scalars.naiveStructuralInf
  structuralInf_original : SY.scalars.originalToInf ≫ naiveStructuralInf =
    originalMap p K B X Y f PX PY SX SY E Q N ≫ (push p K B X Y f PX PY E Q).map SX.scalars.originalToInf
  structuralInf_absolute : SY.scalars.absoluteToInf ≫ naiveStructuralInf =
    binfMap p K B X Y f PX PY SX SY E Q tilt ≫ (push p K B X Y f PX PY E Q).map SX.scalars.absoluteToInf
  structuralThetaSquare : naiveStructuralInf ≫ (push p K B X Y f PX PY E Q).map SX.scalars.structuralTheta =
    SY.scalars.structuralTheta ≫ hatMap p K B X Y f PX PY SX SY E Q completedPositive
  naiveStructuralPositive : SY.naiveStructuralPositive ⟶ (push p K B X Y f PX PY E Q).obj SX.naiveStructuralPositive
  structuralPositive_source : ∀ n : ℕ,
    naiveStructuralPositive ≫ (push p K B X Y f PX PY E Q).map
      (projection SX.scalars.naiveStructuralInf (completedRegular p SX.positive) SX.scalars.structuralTheta n) =
    projection SY.scalars.naiveStructuralInf (completedRegular p SY.positive) SY.scalars.structuralTheta n ≫
      MathlibExt.CategoryTheory.RingSheafMapOperations.quotientMap Q.functor
        SY.scalars.naiveStructuralInf (completedRegular p SY.positive) SY.scalars.structuralTheta
        SX.scalars.naiveStructuralInf (completedRegular p SX.positive) SX.scalars.structuralTheta
        naiveStructuralInf (hatMap p K B X Y f PX PY SX SY E Q completedPositive) structuralThetaSquare n
  absoluteScalar_source : SY.scalars.absoluteToPositive ≫ naiveStructuralPositive =
    absolutePositive ≫ (push p K B X Y f PX PY E Q).map SX.scalars.absoluteToPositive
  thetaGenerators : ∀ (U : (AnalyticProObjectSites.ProEtaleSite p Y.left)ᵒᵖ)
    (t : SY.absolutePositive.obj.obj U),
    IsLocalGenerator SY.absolutePositive (completedRegular p SY.positive) SY.untilting.completedTheta U t →
      IsLocalGenerator SX.absolutePositive (completedRegular p SX.positive) SX.untilting.completedTheta
        (Q.functor.op.obj U) ((absolutePositive.hom.app U).hom t)

namespace NaturalPeriodMaps

variable (M : NaturalPeriodMaps p K B X Y f PX PY SX SY E Q N h)

def absoluteFullMap : SY.absoluteFull ⟶ (push p K B X Y f PX PY E Q).obj SX.absoluteFull :=
  MathlibExt.CategoryTheory.RingSheafMapOperations.localizationMap Q.functor
    SY.absolutePositive (completedRegular p SY.positive) SY.absolutePositive SY.untilting.completedTheta (𝟙 _)
    SX.absolutePositive (completedRegular p SX.positive) SX.absolutePositive SX.untilting.completedTheta (𝟙 _)
    M.absolutePositive M.absolutePositive (by simp) M.thetaGenerators

def structuralFullMap : SY.naiveStructuralFull ⟶ (push p K B X Y f PX PY E Q).obj SX.naiveStructuralFull :=
  MathlibExt.CategoryTheory.RingSheafMapOperations.localizationMap Q.functor
    SY.absolutePositive (completedRegular p SY.positive) SY.naiveStructuralPositive
      SY.untilting.completedTheta SY.scalars.absoluteToPositive
    SX.absolutePositive (completedRegular p SX.positive) SX.naiveStructuralPositive
      SX.untilting.completedTheta SX.scalars.absoluteToPositive
    M.absolutePositive M.naiveStructuralPositive M.absoluteScalar_source M.thetaGenerators

end NaturalPeriodMaps

end PeriodMaps

end MathlibExt.AlgebraicGeometry.AnalyticPeriodPullbackSources
