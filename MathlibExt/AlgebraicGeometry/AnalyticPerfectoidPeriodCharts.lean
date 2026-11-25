/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AnalyticPeriodPullbackSources
public import MathlibExt.CategoryTheory.StructuralPeriodConnectionSources
public import Mathlib.RingTheory.MvPowerSeries.Trunc
public import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Original affinoid-perfectoid toric period charts

Each chart retains an ACTUAL represented affinoid boundary of the full
formal pro-site and its actual perfectoid Tate pair. Its coordinates
come from a finite ORIGINAL etale stage through the original native
inverse-image unit. Compatible tilt roots and a hereditary differential
basis fix the local structural coordinates u_i. They lie in the ORIGINAL
structural theta kernel before completion.

The local Taylor map is fixed on EVERY finite theta quotient by native
finite polynomial evaluation of truncTotal. It is a positive structural
period source. No completeness is asserted for full O_BdR and no whole
structural theta ideal is inverted.

References: Scholze, arXiv:1205.3463v2, Theorem 6.5 and Proposition 6.10;
native Mathlib, Apache 2.0, revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AnalyticPerfectoidPeriodCharts

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open AnalyticTateAdicModels AnalyticProperSmoothSources GeneralPadicCoefficientFields
open QualifiedStructuralPeriodSites AnalyticProEtaleCoefficientSources AnalyticPeriodPullbackSources
open MathlibExt.RingTheory.CompleteHuberPairModels
open MathlibExt.CategoryTheory.RingedDerivedCoefficientOperations
open MathlibExt.CategoryTheory.SheafScalarQuotients
open MathlibExt.CategoryTheory.SheafWittSource
open MathlibExt.CategoryTheory.SheafKernelCompletion
open MathlibExt.CategoryTheory.UntiltingSheafSources
open MathlibExt.CategoryTheory.SheafLocalGeneratorLocalization

section PowerSeries

universe v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (A : Sheaf J CommRingCat.{1}) (n : ℕ)

def rawPowerSeries : Cᵒᵖ ⥤ CommRingCat.{1} where
  obj U := CommRingCat.of (MvPowerSeries (Fin n) (A.obj.obj U))
  map f := CommRingCat.ofHom (MvPowerSeries.map (A.obj.map f).hom)
  map_id U := by ext s d; simp
  map_comp f g := by ext s d; simp

variable [HasSheafify J CommRingCat.{1}]

def powerSeriesSheaf : Sheaf J CommRingCat.{1} :=
  (presheafToSheaf J CommRingCat.{1}).obj (rawPowerSeries A n)

end PowerSeries

section AbsoluteForms

open MathlibExt.CategoryTheory.NativeRingInverseImages

variable (p : ℕ) [Fact p.Prime] (K : BaseField p) (B : BaseRealization p K)
  (X : Over B.analytic) (P : AnalyticProObjectSites.PointRealization p X.left)
  [HasSheafify (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) CommRingCat.{1}]
  [HasSheafify (proTopology p X.left P) CommRingCat.{1}]
  [(etaleInclusion p X.left).IsContinuous
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) (proTopology p X.left P)]
  [((etaleInclusion p X.left).sheafPushforwardContinuous CommRingCat.{1}
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) (proTopology p X.left P)).IsRightAdjoint]
  [IsIso (constantInverseMap
    (J := AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) (T := proTopology p X.left P)
    (etaleInclusion p X.left) (WittVector p (BaseField.residueField p K)))]
  [HasSheafify (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) AddCommGrpCat.{1}]
  [(AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left).WEqualsLocallyBijective AddCommGrpCat.{1}]
  (S : Source p K B X P)
  (Ω : AnalyticRelativeDeRhamSources.DifferentialSource p X.hom S.regularSheaf)

def originalRingUnit : regularEtale p X.left S.regularSheaf ⟶
    ((etaleInclusion p X.left).sheafPushforwardContinuous CommRingCat.{1}
      (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) (proTopology p X.left P)).obj S.regular :=
  inverseUnit (etaleInclusion p X.left) (regularEtale p X.left S.regularSheaf)

variable [(modulePushforward (etaleInclusion p X.left) (regularEtale p X.left S.regularSheaf)
  S.regular (originalRingUnit p K B X P S)).IsRightAdjoint]

/-- Absolute Omega_X/K is the ORIGINAL native module inverse image of the continuous etale forms. -/
def absoluteForms : Modules S.regular :=
  (modulePullback (etaleInclusion p X.left) (regularEtale p X.left S.regularSheaf)
    S.regular (originalRingUnit p K B X P S)).obj Ω.oneForms

structure AbsoluteFormSource where
  differential : ∀ U : (AnalyticProObjectSites.ProEtaleSite p X.left)ᵒᵖ,
    S.regular.obj.obj U →+ (absoluteForms p K B X P S Ω).val.obj U
  natural : ∀ {U V : (AnalyticProObjectSites.ProEtaleSite p X.left)ᵒᵖ} (f : U ⟶ V) a,
    differential V ((S.regular.obj.map f).hom a) =
      (absoluteForms p K B X P S Ω).val.map f (differential U a)
  leibniz : ∀ U a b, differential U (a * b) = a • differential U b + b • differential U a
  original_source : ∀ (U : (AnalyticProObjectSites.Etale p X.left)ᵒᵖ)
    (a : (regularEtale p X.left S.regularSheaf).obj.obj U),
    differential ((etaleInclusion p X.left).op.obj U) ((originalRingUnit p K B X P S).hom.app U a) =
      (((moduleAdjunction (etaleInclusion p X.left) (regularEtale p X.left S.regularSheaf)
        S.regular (originalRingUnit p K B X P S)).unit.app Ω.oneForms).val.app U).hom
          (Ω.differential U a)

end AbsoluteForms

variable (p : ℕ) [Fact p.Prime] (K : BaseField p) (B : BaseRealization p K)
  (X : Over B.analytic) (P : AnalyticProObjectSites.PointRealization p X.left)
  [HasSheafify (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) CommRingCat.{1}]
  [HasSheafify (proTopology p X.left P) CommRingCat.{1}]
  [(etaleInclusion p X.left).IsContinuous
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) (proTopology p X.left P)]
  [((etaleInclusion p X.left).sheafPushforwardContinuous CommRingCat.{1}
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) (proTopology p X.left P)).IsRightAdjoint]
  [IsIso (MathlibExt.CategoryTheory.NativeRingInverseImages.constantInverseMap
    (J := AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) (T := proTopology p X.left P)
    (etaleInclusion p X.left) (WittVector p (BaseField.residueField p K)))]
  (S : Source p K B X P) (Ω : Modules S.regular)
  (d : ∀ U : (AnalyticProObjectSites.ProEtaleSite p X.left)ᵒᵖ, S.regular.obj.obj U →+ Ω.val.obj U)

def stageCoordinate (U : AnalyticProObjectSites.RepresentedBoundary p X.left P)
    (i : U.presentation.ind.I)
    (a : (etaleRings p X.left).obj (op (U.presentation.ind.F.obj i).unop)) : S.regular.obj.obj (op U.formal) :=
  (S.regular.obj.map (formalProjection p X.left U.presentation i).op).hom
    (((((etaleInclusion p X.left).sheafAdjunctionContinuous CommRingCat.{1}
      (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) (proTopology p X.left P)).unit.app
        (regularEtale p X.left S.regularSheaf)).hom.app (op (U.presentation.ind.F.obj i).unop)).hom
          (ULift.up a))

structure ToricChart where
  boundary : AnalyticProObjectSites.RepresentedBoundary p X.left P
  perfectoid : ∃ A : PerfectoidPair p, boundary.chart.pair = TatePair.ofPerfectoid p A
  dimension : ℕ
  stage : boundary.presentation.ind.I
  original : Fin dimension → (etaleRings p X.left).obj (op (boundary.presentation.ind.F.obj stage).unop)
  root : Fin dimension → (tilt p S.positive).obj.obj (op boundary.formal)
  sharp_source : ∀ i,
    ((localizePUnit p (positiveCompletion p S.positive)).hom.app (op boundary.formal)).hom
      (S.untilting.sharp (op boundary.formal) (root i)) =
    (S.scalars.originalTheta.hom.app (op boundary.formal)).hom
      (stageCoordinate p K B X P S boundary stage (original i))
  basis : ∀ (V : AnalyticProObjectSites.ProEtaleSite p X.left) (_f : V ⟶ boundary.formal),
    _root_.Module.Basis (Fin dimension) (S.regular.obj.obj (op V)) (Ω.val.obj (op V))
  basis_source : ∀ V f i, basis V f i =
    Ω.val.map f.op (d (op boundary.formal) (stageCoordinate p K B X P S boundary stage (original i)))
  thetaGenerator : S.absolutePositive.obj.obj (op boundary.formal)
  generator_source : IsLocalGenerator S.absolutePositive (completedRegular p S.positive)
    S.untilting.completedTheta (op boundary.formal) thetaGenerator

namespace ToricChart

variable (C : ToricChart p K B X P S Ω d)

/-- The finite original stage is an actual affinoid, finite etale over a rational polydisc.
Both its K scalars and coordinate functions are fixed by native original Gamma. -/
structure CoordinateSource where
  pair : TatePair p
  model : AffinoidModel p pair
  whole : model.valued ≅ (C.boundary.presentation.ind.F.obj C.stage).unop.obj.left.obj
  polydisc : TatePowerSeries p B.pair C.dimension
  neighborhood : RationalTateModel p polydisc.pair
  etale : TateRingMap p neighborhood.pair pair
  finite_etale : AnalyticDiamondEtaleSites.IsFiniteEtalePair p etale
  coordinateLift : Fin C.dimension → polydisc.pair.ring
  variable_source : ∀ i, (polydisc.coordinates (coordinateLift i)).val = MvPowerSeries.X i
  coefficient_source : ∀ a : B.pair.ring,
    (((_root_.AlgebraicGeometry.LocallyRingedSpace.Γ.mapIso
      ((forgetValuations.mapIso whole).op)).symm.commRingCatIsoToRingEquiv)
        (model.globalRing (etale.hom (neighborhood.map.hom (polydisc.scalar.hom a))))) =
    ((_root_.AlgebraicGeometry.LocallyRingedSpace.Γ.map
      ((((C.boundary.presentation.ind.F.obj C.stage).unop.obj.hom ≫ X.hom).hom.val).op)).hom)
        (AnalyticBaseWittScalarSources.baseCoordinates p K B (B.ring.symm a))
  coordinate_source : ∀ i,
    C.original i =
      (((_root_.AlgebraicGeometry.LocallyRingedSpace.Γ.mapIso
        ((forgetValuations.mapIso whole).op)).symm.commRingCatIsoToRingEquiv)
          (model.globalRing (etale.hom (neighborhood.map.hom (coordinateLift i)))))

def infCoordinate (i : Fin C.dimension) : S.scalars.naiveStructuralInf.obj.obj (op C.boundary.formal) :=
  (S.scalars.originalToInf.hom.app (op C.boundary.formal)).hom
    (stageCoordinate p K B X P S C.boundary C.stage (C.original i)) -
  (S.scalars.absoluteToInf.hom.app (op C.boundary.formal)).hom
    (((localizePUnit p (inf p S.positive)).hom.app (op C.boundary.formal)).hom
      (((toSheafify (proTopology p X.left P) (wittPresheaf p (tilt p S.positive))).app
        (op C.boundary.formal)).hom (WittVector.teichmuller p (C.root i))))

def structuralCoordinate (i : Fin C.dimension) : S.naiveStructuralPositive.obj.obj (op C.boundary.formal) :=
  (S.scalars.infToPositive.hom.app (op C.boundary.formal)).hom
    (infCoordinate p K B X P S Ω d C i)

end ToricChart

/-- Qualified actual affinoid-perfectoid toric boundaries cover EVERY formal pro-object. -/
def HasToricCover : Prop :=
  ∀ U : AnalyticProObjectSites.ProEtaleSite p X.left,
    Sieve.generate (fun V (_ : V ⟶ U) =>
      ∃ C : ToricChart p K B X P S Ω d,
        Nonempty (ToricChart.CoordinateSource p K B X P S Ω d C) ∧ C.boundary.formal = V) ∈
      proTopology p X.left P U

variable [∀ U : AnalyticProObjectSites.ProEtaleSite p X.left,
  HasSheafify ((proTopology p X.left P).over U) CommRingCat.{1}]

/-- Source evaluation on the ACTUAL slice site, fixed by all native finite completion projections. -/
structure TaylorSource (C : ToricChart p K B X P S Ω d) where
  map : powerSeriesSheaf (S.absolutePositive.over C.boundary.formal) C.dimension ⟶
    S.naiveStructuralPositive.over C.boundary.formal
  finite_source : ∀ (V : (Over C.boundary.formal)ᵒᵖ)
    (f : MvPowerSeries (Fin C.dimension) ((S.absolutePositive.over C.boundary.formal).obj.obj V)) (n : ℕ),
    ((projection S.scalars.naiveStructuralInf (completedRegular p S.positive) S.scalars.structuralTheta n).hom.app
      (op V.unop.left)).hom
        ((map.hom.app V).hom
          (((toSheafify ((proTopology p X.left P).over C.boundary.formal)
            (rawPowerSeries (S.absolutePositive.over C.boundary.formal) C.dimension)).app V).hom f)) =
    MvPolynomial.eval₂Hom
      (((projection S.scalars.naiveStructuralInf (completedRegular p S.positive) S.scalars.structuralTheta n).hom.app
        (op V.unop.left)).hom.comp (S.scalars.absoluteToPositive.hom.app (op V.unop.left)).hom)
      (fun i => ((projection S.scalars.naiveStructuralInf (completedRegular p S.positive) S.scalars.structuralTheta n).hom.app
        (op V.unop.left)).hom ((S.naiveStructuralPositive.obj.map V.unop.hom.op).hom
          (ToricChart.structuralCoordinate p K B X P S Ω d C i)))
      (MvPowerSeries.truncTotal (n + 1) f)

end MathlibExt.AlgebraicGeometry.AnalyticPerfectoidPeriodCharts
