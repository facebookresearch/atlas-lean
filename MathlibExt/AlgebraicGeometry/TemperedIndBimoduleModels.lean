/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LocalBetaDifferentialActionModels
public import MathlibExt.AlgebraicGeometry.TemperedDifferentialActionModels
public import MathlibExt.AlgebraicGeometry.GeometricDModuleFiltrations

/-!
# Tempered distributions in actual Ind(k_X) with full beta-D/Dbar actions

The carrier is a native Bimod over the actual beta differential rings.
Its underlying object is the source-qualified subanalytic distribution
Ind object. Both local-End actions are computed from the actual open
inverse image, monoidal beta section maps and original bimodule actions.
Every source probe is normalized to the full LF transpose on V compact
in U. This couples the analytic section data to both actual native ring
actions; ordinary-module Ind completion is not used.

Source: DK1311.2374v2 Section4.10, Definition5.1.1, Proposition5.1.3,
Definition5.2.1; Mathlib56a005 native Ind/Bimod maps, Apache2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.TemperedIndBimoduleModels

open _root_.CategoryTheory _root_.Opposite TopologicalSpace
open CompactSupportIndSheaves IndSheafCoefficientModels IndSheafInverseImageModels
open NativeIndDifferentialContexts LocalBetaDifferentialActionModels
open SubanalyticIndDistributionModels TemperedDifferentialActionModels
open ManifoldDistributionModels AnalyticChartDifferentialOperators

open scoped Manifold ContDiff

variable [∀ Z : TopCat.{0}, HasSheafify (Opens.grothendieckTopology Z) (ModuleCat.{0} ℂ)]
  (n : ℕ) (M : Type) [TopologicalSpace M]
  [ChartedSpace (TemperedDistributionSectionModels.ComplexCoordinates n) M]
  [IsManifold 𝓘(ℂ, TemperedDistributionSectionModels.ComplexCoordinates n) ∞ M]
  [HasSheafify (Opens.grothendieckTopology M) RingCat.{0}]
  [CompactSheafSource ℂ (TopCat.of M)]

local instance temperedModuleIndPreadditive : Preadditive (IndSheaf ℂ (TopCat.of M)) :=
  Abelian.toPreadditive

variable [IndSpaceSource (TopCat.of M)]
  [DifferentialBetaSource M (analyticCoefficients n M)]
  [OppositeDifferentialBetaSource M (analyticConjugateCoefficients n M)]
  [∀ U : Opens M, CompactSheafSource ℂ (TopCat.of U)]
  [∀ U : Opens M, IndSpaceSource (TopCat.of U)]
  [∀ U : Opens M, BetaRingSource (TopCat.of U)
    (pulledRing (TopCat.of M) U (analyticDifferentialRing n M))]
  [∀ U : Opens M, BetaRingSource (TopCat.of U)
    (pulledRing (TopCat.of M) U (analyticConjugateOppositeRing n M))]
  (C : CompactOpenCoefficientSource n M)
  (A : ChartOpenSource n M) (J : TestDensityTransferSource n M A)
  (R : TemperedRestrictionSource n M A J)
  (D : TemperedIndDistributionSource n M C A J R)
  (P : TemperedChartProjectionSource n M A J)
  (L : TemperedOperatorSource n M A J P (analyticCoefficients n M)
    (holomorphicChartValue n M) false)
  (B : TemperedOperatorSource n M A J P (analyticConjugateCoefficients n M)
    (conjugateChartValue n M) true)

abbrev TemperedBimodule := Bimod (betaRing (TopCat.of M) (analyticDifferentialRing n M))
  (betaRing (TopCat.of M) (analyticConjugateOppositeRing n M))

def localProbeMap (F : TemperedBimodule n M) (underlying : F.X ≅ D.object)
    (U : Opens M)
    (N : LocalRestrictedModuleSource (TopCat.of M) U
      (analyticDifferentialRing n M) (analyticConjugateOppositeRing n M) F)
    (V : RelativelyCompactSubanalyticOpen n M) (s : openProbe n M C V ⟶ D.object) :
    (indInverseImage ℂ (openInclusion (TopCat.of M) U) N.ordinary N.inverse).obj
      (openProbe n M C V) ⟶
        restrictedUnderlying (TopCat.of M) U (analyticDifferentialRing n M)
          (analyticConjugateOppositeRing n M) F N :=
  letI := N.monoidal
  (indInverseImage ℂ (openInclusion (TopCat.of M) U) N.ordinary N.inverse).map
    (s ≫ underlying.inv) ≫ N.mapping.underlying.inv.app F

/-- A construction must satisfy both native local-End normalizations on every original source probe. -/
structure TemperedDoubleModuleSource where
  object : TemperedBimodule n M
  underlying : object.X ≅ D.object
  restrictions : ∀ U : Opens M, LocalRestrictedModuleSource (TopCat.of M) U
    (analyticDifferentialRing n M) (analyticConjugateOppositeRing n M) object
  leftSections : ∀ U : Opens M, OrdinaryRingSectionSource (TopCat.of M) U
    (analyticDifferentialRing n M)
  rightSections : ∀ U : Opens M, OrdinaryRingSectionSource (TopCat.of M) U
    (analyticConjugateOppositeRing n M)
  leftValue : ∀ (U : Opens M)
      (Q : DifferentialOperatorSheaves.finiteOperatorRing ℂ M (analyticCoefficients n M) U)
      (V : RelativelyCompactSubanalyticOpen n M) (hVU : closure (V.openSet : Set M) ⊆ U)
      (s : openProbe n M C V ⟶ D.object),
    localProbeMap n M C A J R D object underlying U (restrictions U) V s ≫
      localLeftEnd (TopCat.of M) U (analyticDifferentialRing n M)
        (analyticConjugateOppositeRing n M) object (restrictions U) (leftSections U)
          (GeometricDModuleFiltrations.operatorValue
            (TemperedDistributionSectionModels.ComplexCoordinates n) M Q) =
      localProbeMap n M C A J R D object underlying U (restrictions U) V
        ((D.sections V).symm (L.action U Q V hVU (D.sections V s)))
  rightValue : ∀ (U : Opens M)
      (Q : DifferentialOperatorSheaves.finiteOperatorRing ℂ M
        (analyticConjugateCoefficients n M) U)
      (V : RelativelyCompactSubanalyticOpen n M) (hVU : closure (V.openSet : Set M) ⊆ U)
      (s : openProbe n M C V ⟶ D.object),
    localProbeMap n M C A J R D object underlying U (restrictions U) V s ≫
      localRightEnd (TopCat.of M) U (analyticDifferentialRing n M)
        (analyticConjugateOppositeRing n M) object (restrictions U) (rightSections U)
          (RightDifferentialModules.rightOperatorValue ℂ M (analyticConjugateCoefficients n M) U Q) =
      localProbeMap n M C A J R D object underlying U (restrictions U) V
        ((D.sections V).symm (B.action U Q V hVU (D.sections V s)))

end MathlibExt.AlgebraicGeometry.TemperedIndBimoduleModels
