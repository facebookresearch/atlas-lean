/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.MeromorphicPeriodPositionsPeriodModuleGeneratorMap
import MathlibExt.AlgebraicGeometry.ReductiveGroupSchemeModels
import MathlibExt.AlgebraicGeometry.AnalyticProObjectSites

/-!
# Period matrix column compatibility

A standard basis generator in positive dimension identifies each period
matrix column with the image of the original framed matrix column.

Source: Fargues--Scholze, arXiv:2102.13459v4, Sections III.3 and VI.1--VI.2.
-/

set_option autoImplicit false
noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.MeromorphicPeriodPositionsPeriodModuleGeneratorMap

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open LocalWittCoefficientFields RelativeFarguesFontaineRings MarkedUntiltingPeriodModels
open LocalCoefficientScalarFrames AnalyticTateAdicModels AffinoidPeriodRings
open AnalyticGroupTorsorSites AnalyticBundlePrestackModels AnalyticBundleModifications
open AnalyticMeromorphicCoordinates MeromorphicHeckeModels AffinoidTorsorAlgebraizationModels
open CompletedTorsorSourceFrames MeromorphicTorsorCompletion MeromorphicPeriodPositionMaps
open AlgebraicGroupPointRepresentations AnalyticProObjectSites
open MathlibExt.LinearAlgebra.LocalizedLattices

private theorem column_map
    (p : ℕ) [Fact p.Prime] {E : MixedField p} (K : CoefficientData p E)
    (R : AffineRealization p) (I : IntegerPresentation p K)
    (A : RelativeFFCurveFamilies.Family p K I) {S : Base p K}
    (T : Untilting p K S) (D : UntiltingCartierModels.Divisor p K R I A T)
    (V : UntiltingCartierChartModels.PeriodChart p K R I A T D)
    {X Z : ESpace p E.field} (d : Z ⟶ X) (U : Puncture p E.field d)
    (Q : PoleChart p E.field d U)
    (B : PeriodBridge p K R I A T D V d U Q)
    (G : Over (Spec (.of E.field))) [GrpObj G]
    (H : ∀ W : ESpace p E.field, GroupDescent p E.field G W)
    (P : PullbackPreservation p E.field G H)
    (Aq : Algebraization p E.field G H Q.space)
    (Bq : FpqcPreservesTorsors E.field G (completionBaseMap p E.field d U Q))
    (F : SourceFrames p E.field G H P d U Q Aq)
    (h : IsUnit (sectionMap p E.field Q.puncture.map Q.parameter))
    (C : MeromorphicTorsorCompletion.CompletionComparison p E.field G H P d U Q Aq Bq F h)
    (M : Hecke p E.field G H P d U)
    (left : IntegralFrame p E.field G H d U Q (originalModification p E.field G H P d U M).left)
    (right : IntegralFrame p E.field G H d U Q (originalModification p E.field G H P d U M).right)
    (n : ℕ) (ρ : Representation E.field G (n + 1)) (i j : Fin (n + 1)) :
    (PeriodGroupPositionModels.representationMatrix p K V.chart.refinement.untilt
      V.scalar V.parameter G ρ
        (periodElement p K R I A T D V d U Q B G H P Aq Bq F h C M left right) :
          Matrix (Fin (n + 1)) (Fin (n + 1))
            (FractionRing (DeRhamPlus p V.chart.refinement.untilt.affine.pair)
              V.parameter.value)) i j =
      genericPeriodMap p K R I A T D V d U Q B
        (framedMatrix p E.field G H P d U Q Aq Bq F h C M left right (n + 1) ρ i j) := by
  have hgen := WantedExt.AlgebraicGeometry.MeromorphicPeriodPositions.periodModule_generator_map
    p K R I A T D V d U Q B G H P Aq Bq F h C M left right (n + 1) ρ (Pi.single j 1)
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using congrFun hgen i

end MathlibExtTest.AlgebraicGeometry.MeromorphicPeriodPositionsPeriodModuleGeneratorMap
