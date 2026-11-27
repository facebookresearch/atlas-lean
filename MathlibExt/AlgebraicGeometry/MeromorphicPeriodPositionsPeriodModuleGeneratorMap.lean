/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MeromorphicPeriodPositionMaps
import MathlibExt.AlgebraicGeometry.ReductiveGroupSchemeModels
import MathlibExt.AlgebraicGeometry.AnalyticProObjectSites

/-!
# Period module generators under the original coefficient map

Every represented lattice generator follows the original completed
coefficient and period square.

Source: Fargues--Scholze, arXiv:2102.13459v4, Sections III.3 and VI.1--VI.2.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.MeromorphicPeriodPositions

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open LocalWittCoefficientFields RelativeFarguesFontaineRings MarkedUntiltingPeriodModels
open LocalCoefficientScalarFrames AnalyticTateAdicModels AffinoidPeriodRings
open AnalyticGroupTorsorSites AnalyticBundlePrestackModels AnalyticBundleModifications
open AnalyticMeromorphicCoordinates MeromorphicHeckeModels AffinoidTorsorAlgebraizationModels
open CompletedTorsorSourceFrames MeromorphicTorsorCompletion MeromorphicPeriodPositionMaps
open AlgebraicGroupPointRepresentations AnalyticProObjectSites
open MathlibExt.LinearAlgebra.LocalizedLattices

/-- Every lattice generator follows the same original completed coefficient/period square. -/
public theorem periodModule_generator_map
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
    (n : ℕ) (ρ : Representation E.field G n) (v : Fin n → FormalRing p E.field d U Q) :
    (PeriodGroupPositionModels.representationMatrix p K V.chart.refinement.untilt
      V.scalar V.parameter G ρ
        (periodElement p K R I A T D V d U Q B G H P Aq Bq F h C M left right) :
          Matrix (Fin n) (Fin n)
            (FractionRing (DeRhamPlus p V.chart.refinement.untilt.affine.pair)
              V.parameter.value)).mulVec
              (fun i ↦ algebraMap _ _
                (positivePeriod p K R I A T D V d U Q B.toCompletionDictionary (v i))) =
      fun i ↦ genericPeriodMap p K R I A T D V d U Q B
        ((framedMatrix p E.field G H P d U Q Aq Bq F h C M left right n ρ).mulVec
          (fun j ↦ algebraMap _ (GenericRing p E.field d U Q) (v j)) i)
    := by
  have hn := ConcreteCategory.congr_hom
    (ρ.naturality (periodTestMap p K R I A T D V d U Q B))
      (framedElement p E.field G H P d U Q Aq Bq F h C M left right)
  have hm := congrArg (fun a : GL (Fin n)
    (FractionRing (DeRhamPlus p V.chart.refinement.untilt.affine.pair) V.parameter.value) ↦
      (a : Matrix (Fin n) (Fin n)
        (FractionRing (DeRhamPlus p V.chart.refinement.untilt.affine.pair)
          V.parameter.value))) hn
  change (PeriodGroupPositionModels.representationMatrix p K V.chart.refinement.untilt
    V.scalar V.parameter G ρ
      (periodElement p K R I A T D V d U Q B G H P Aq Bq F h C M left right) :
        Matrix (Fin n) (Fin n)
          (FractionRing (DeRhamPlus p V.chart.refinement.untilt.affine.pair)
            V.parameter.value)) =
      (framedMatrix p E.field G H P d U Q Aq Bq F h C M left right n ρ).map
        (genericPeriodMap p K R I A T D V d U Q B) at hm
  rw [hm]
  funext i
  simpa only [Function.comp_def,
    genericPeriodMap_coefficients p K R I A T D V d U Q B] using
      ((genericPeriodMap p K R I A T D V d U Q B).map_mulVec
        (framedMatrix p E.field G H P d U Q Aq Bq F h C M left right n ρ)
        (fun j ↦ algebraMap _ (GenericRing p E.field d U Q) (v j)) i).symm

end WantedExt.AlgebraicGeometry.MeromorphicPeriodPositions
