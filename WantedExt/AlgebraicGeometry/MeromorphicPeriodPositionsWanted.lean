/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.MeromorphicPeriodPositionMaps
public import MathlibExt.AlgebraicGeometry.ReductiveGroupSchemeModels
public import MathlibExt.AlgebraicGeometry.AnalyticProObjectSites

/-!
# Actual source period bridges and Hecke position comparison requests

The chart constructor starts from the full source marked-untilt cover.
Its bridge uses the actual chart model/global-ring dictionary and every
finite completion stage. The Cartier/period parameter unit is explicit.
Position and lattice requests concern the actual completed global
comparison, with every representation and every original frame retained.

Source: Fargues--Scholze, arXiv:2102.13459v4, Sections III.3 and VI.1--VI.2.
No classification or Hecke-stack equivalence is a hypothesis.
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

/-- Match each actual source untilt period chart to its native whole analytic pole chart. -/
public def_wanted untiltPeriodPoleChart (p : ℕ) [Fact p.Prime]
    {E : MixedField p} (K : CoefficientData p E)
    (R : AffineRealization p) (I : IntegerPresentation p K)
    (A : RelativeFFCurveFamilies.Family p K I) {S : Base p K}
    (T : Untilting p K S)
    (D : UntiltingCartierChartModels.SourceDivisor p K R I A T)
    (i : D.periods.index)
    (hV : IsStronglyNoetherian p (D.periods.chart i).chart.curve.pair)
    (U : Puncture p E.field D.divisor.map) :
    MatchedPeriodPoleChart p K R I A T D.divisor (D.periods.chart i) U

section GeneralFormalLattices

/-- Realize every actual formal representation image as its original finite-projective lattice. -/
public def_wanted representedFormalLattice (p : ℕ) [Fact p.Prime]
    (E : Type) [Field E] (G : Over (Spec (.of E))) [GrpObj G]
    [ReductiveGroupSchemeModels.IsReductive (Spec (.of E)) G]
    (H : ∀ W : ESpace p E, GroupDescent p E G W)
    (P : PullbackPreservation p E G H)
    {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
    (Q : PoleChart p E d U)
    (hQ : IsStronglyNoetherian p (wholePoleChart p E d U Q).pair)
    (Aq : Algebraization p E G H Q.space)
    (Bq : FpqcPreservesTorsors E G (completionBaseMap p E d U Q))
    (F : SourceFrames p E G H P d U Q Aq)
    (h : IsUnit (sectionMap p E Q.puncture.map Q.parameter))
    (C : MeromorphicTorsorCompletion.CompletionComparison p E G H P d U Q Aq Bq F h)
    (M : Hecke p E G H P d U)
    (left : IntegralFrame p E G H d U Q (originalModification p E G H P d U M).left)
    (right : IntegralFrame p E G H d U Q (originalModification p E G H P d U M).right)
    (n : ℕ) (ρ : Representation E G n) :
    RepresentedFormalLattice p E G H P d U Q Aq Bq F h C M left right n ρ

end GeneralFormalLattices

section SourcePeriods

variable (p : ℕ) [Fact p.Prime] {E : MixedField p} (K : CoefficientData p E)
  (R : AffineRealization p) (I : IntegerPresentation p K)
  (A : RelativeFFCurveFamilies.Family p K I) {S : Base p K}
  (T : Untilting p K S) (D : UntiltingCartierModels.Divisor p K R I A T)
  (V : UntiltingCartierChartModels.PeriodChart p K R I A T D)
  {X Z : ESpace p E.field} (d : Z ⟶ X) (U : Puncture p E.field d)
  (Q : PoleChart p E.field d U)
  (B : PeriodBridge p K R I A T D V d U Q)

/-- Bijectivity concerns the same actual parameter-unit normalized localization map. -/
public theorem_wanted genericPeriodMap_bijective :
    Function.Bijective (genericPeriodMap p K R I A T D V d U Q B)

variable (G : Over (Spec (.of E.field))) [GrpObj G]
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

/-- Exact source position agrees with the actual period double orbit, retaining its unit. -/
public theorem_wanted localPosition_iff_period
    [ReductiveGroupSchemeModels.IsReductive (Spec (.of E.field)) G]
    (μ : Cocharacter E.field G) :
    HasLocalPosition p E.field G H P d U Q Aq Bq F h C M left right μ ↔
      HasPeriodPosition p K R I A T D V d U Q B G H P Aq Bq F h C M left right μ

/-- Every original representation gives the actual computed period lattice image. -/
public def_wanted representedPeriodLattice
    [ReductiveGroupSchemeModels.IsReductive (Spec (.of E.field)) G]
    (n : ℕ) (ρ : Representation E.field G n) :
    PeriodGroupPositionModels.RepresentedLattice p K V.chart.refinement.untilt
      V.scalar V.parameter G ρ
        (periodElement p K R I A T D V d U Q B G H P Aq Bq F h C M left right)

/-- Every lattice generator follows the same original completed coefficient/period square. -/
public theorem_wanted periodModule_generator_map
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

/-- Every change of original integral frames preserves the actual relative position. -/
public theorem_wanted periodPosition_frame_independence
    [ReductiveGroupSchemeModels.IsReductive (Spec (.of E.field)) G]
    (left' : IntegralFrame p E.field G H d U Q (originalModification p E.field G H P d U M).left)
    (right' : IntegralFrame p E.field G H d U Q (originalModification p E.field G H P d U M).right)
    (μ : Cocharacter E.field G) :
    HasPeriodPosition p K R I A T D V d U Q B G H P Aq Bq F h C M left right μ ↔
      HasPeriodPosition p K R I A T D V d U Q B G H P Aq Bq F h C M left' right' μ

/-- Closed representation-lattice bounds retain the same all-frame invariance. -/
public theorem_wanted periodBound_frame_independence
    [ReductiveGroupSchemeModels.IsReductive (Spec (.of E.field)) G]
    (left' : IntegralFrame p E.field G H d U Q (originalModification p E.field G H P d U M).left)
    (right' : IntegralFrame p E.field G H d U Q (originalModification p E.field G H P d U M).right)
    (μ : Cocharacter E.field G) :
    IsPeriodBounded p K R I A T D V d U Q B G H P Aq Bq F h C M left right μ ↔
      IsPeriodBounded p K R I A T D V d U Q B G H P Aq Bq F h C M left' right' μ

end SourcePeriods

end WantedExt.AlgebraicGeometry.MeromorphicPeriodPositions
