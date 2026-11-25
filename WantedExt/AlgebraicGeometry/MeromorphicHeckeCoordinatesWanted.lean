/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.MeromorphicHeckeModels
public import MathlibExt.AlgebraicGeometry.UntiltingCartierChartModels

/-!
# Native meromorphic coordinate and untilt-chart requests

All comparisons refer to the original punctured torsor map, all original
integral frames, and the actual analytic ring maps. The refinement
normalization below is a proof about those completed operations. The
chart constructor starts from a real source-normalized untilt divisor.

The completed-disc torsor constructor, global-to-local Hecke functor,
reflex extensions and B(G)/v-stack endpoints remain separate required
interfaces. These two requests do not supply those maps.

Source: Fargues--Scholze, arXiv:2102.13459v4, Section III.3 and VI.1.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.MeromorphicHeckeCoordinates

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open AnalyticGroupTorsorSites AnalyticBundlePrestackModels AnalyticBundleModifications
open AnalyticMeromorphicCoordinates

/-- The global comparison element represents the original map on every refined point. -/
public theorem_wanted comparison_refinement_normalization
    (p : ℕ) [Fact p.Prime] (E : Type) [Field E]
    (G : Over (Spec (.of E))) [GrpObj G]
    (H : ∀ V : ESpace p E, GroupDescent p E G V)
    (P : PullbackPreservation p E G H)
    {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
    (Q : PoleChart p E d U) (M : Modification p E G H P d U)
    (left : IntegralFrame p E G H d U Q M.left)
    (right : IntegralFrame p E G H d U Q M.right)
    (T : Site p E Q.puncture.space) (a : (pointGroups p E G).obj (op T.left)) :
    comparisonValue p E G H P d U Q M left right T a =
      ((pointGroups p E G).map T.hom.op).hom
        (comparisonElement p E G H P d U Q M left right) * a

/-- Actual etale Cartier pole charts of the fixed marked-untilt divisor. -/
public def_wanted untiltPoleCharts
    (p : ℕ) [Fact p.Prime] {E : LocalWittCoefficientFields.MixedField p}
    (C : LocalWittCoefficientFields.CoefficientData p E)
    (R : AnalyticTateAdicModels.AffineRealization p)
    (I : LocalCoefficientScalarFrames.IntegerPresentation p C)
    (A : RelativeFFCurveFamilies.Family p C I)
    {S : RelativeFarguesFontaineRings.Base p C}
    (T : MarkedUntiltingPeriodModels.Untilting p C S)
    (D : UntiltingCartierChartModels.SourceDivisor p C R I A T)
    (U : Puncture p E.field D.divisor.map) :
    CartierAtlas p E.field D.divisor.map U

end WantedExt.AlgebraicGeometry.MeromorphicHeckeCoordinates
