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
public import MathlibExt.AlgebraicGeometry.MeromorphicHeckeCoordinates

/-!
# Native meromorphic coordinate and untilt-chart requests

All comparisons refer to the original punctured torsor map, all original
integral frames, and the actual analytic ring maps. The refinement
normalization, now proved in
`MathlibExt.AlgebraicGeometry.MeromorphicHeckeCoordinates`, is a proof about
those completed operations. The chart constructor starts from a real
source-normalized untilt divisor.

The completed-disc torsor constructor, global-to-local Hecke functor,
reflex extensions and B(G)/v-stack endpoints remain separate required
interfaces. The chart request here and the refinement normalization proved in
`MathlibExt.AlgebraicGeometry.MeromorphicHeckeCoordinates` do not supply those
maps.

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

/-- The divisor of an untilt is an étale-locally principal Cartier divisor: let $p$ be a prime, $E$
a finite extension of $\mathbb{Q}_p$ with the given coefficient data, affine realization and integer
presentation, $A$ a family of relative Fargues–Fontaine curves, $T$ an untilt over a base $S$, $D$
the divisor of $T$ on the curve with its formal cover (`UntiltingCartierChartModels.SourceDivisor`)
and $U$ a puncture of it. Then the inclusion of the divisor is a closed embedding, surjective on
stalks, and the divisor is covered by pole charts: affinoid étale neighbourhoods on which a regular
parameter generates its ideal (`CartierAtlas`). -/
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
