/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GlobalFFCurveModels
public import MathlibExt.AlgebraicGeometry.UntiltingCartierChartModels

/-!
# Actual global degree-one Cartier divisor/untilt diagrams

The divisor is an actual closed Cartier analytic map to the specified
relative curve. Above every original perfectoid atlas chart, its full
inverse image is an actual affine untilt with its native theta-adic
formal comparison. Those open untilts cover the divisor, and their
tilt markings assemble to the original global perfectoid base by the
prescribed diamondification map.

The divisor category retains only the existence of these witnesses;
it does not retain an extra chosen untilt marking as object data.
Its arrows are actual maps over the curve and its groupoid is the
native core. The geometric constructor/classification is deferred.
Source: Fargues--Scholze, arXiv:2102.13459v4, Sections I.2 and VI.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GlobalUntiltingDivisorModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Topology
open _root_.AlgebraicGeometry
open LocalWittCoefficientFields LocalCoefficientScalarFrames RelativeFarguesFontaineRings
open RelativeFFCurveFamilies RelativePerfectoidBases GlobalFFCurveModels
open AnalyticTateAdicModels AnalyticAdicDiamondification AnalyticGroupTorsorSites
open MarkedUntiltingPeriodModels UntiltingCartierModels UntiltingCartierChartModels

variable (p : ℕ) [Fact p.Prime] {E : MixedField p} (C : CoefficientData p E)
  (R : AffineRealization p) (I : IntegerPresentation p C)
  (A : RelativeFFCurveFamilies.Family p C I) (F : GlobalFFCurveModels.Family p C I A)
  (S : RelativePerfectoidBases.Space p C)

/-- An existing actual E-untilt of S; existence is not asserted for an arbitrary global base. -/
structure UntiltingModel where
  space : ESpace p E.field
  untilt : ∀ i, Untilting p C ((F.atlas S).labels.base i)
  chart : ∀ i, untiltObject p C R (untilt i) ⟶ space
  open_embedding : ∀ i, IsOpenEmbedding (chart i).left.hom.val.base
  stalk_iso : ∀ i x, IsIso ((chart i).left.hom.val.stalkMap x)
  covers : ∀ x : space.left.obj.space, ∃ i, x ∈ Set.range (chart i).left.hom.val.base
  localTilt : ∀ i, UntiltingCartierModels.TiltComparison p C R (untilt i)
  marking : (diamondFunctor p R).obj space.left ≅ S.perfectoid.sheaf
  marked_chart : ∀ i,
    (diamondFunctor p R).map (chart i).left ≫ marking.hom =
      (localTilt i).comparison.hom ≫ (F.atlas S).labels.chart p C i

structure Witness (D : Over (F.atlas S).curve) where
  closed : UntiltingCartierModels.IsClosed p D.hom
  cartier : UntiltingCartierModels.IsCartier p D.hom
  untilt : ∀ i, Untilting p C ((F.atlas S).labels.base i)
  localDivisor : ∀ i, UntiltingCartierModels.Divisor p C R I A (untilt i)
  localPeriod : ∀ i, UntiltingCartierChartModels.Cover p C R I A (untilt i) (localDivisor i)
  chart : ∀ i, untiltObject p C R (untilt i) ⟶ D.left
  open_embedding : ∀ i, IsOpenEmbedding (chart i).left.hom.val.base
  stalk_iso : ∀ i x, IsIso ((chart i).left.hom.val.stalkMap x)
  square : ∀ i, chart i ≫ D.hom = (localDivisor i).map ≫ (F.atlas S).chart i
  full_preimage : ∀ i, Set.range (chart i).left.hom.val.base =
    D.hom.left.hom.val.base ⁻¹' Set.range ((F.atlas S).chart i).left.hom.val.base
  covers : ∀ x : D.left.left.obj.space, ∃ i, x ∈ Set.range (chart i).left.hom.val.base
  localTilt : ∀ i, UntiltingCartierModels.TiltComparison p C R (untilt i)
  marking : (diamondFunctor p R).obj D.left.left ≅ S.perfectoid.sheaf
  marked_chart : ∀ i,
    (diamondFunctor p R).map (chart i).left ≫ marking.hom =
      (localTilt i).comparison.hom ≫ (F.atlas S).labels.chart p C i

def IsDegreeOne (D : Over (F.atlas S).curve) : Prop := Nonempty (Witness p C R I A F S D)

/-- Objects are the actual Cartier maps; chosen witnesses are absent from their data. -/
abbrev Divisors := Core (show ObjectProperty (Over (F.atlas S).curve) from
  IsDegreeOne p C R I A F S).FullSubcategory

/-- The image of the supplied global untilt preserves its actual marking,
all original affine untilts and their chart maps. -/
structure UntiltingImage (U : UntiltingModel p C R I A F S) where
  map : U.space ⟶ (F.atlas S).curve
  witness : Witness p C R I A F S (Over.mk map)
  untilt_normalized : ∀ i, witness.untilt i = U.untilt i
  chart_normalized : ∀ i, HEq (witness.chart i) (U.chart i)
  marking_normalized : witness.marking = U.marking

end MathlibExt.AlgebraicGeometry.GlobalUntiltingDivisorModels
