/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.UntiltingCartierModels
public import MathlibExt.AlgebraicGeometry.AnalyticDiamondEtaleSites

/-!
# Source-normalized local formal neighbourhoods of untilt divisors

A chart retains an actual open untilt refinement and an actual curve
affinoid. Its inverse image of the divisor is exactly that refinement.
The curve chart lifts into the original relative annulus, with the
full quotient/base-change square. Thus its original Witt coefficients
are computed from actual pulled-back annular sections.

Theta is the actual map on curve-chart sections induced by the untilt
closed map. The completion is literally its kernel-adic completion.
Comparison with native B_dR-plus fixes every original coefficient,
theta reduction and every filtration level. Refinements cover the
actual untilt; a single global affinoid neighbourhood is not assumed.
Source: Fargues--Scholze, arXiv:2102.13459v4, Sections III.3 and VI.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.UntiltingCartierChartModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite TopologicalSpace Topology
open _root_.AlgebraicGeometry
open LocalWittCoefficientFields LocalCoefficientScalarFrames RelativeFarguesFontaineRings
open RelativeFarguesFontaineMaps MarkedUntiltingPeriodModels AffinoidPeriodRings
open AnalyticTateAdicModels AnalyticDiamondEtaleSites RelativeFFCurveFamilies
open UntiltingCartierModels

/-- Actual section pullback to a source contained in the given open. -/
def pullOnOpen {Y Z : LocallyRingedSpace.{0}} (f : Y ⟶ Z) (U : Opens Z)
    (h : ∀ y : Y, f.base y ∈ U) :
    Z.presheaf.obj (op U) →+* Y.presheaf.obj (op ⊤) := by
  have hU : (⊤ : Opens Y) ≤ (Opens.map f.base).obj U := by
    intro y hy
    exact h y
  exact (Y.presheaf.map (homOfLE hU).op).hom.comp (f.c.app (op U)).hom

variable (p : ℕ) [Fact p.Prime] {E : MixedField p} (C : CoefficientData p E)
  (R : AffineRealization p) (I : IntegerPresentation p C)
  (A : RelativeFFCurveFamilies.Family p C I) {S : Base p C}
  (T : Untilting p C S) (D : UntiltingCartierModels.Divisor p C R I A T)

structure Chart where
  refinement : Refinement p C R T
  curve : AnalyticDiamondEtaleSites.Chart p ((A.frame S).object p C I).left
  untilt : (untiltObject p C R refinement.untilt).left.obj ⟶ curve.model.valued
  untilt_square : untilt ≫ curve.map = refinement.map.left.hom ≫ D.map.left.hom
  full_preimage : Set.range untilt.val.base =
    curve.map.val.base ⁻¹' Set.range D.map.left.hom.val.base
  presentation : RationalPresentation p C refinement.base
  annular : curve.model.valued ⟶ ((A.frame refinement.base).annularSpace p C I).obj
  annular_mem : ∀ x : curve.model.valued.space,
    annular.val.base x ∈ (A.frame refinement.base).annularOpen p C I presentation
  annular_square : annular ≫ ((A.frame refinement.base).quotientMap p C I).hom ≫
    (A.change refinement.baseMap).map.left.hom = curve.map

variable (Q : Chart p C R I A T D)

/-- Original coefficients are actual pullbacks of their annular local-section germs. -/
def rawCoefficient : Ring p C Q.refinement.base →+* Q.curve.pair.ring :=
  Q.curve.model.globalRing.symm.toRingHom.comp
    ((pullOnOpen Q.annular.val
      ((A.frame Q.refinement.base).annularOpen p C I Q.presentation) Q.annular_mem).comp
        ((A.frame Q.refinement.base).annularCoefficient p C I Q.presentation))

/-- Theta is fixed by the actual untilt-to-curve map on original affine coordinates. -/
def theta : Q.curve.pair.ring →+* Q.refinement.untilt.affine.pair.ring :=
  (R.model Q.refinement.untilt.affine).globalRing.symm.toRingHom.comp
    ((Q.untilt.val.c.app (op ⊤)).hom.comp Q.curve.model.globalRing.toRingHom)

abbrev FormalRing := AdicCompletion (RingHom.ker (theta p C R I A T D Q)) Q.curve.pair.ring

variable (L : ScalarLift p C Q.refinement.base Q.refinement.untilt)

set_option maxHeartbeats 1200000 in
-- Allow the dependent native period-ring and sheaf signatures to elaborate.
structure CompletionComparison where
  equivalence : FormalRing p C R I A T D Q ≃+* DeRhamPlus p Q.refinement.untilt.affine.pair
  coefficients : ∀ a : Ring p C Q.refinement.base,
    equivalence (algebraMap Q.curve.pair.ring (FormalRing p C R I A T D Q)
      (rawCoefficient p C R I A T D Q a)) = periodEmbedding p C Q.refinement.untilt L a
  theta : (thetaPlusToRing p Q.refinement.untilt.affine.pair).comp
    (equivalence.toRingHom.comp (algebraMap _ _)) =
      UntiltingCartierChartModels.theta p C R I A T D Q
  filtration : ∀ n : ℕ,
    Ideal.comap equivalence.toRingHom (AffinoidPeriodRings.filtration p
      Q.refinement.untilt.affine.pair n) =
      RingHom.ker ((AdicCompletion.evalₐ
        (RingHom.ker (UntiltingCartierChartModels.theta p C R I A T D Q)) n).toRingHom)

structure PeriodChart where
  chart : Chart p C R I A T D
  scalar : ScalarLift p C chart.refinement.base chart.refinement.untilt
  comparison : CompletionComparison p C R I A T D chart scalar
  parameter : Parameter p C chart.refinement.untilt scalar

/-- Every original untilt point lies in an actual source-normalized formal chart. -/
structure Cover where
  index : Type
  chart : index → PeriodChart p C R I A T D
  covers : ∀ x : (untiltObject p C R T).left.obj.space, ∃ i,
    x ∈ Set.range (chart i).chart.refinement.map.left.hom.val.base

/-- A source untilt divisor retains its actual theta-normalized formal cover.
An arbitrary closed Cartier map is only a candidate for this structure. -/
structure SourceDivisor where
  divisor : UntiltingCartierModels.Divisor p C R I A T
  periods : Cover p C R I A T divisor

end MathlibExt.AlgebraicGeometry.UntiltingCartierChartModels
