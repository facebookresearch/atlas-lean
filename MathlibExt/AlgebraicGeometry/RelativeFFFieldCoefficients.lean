/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativeFFAnalyticModels
public import MathlibExt.AlgebraicGeometry.LocalCoefficientScalarFrames

/-!
# Original local-field coefficients on the actual FF curve

The curve coefficient map is fixed by restriction through the native
invariant-sheaf inclusion to every actual annular rational ring. Its
value there is the literal localization lift of the original O_E Witt
tensor factor. This binds the E-space used by the G-torsor site to the
displayed relative curve; an arbitrary scalar action is insufficient.
Source: Fargues--Scholze, arXiv:2102.13459v4, Section I.2.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RelativeFFFieldCoefficients

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite TopologicalSpace
open _root_.AlgebraicGeometry
open LocalWittCoefficientFields RelativeFarguesFontaineRings RelativeFarguesFontaineSheaves
open RelativeFFAnalyticModels LocalCoefficientScalarFrames AnalyticGroupTorsorSites

variable (p : ℕ) [Fact p.Prime] {E : MixedField p} (C : CoefficientData p E)
  (F : IntegerPresentation p C) (S : Base p C) [D : RationalRestrictions p C S]
  (φ : FrobeniusPoints p C S) (O : PeriodSheaf p C S)
  (g : O.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat (frobeniusMap p C S φ)).obj O.sheaf)
  (A : AnnularModel p C S O) (Q : QuotientModel p C S φ O g A)

/-- Restriction uses the actual invariant inclusion and actual annular section comparison. -/
def coefficientRestriction (P : RationalPresentation p C S) :
    (globalRings p).obj (op Q.curve) →+* ChartRing p C S P :=
  (O.rationalComparison.hom.app (op P)).hom.comp
    ((O.sheaf.obj.map (homOfLE (show P.openSet ≤ ⊤ from le_top)).op).hom.comp
      (((invariantInclusion p C S φ O g).hom.app (op ⊤)).hom.comp
        (Q.comparison.hom.hom.app (op ⊤)).hom))

/-- Every original E coefficient is fixed on every actual annular chart. -/
structure FieldMap where
  map : E.field →+* (globalRings p).obj (op Q.curve)
  normalized : ∀ P : RationalPresentation p C S,
    (coefficientRestriction p C S φ O g A Q P).comp map = chartScalars p C F S P

def curveObject (H : FieldMap p C F S φ O g A Q) : ESpace p E.field :=
  CostructuredArrow.mk (Y := Q.curve) (CommRingCat.ofHom H.map).op

end MathlibExt.AlgebraicGeometry.RelativeFFFieldCoefficients
