/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import MathlibExt.AlgebraicGeometry.HolomorphicDeRham
public import MathlibExt.Geometry.RationalHodgeStructures

/-!
# Betti--de Rham cohomology with a fixed geometric Hodge filtration

The rational complex resolves the actual constant rational sheaf. The
complex complex resolves the sectionwise characterized holomorphic de Rham
complex. Their comparison is normalized by the derived constant-unit square.
Both complexes consist of injective sheaves and vanish in negative degrees;
their actual global-section complexes therefore compute derived global
sections. The filtration uses geometric brutal cuts before global sections.

Sources: Deligne, *Théorie de Hodge II*, §§1.2, 2.2;
Peters--Steenbrink, *Mixed Hodge Structures*, Chapters 2 and 3.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.HodgeRealization

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AnalyticRealization ConstructibleComplexes HolomorphicDeRham
open MathlibExt.Geometry.RationalHodgeStructures

attribute [local instance] HasDerivedCategory.standard

/-- Global sections of the actual sheaf, evaluated at the maximal open. -/
def globalSections (k : Type) [Field k] (Z : TopCat.{0}) :
    CoefficientSheaf k Z ⥤ ModuleCat.{0} k :=
  (sheafSections (Opens.grothendieckTopology Z) (ModuleCat.{0} k)).obj (op ⊤)

instance globalSections_additive (k : Type) [Field k] (Z : TopCat.{0}) :
    (globalSections k Z).Additive where
  map_add := by intro A B f g; rfl

/-- An actual bounded-below complex of injective sheaves resolving the
specified geometric complex. These are toolbox data, not a replacement for
the geometric complex. -/
structure InjectiveCochainResolution (k : Type) [Field k] (Z : TopCat.{0})
    (K : CochainComplex (CoefficientSheaf k Z) ℤ) where
  complex : CochainComplex (CoefficientSheaf k Z) ℤ
  comparison : K ⟶ complex
  quasiIso : QuasiIso comparison
  injective : ∀ j, Injective (complex.X j)
  negative : ∀ j, j < 0 → IsZero (complex.X j)

/-- Resolutions and comparisons normalized by the actual constant-unit map.
The equality is in the derived category: no particular choice of a chain
lift of the unit is presumed to commute strictly. -/
structure BettiDeRhamResolution (X : AnalyticRealization.ComplexScheme) (d : ℕ)
    [AnalyticManifold X d] (D : HolomorphicDeRhamData X d) where
  rational : InjectiveCochainResolution ℚ (ComplexAnalytification.space X)
    (rationalUnitComplex X)
  complex : InjectiveCochainResolution ℂ (ComplexAnalytification.space X) D.complex
  comparison : rational.complex ⟶
    ((rationalRestriction X).mapHomologicalComplex (ComplexShape.up ℤ)).obj complex.complex
  unit_square :
    (DerivedCategory.Q (C := _)).map rational.comparison ≫
        (DerivedCategory.Q (C := _)).map comparison =
      (DerivedCategory.Q (C := _)).map D.rationalUnit ≫
        (DerivedCategory.Q (C := _)).map
          (((rationalRestriction X).mapHomologicalComplex (ComplexShape.up ℤ)).map
            complex.comparison)
  cut : ∀ p : ℤ, HodgeCut D p
  cutResolution : ∀ p : ℤ,
    InjectiveCochainResolution ℂ (ComplexAnalytification.space X) (cut p).complex
  cutMap : ∀ p : ℤ, (cutResolution p).complex ⟶ complex.complex
  cut_square : ∀ p : ℤ,
    (DerivedCategory.Q (C := _)).map (cutResolution p).comparison ≫
        (DerivedCategory.Q (C := _)).map (cutMap p) =
      (DerivedCategory.Q (C := _)).map (cut p).inclusion ≫
        (DerivedCategory.Q (C := _)).map complex.comparison

variable {X : AnalyticRealization.ComplexScheme} {d : ℕ} [AnalyticManifold X d]
  {D : HolomorphicDeRhamData X d} (R : BettiDeRhamResolution X d D)

/-- The actual rational global-section complex of the injective resolution. -/
def bettiComplex : CochainComplex (ModuleCat.{0} ℚ) ℤ :=
  ((globalSections ℚ (ComplexAnalytification.space X)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj R.rational.complex

/-- The actual complex global-section complex of the de Rham resolution. -/
def deRhamComplex : CochainComplex (ModuleCat.{0} ℂ) ℤ :=
  ((globalSections ℂ (ComplexAnalytification.space X)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj R.complex.complex

/-- Hodge filtration as images of actual maps from the geometric cut
resolutions. In particular, this is not a cut of `deRhamComplex R`. -/
def hodgeFiltration (n p : ℤ) : Submodule ℂ ((deRhamComplex R).homology n) :=
  LinearMap.range
    (HomologicalComplex.homologyMap
      (((globalSections ℂ (ComplexAnalytification.space X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (R.cutMap p)) n).hom

/-- The degreewise rational-to-complex map fixed by the unit square. -/
def comparisonInDegree (n : ℤ) :
    (bettiComplex R).X n →ₗ[ℤ] (deRhamComplex R).X n :=
  ((((globalSections ℚ (ComplexAnalytification.space X)).mapHomologicalComplex
    (ComplexShape.up ℤ)).map R.comparison).f n).hom.restrictScalars ℤ

/-- A pure realization on the actual rational Betti cohomology. The cycle
and quotient conditions pin its complexification map to the actual chain
comparison, and the filtration is the fixed geometric image filtration. -/
structure PureBettiHodgeData (n : ℤ) where
  complexification : RationalComplexification ((bettiComplex R).homology n)
  complexIso : complexification.complexSpace ≅ (deRhamComplex R).homology n
  cyclesMap : (bettiComplex R).cycles n →ₗ[ℤ] (deRhamComplex R).cycles n
  cycles_normalization : ∀ z,
    ((deRhamComplex R).iCycles n) (cyclesMap z) =
      comparisonInDegree R n (((bettiComplex R).iCycles n) z)
  cohomology_normalization : ∀ z,
    complexIso.hom
      (complexification.comparisonMap (((bettiComplex R).homologyπ n) z)) =
        ((deRhamComplex R).homologyπ n) (cyclesMap z)
  hodge : PureHodgeStructure complexification n
  filtration : ∀ p,
    hodge.F p = (hodgeFiltration R n p).comap complexIso.hom.hom

end MathlibExt.AlgebraicGeometry.HodgeRealization
