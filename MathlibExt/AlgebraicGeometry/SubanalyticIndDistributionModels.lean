/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SubanalyticConstructibleSheaves
public import MathlibExt.AlgebraicGeometry.ManifoldDistributionModels
public import MathlibExt.AlgebraicGeometry.OrdinaryOpenCutInclusions
public import MathlibExt.AlgebraicGeometry.IndSheafMonoidalModels
public import Mathlib.CategoryTheory.Linear.Basic

/-!
# Tempered distribution Ind objects fixed by all source subanalytic probes

Subanalytic objects are filtered colimits of the actual R-constructible
compact generators. The distribution object is characterized on every
relatively compact subanalytic open by the original global LF-family
quotient, with every restriction fixed by the original open-cut inclusion.
DK Proposition2.4.2 makes this a source characterization; it does not
equate Ind objects with ordinary stalk support.

Source: DK1311.2374v2 Sections2.4,5.1; native filtered cocones,
Yoneda, linear morphisms and quotients: Mathlib56a005, Apache2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.SubanalyticIndDistributionModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits TopologicalSpace
open CompactSupportIndSheaves SubanalyticConstructibleSheaves SubanalyticCoordinateModels
open OrdinarySheafOpenCuts OrdinaryOpenCutInclusions IndSheafMonoidalModels
open ManifoldDistributionModels

variable [∀ Z : TopCat.{0}, HasSheafify (Opens.grothendieckTopology Z) (ModuleCat.{0} ℂ)]
  (n : ℕ) (M : Type) [TopologicalSpace M] [ChartedSpace (ComplexCoordinates n) M]
  [CompactSheafSource ℂ (TopCat.of M)]

local instance subanalyticIndPreadditive : Preadditive (IndSheaf ℂ (TopCat.of M)) :=
  Abelian.toPreadditive

/-- A genuine filtered presentation in the original compact R-constructible sheaves. -/
structure SubanalyticIndPresentation (F : IndSheaf ℂ (TopCat.of M)) where
  index : Type
  [category : SmallCategory index]
  [filtered : IsFiltered index]
  diagram : index ⥤ CompactSubanalyticSheaf n M
  cocone : Cocone (diagram ⋙ compactSubanalyticToCompact n M ⋙ Ind.yoneda)
  colimit : IsColimit cocone
  comparison : cocone.pt ≅ F

structure RelativelyCompactSubanalyticOpen where
  openSet : Opens M
  compactClosure : IsCompact (closure (openSet : Set M))
  subanalytic : IsSubanalyticSubset n M openSet

def openCoefficient (U : RelativelyCompactSubanalyticOpen n M) :
    OrdinarySheaf ℂ (TopCat.of M) :=
  (ordinaryOpenCut ℂ (TopCat.of M) U.openSet).obj (coefficientUnitSheaf ℂ (TopCat.of M))

structure CompactOpenCoefficientSource : Prop where
  compact : ∀ U : RelativelyCompactSubanalyticOpen n M,
    IsCompactSupported ℂ (TopCat.of M) (openCoefficient n M U)

variable (C : CompactOpenCoefficientSource n M)

def openProbe (U : RelativelyCompactSubanalyticOpen n M) : IndSheaf ℂ (TopCat.of M) :=
  (compactToInd ℂ (TopCat.of M)).obj ⟨openCoefficient n M U, C.compact U⟩

def openProbeInclusion (U V : RelativelyCompactSubanalyticOpen n M)
    (h : V.openSet ≤ U.openSet) : openProbe n M C V ⟶ openProbe n M C U :=
  (compactToInd ℂ (TopCat.of M)).map (ObjectProperty.homMk
    (cutInclusion ℂ (TopCat.of M) (coefficientUnitSheaf ℂ (TopCat.of M)) h))

variable [Linear ℂ (IndSheaf ℂ (TopCat.of M))]
  (O : ChartOpenSource n M) (J : TestDensityTransferSource n M O)

/-- The normalized native quotient restriction, on all globally extendible sections. -/
structure TemperedRestrictionSource where
  restriction : ∀ (U V : Opens M), V ≤ U → TemperedSections n M O J U →ₗ[ℂ]
    TemperedSections n M O J V
  projection : ∀ (U V : Opens M) (h : V ≤ U) (T : GlobalDistribution n M O J),
    restriction U V h (temperedProjection n M O J U T) = temperedProjection n M O J V T

variable (R : TemperedRestrictionSource n M O J)

/-- Actual subanalytic distribution realization: every source value and map is retained. -/
structure TemperedIndDistributionSource where
  object : IndSheaf ℂ (TopCat.of M)
  subanalytic : SubanalyticIndPresentation n M object
  sections : ∀ U : RelativelyCompactSubanalyticOpen n M,
    (openProbe n M C U ⟶ object) ≃ₗ[ℂ] TemperedSections n M O J U.openSet
  restriction : ∀ (U V : RelativelyCompactSubanalyticOpen n M) (h : V.openSet ≤ U.openSet)
      (s : openProbe n M C U ⟶ object),
    sections V (openProbeInclusion n M C U V h ≫ s) =
      R.restriction U.openSet V.openSet h (sections U s)

end MathlibExt.AlgebraicGeometry.SubanalyticIndDistributionModels
