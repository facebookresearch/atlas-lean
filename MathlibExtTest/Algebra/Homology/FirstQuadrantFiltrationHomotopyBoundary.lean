/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua -/

module

public import MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltrationSpectralHomotopy
public import MathlibExt.Algebra.Homology.FirstQuadrantFirstPageColumnNaturality
public import MathlibExt.Algebra.Homology.FirstQuadrantFirstPageBoundaryComparison
public import MathlibExtTest.Algebra.Homology.FirstQuadrantFirstPageFocusedClients

/-!
# Coefficient naturality and boundary clients for a complete filtration

The two integer rows have horizontal doubling. Tripling both rows is a nonidentity
bicomplex endomorphism; its square is multiplication by nine. The direct-column,
untwisting and homology comparisons retain this actual coefficient map. The complete
filtration and its spectral object also accept the canonical reflexive homotopy of this
nonzero map, at finite, negative, bottom and top cuts.

The zero-column comparison and adjacent boundary formulas apply to this same doubling
bicomplex. Its horizontal cycle coordinate is -2 and its finite boundary coordinate is +2.
The homotopy examples check reflexive transport and do not supply a nonzero homotopy witness.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex₂
open MathlibExtTest.Algebra.Homology.FirstQuadrantFirstPageFocusedClients
open scoped ZeroObject

namespace MathlibExtTest.Algebra.Homology.FirstQuadrantFiltrationHomotopyBoundary

/-- Tripling every coefficient of the integer doubling bicomplex. -/
abbrev triple : K ⟶ K := 𝟙 K + 𝟙 K + 𝟙 K

/-- The canonical reflexive homotopy of the flipped coefficient map. -/
def coefficientHomotopy : _root_.Homotopy (flipMap triple) (flipMap triple) :=
  _root_.Homotopy.refl _

example : ((triple.f 1).f 0).hom (1 : ℤ) = (3 : ℤ) := rfl

example : (((triple ≫ triple).f 1).f 0).hom (1 : ℤ) = (9 : ℤ) := rfl

example : (horizontalDirectColumnCochainMap triple 1).f (-(1 : ℤ) - 0) =
    (horizontalDirectColumnCochainXIso K 1 0).hom ≫
      (triple.f 1).f 0 ≫ (horizontalDirectColumnCochainXIso K 1 0).inv :=
  horizontalDirectColumnCochainMap_f triple 1 0

example : horizontalDirectColumnCochainMap (triple ≫ triple) 1 =
    horizontalDirectColumnCochainMap triple 1 ≫
      horizontalDirectColumnCochainMap triple 1 :=
  horizontalDirectColumnCochainMap_comp triple triple 1

example : horizontalDirectColumnCochainMap triple 1 ≫
    (horizontalDirectColumnUntwistIso K 1).hom =
      (horizontalDirectColumnUntwistIso K 1).hom ≫
        HomologicalComplex.extendMap (triple.f 1)
          (ComplexShape.embeddingUpIntLE (-(1 : ℤ))) :=
  horizontalDirectColumnUntwistIso_hom_naturality triple 1

example : HomologicalComplex.homologyMap (horizontalDirectColumnCochainMap triple 1)
    (-(1 : ℤ) - 0) ≫ (horizontalDirectColumnHomologyIso K 1 0).hom =
      (horizontalDirectColumnHomologyIso K 1 0).hom ≫
        HomologicalComplex.homologyMap (triple.f 1) 0 :=
  horizontalDirectColumnHomologyIso_hom_naturality triple 1 0

example : horizontalFilteredTotalComplexMapOfBicomplex (triple ≫ triple) 1 =
    horizontalFilteredTotalComplexMapOfBicomplex triple 1 ≫
      horizontalFilteredTotalComplexMapOfBicomplex triple 1 :=
  horizontalFilteredTotalComplexMapOfBicomplex_comp triple triple 1

example : horizontalCompleteFilteredTotalComplexMapOfBicomplex
    (triple ≫ triple) (1 : EInt) =
      horizontalCompleteFilteredTotalComplexMapOfBicomplex triple (1 : EInt) ≫
        horizontalCompleteFilteredTotalComplexMapOfBicomplex triple (1 : EInt) :=
  horizontalCompleteFilteredTotalComplexMapOfBicomplex_comp triple triple (1 : EInt)

example : (horizontalFilteredTotalHomotopy coefficientHomotopy 1).hom 0 1 ≫
    (horizontalFilteredTotalComplexToTotal K 1).f 1 =
      (horizontalFilteredTotalComplexToTotal K 1).f 0 ≫
        (verticalTotalHomotopy coefficientHomotopy).hom 0 1 :=
  horizontalFilteredTotalHomotopy_toTotal coefficientHomotopy 1 0 1

example : (horizontalCompleteFilteredTotalHomotopy coefficientHomotopy ⊤).hom 0 1 =
    (verticalTotalHomotopy coefficientHomotopy).hom 0 1 :=
  horizontalCompleteFilteredTotalHomotopy_hom_top coefficientHomotopy 0 1

example : (horizontalCompleteFilteredTotalHomotopy coefficientHomotopy ⊥).hom 0 1 = 0 :=
  horizontalCompleteFilteredTotalHomotopy_hom_bot coefficientHomotopy 0 1

example : (horizontalCompleteFilteredTotalHomotopy coefficientHomotopy
    ((-1 : ℤ) : EInt)).hom 0 1 = 0 :=
  horizontalCompleteFilteredTotalHomotopy_hom_coe_of_neg
    coefficientHomotopy (-1) (by decide) 0 1

example : horizontalCompleteFiltrationTriangulatedSpectralObjectMap triple =
    horizontalCompleteFiltrationTriangulatedSpectralObjectMap triple :=
  horizontalCompleteFiltrationTriangulatedSpectralObjectMap_eq_of_homotopy coefficientHomotopy

example : horizontalCompleteFiltrationSpectralObjectMap triple =
    horizontalCompleteFiltrationSpectralObjectMap triple :=
  horizontalCompleteFiltrationSpectralObjectMap_eq_of_homotopy coefficientHomotopy

example : (horizontalCompleteFilteredTotalMonoOverUpperIso K 0).symm ≪≫
    horizontalCompleteFilteredTotalMonoOverMiddleIso K 0 ≪≫
      horizontalCompleteFilteredTotalMonoOverLowerSuccIso K 0 = Iso.refl _ :=
  horizontalCompleteFilteredTotalMonoOver_zero_middle_triangle K

example : (horizontalCompleteFiltrationCochainMonoUpperIso K 0).symm ≪≫
    horizontalFirstPageMiddleStageIso K 0 ≪≫
      horizontalCompleteFiltrationCochainMonoLowerSuccIso K 0 = Iso.refl _ :=
  horizontalFirstPageZeroMiddleMonoCochainTriangle K

example : horizontalFirstPageAdjacentBoundaryCycles K 0 0 =
    (((0 + 1 : ℕ) : ℤ).negOnePow) •
      (horizontalDirectColumnHorizontalCyclesMap K 0 0 ≫
        (horizontalDirectColumnCochain K 0).iCycles (-(0 : ℤ) - 0)) :=
  horizontalFirstPageAdjacentBoundaryCycles_eq_horizontal K 0 0

example : horizontalFirstPageAdjacentVerticalConnectingMap K 0 0 =
    (((0 + 1 : ℕ) : ℤ).negOnePow) • horizontalFirstPageHorizontalHomologyMap K 0 0 :=
  horizontalFirstPageAdjacentVerticalConnectingMap_eq_horizontal K 0 0

example : (sourceCycle ≫ horizontalDirectColumnHorizontalCyclesMap K 0 0 ≫
    (horizontalDirectColumnCochain K 0).iCycles 0 ≫
      (horizontalDirectColumnCochainXIso K 0 0).hom).hom (1 : ℤ) = (-2 : ℤ) := by
  rw [horizontal_cycle_coordinate, horizontal_component]
  change (1 : ℤ).negOnePow • ((1 : ℤ) + 1) = -2
  decide

example : (sourceCycle ≫ (horizontalDirectColumnCochain K 1).iCycles (-1) ≫
    (horizontalDirectColumnCochainXIso K 1 0).hom ≫
      horizontalFilteredTopInclusion K 1 0 ≫
        horizontalFilteredTotalD K 1 1 0 ≫ lowerRecovery).hom (1 : ℤ) = (2 : ℤ) := by
  rw [finite_boundary_coordinate, horizontal_component]
  rfl

end MathlibExtTest.Algebra.Homology.FirstQuadrantFiltrationHomotopyBoundary
