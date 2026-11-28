/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua -/

module

public import MathlibExt.Algebra.Homology.FirstQuadrantConvergence
public import MathlibExt.Algebra.Homology.FirstQuadrantSecondPageNaturality
public import MathlibExt.Algebra.Homology.FirstQuadrantFirstPageHomologyTailNaturality
public import MathlibExt.Algebra.Homology.FirstQuadrantHomologyFilteredObjectFunctor
public import MathlibExtTest.Algebra.Homology.FirstQuadrantSecondPageFiltrationClients

/-!
# Nonzero abutment and natural filtered-homology clients

Use the integer doubling bicomplex and its already-constructed nonzero second-page term.
The actual stable-page comparison gives nonzero canonical abutment, image-quotient and
associated graded objects in bidegree (0,0). These outcomes use canonical isomorphisms and
the compiled second-page witness, with no separate convergence certificate assumed.

Tripling and its square give actual nonidentity coefficient maps. The first-page,
first-page-homology, second-page and finite filtered-homology comparisons commute with
those maps. Bottom-stage short exactness and its mapping-cone quasi-isomorphism are also
constructed for the same bicomplex.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex₂
open MathlibExtTest.Algebra.Homology.FirstQuadrantFirstPageFocusedClients
open MathlibExtTest.Algebra.Homology.FirstQuadrantFiltrationHomotopyBoundary
open MathlibExtTest.Algebra.Homology.FirstQuadrantSecondPageFiltrationClients

namespace MathlibExtTest.Algebra.Homology.FirstQuadrantConvergenceNaturalityClients

/-- The canonical abutment is nonzero by its actual stable-page comparison. -/
theorem canonical_abutment_nonzero :
    ¬ IsZero (horizontalFirstQuadrantCanonicalAbutmentTerm K 0 0) := by
  intro hz
  exact second_page_nonzero (IsZero.of_iso hz
    (horizontalStablePageCanonicalAbutmentIso K 2 (by decide) 0 0 (by decide) (by decide)))

/-- The canonical quotient of homology images is nonzero. -/
theorem image_quotient_nonzero :
    ¬ IsZero (horizontalCanonicalAbutmentImageQuotient K 0 0) := by
  intro hz
  exact canonical_abutment_nonzero (IsZero.of_iso hz
    (horizontalCanonicalAbutmentImageQuotientIso K 0 0))

/-- The degree-zero graded piece of total homology is nonzero. -/
theorem graded_piece_nonzero : ¬ IsZero (horizontalTotalHomologyGradedPiece K 0 0) := by
  intro hz
  exact second_page_nonzero (IsZero.of_iso hz
    (horizontalStablePageGradedIso K 2 (by decide) 0 0 (by decide) (by decide)))

example : ¬ IsZero (horizontalFirstQuadrantCanonicalAbutmentTerm K 0 0) :=
  canonical_abutment_nonzero

example : ¬ IsZero (horizontalCanonicalAbutmentImageQuotient K 0 0) :=
  image_quotient_nonzero

example : ¬ IsZero (horizontalTotalHomologyGradedPiece K 0 0) := graded_piece_nonzero

example : Nonempty (((horizontalFirstQuadrantSpectralSequence K).page 2).X (0, 0) ≅
    horizontalTotalHomologyGradedPiece K 0 0) :=
  ⟨horizontalStablePageGradedIso K 2 (by decide) 0 0 (by decide) (by decide)⟩

example : ((triple.f 1).f 0).hom (1 : ℤ) = (3 : ℤ) := rfl

example : (((triple ≫ triple).f 1).f 0).hom (1 : ℤ) = (9 : ℤ) := rfl

example : (horizontalPageMapOfBicomplex triple 1 (by decide)).f (0, 0) ≫
    (horizontalFirstPageCoherentVerticalHomologyIso K 0 0).hom =
      (horizontalFirstPageCoherentVerticalHomologyIso K 0 0).hom ≫
        HomologicalComplex.homologyMap (triple.f 0) 0 :=
  horizontalFirstPageCoherentVerticalHomologyIso_hom_naturality triple 0 0

example : (horizontalPageMapOfBicomplex triple 1 (by decide)).f (0, 0) ≫
    (horizontalFirstPageNormalizedVerticalHomologyIso K 0 0).hom =
      (horizontalFirstPageNormalizedVerticalHomologyIso K 0 0).hom ≫
        HomologicalComplex.homologyMap (triple.f 0) 0 :=
  horizontalFirstPageNormalizedVerticalHomologyIso_hom_naturality triple 0 0

example : HomologicalComplex.homologyMap
    (horizontalPageMapOfBicomplex triple 1 (le_refl 1)) (0, 0) ≫
      (horizontalFirstPageHomologyVerticalHorizontalHomologyIso K 0 0).hom =
        (horizontalFirstPageHomologyVerticalHorizontalHomologyIso K 0 0).hom ≫
          HomologicalComplex.homologyMap (verticalHomologyComplexMap triple 0) 0 :=
  horizontalFirstPageHomologyVerticalHorizontalHomologyIso_hom_naturality_of_bicomplex triple 0 0

example : HomologicalComplex.homologyMap
    (horizontalPageMapOfBicomplex triple 1 (le_refl 1)) (0, 0) ≫
      ((horizontalFirstQuadrantSpectralSequence K).iso 1 2 (0, 0)).hom =
        ((horizontalFirstQuadrantSpectralSequence K).iso 1 2 (0, 0)).hom ≫
          horizontalSecondPageMapOfBicomplex triple 0 0 :=
  horizontalPageMapOfBicomplex_successor_one_two triple 0 0

example : horizontalSecondPageMapOfBicomplex triple 0 0 ≫
    (horizontalSecondPageVerticalHorizontalHomologyIso K 0 0).hom =
      (horizontalSecondPageVerticalHorizontalHomologyIso K 0 0).hom ≫
        HomologicalComplex.homologyMap (verticalHomologyComplexMap triple 0) 0 :=
  horizontalSecondPageVerticalHorizontalHomologyIso_hom_naturality triple 0 0

example : ((horizontalFiniteTotalHomologyFiltrationDiagramFunctor 0).map triple).app 1 =
    horizontalFiniteHomologyImageMapOfBicomplex triple 0 1 :=
  horizontalFiniteTotalHomologyFiltrationDiagramFunctor_map_app 0 triple 1

example : ((horizontalFiniteTotalHomologyFiltrationDiagramFunctor 0).map triple).app 1 ≫
    (horizontalFiniteTotalHomologyFiltration K 0).ι.app 1 =
      (horizontalFiniteTotalHomologyFiltration K 0).ι.app 1 ≫
        HomologicalComplex.homologyMap (total.map triple (ComplexShape.down ℕ)) 0 :=
  horizontalFiniteTotalHomologyFiltrationDiagramFunctor_map_app_ι 0 triple 1

example : ((horizontalFiniteTotalHomologyFilteredObjectFunctor 0).map triple).hom =
    HomologicalComplex.homologyMap (total.map triple (ComplexShape.down ℕ)) 0 :=
  horizontalFiniteTotalHomologyFilteredObjectFunctor_map_hom 0 triple

example : ((horizontalFiniteTotalHomologyFilteredObjectFunctor 0).map triple).natTrans.app 1 =
    horizontalFiniteHomologyImageMapOfBicomplex triple 0 1 :=
  horizontalFiniteTotalHomologyFilteredObjectFunctor_map_natTrans_app 0 triple 1

example : (horizontalCanonicalAbutmentCokernelSequence K 0 0).Exact :=
  horizontalCanonicalAbutmentCokernelSequence_exact K 0 0

example : (horizontalBottomStageShortComplex K (0 : EInt)).ShortExact :=
  horizontalBottomStageShortComplex_shortExact K (0 : EInt)

example : QuasiIso (horizontalBottomMappingConeToStage K (0 : EInt)) :=
  horizontalBottomMappingConeToStage_quasiIso K (0 : EInt)

example : Nonempty
    (((horizontalCompleteFiltrationSpectralObject K).H (-((0 : ℕ) : ℤ))).obj
      (CategoryTheory.ComposableArrows.mk₁ (horizontalBottomToStageMap (0 : EInt))) ≅
        (horizontalCompleteFilteredTotalComplex K (0 : EInt)).homology 0) :=
  ⟨horizontalBottomRelativeHomologyStageIso K (0 : EInt) 0⟩

end MathlibExtTest.Algebra.Homology.FirstQuadrantConvergenceNaturalityClients
