/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua -/

module

public import MathlibExt.Algebra.Homology.FirstQuadrantCanonicalAbutmentCurrentImageNaturality
public import MathlibExtTest.Algebra.Homology.FirstQuadrantConvergenceNaturalityClients

/-!
# A nonzero graded-homology functor and its coefficient maps

The integer doubling bicomplex has a nonzero total-homology graded piece at (0,0).
The new graded-piece functor has that actual object. Tripling coefficients and its square
supply nonidentity maps whose composition is preserved by the graded functor.

The previous-stage map at column zero is the canonical zero map from the negative cut;
positive columns use their finite-stage comparisons. The same coefficient map preserves
the filtration-step square and the canonical current image under its abutment comparison.
No graded-object or image outcome is supplied as a hypothesis.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex₂
open MathlibExtTest.Algebra.Homology.FirstQuadrantFirstPageFocusedClients
open MathlibExtTest.Algebra.Homology.FirstQuadrantFiltrationHomotopyBoundary
open MathlibExtTest.Algebra.Homology.FirstQuadrantConvergenceNaturalityClients

namespace MathlibExtTest.Algebra.Homology.FirstQuadrantGradedFunctorClients

/-- The actual value of the graded-piece functor is nonzero. -/
theorem graded_functor_object_nonzero :
    ¬ IsZero ((horizontalTotalHomologyGradedPieceFunctor (C := ModuleCat ℤ) 0 0).obj K) := by
  change ¬ IsZero (horizontalTotalHomologyGradedPiece K 0 0)
  exact graded_piece_nonzero

example : ¬ IsZero
    ((horizontalTotalHomologyGradedPieceFunctor (C := ModuleCat ℤ) 0 0).obj K) :=
  graded_functor_object_nonzero

example : ((triple.f 1).f 0).hom (1 : ℤ) = (3 : ℤ) := rfl

example : (((triple ≫ triple).f 1).f 0).hom (1 : ℤ) = (9 : ℤ) := rfl

example : horizontalZeroPrevTotalHomologyFiltrationMapOfBicomplex triple 0 = 0 :=
  horizontalZeroPrevTotalHomologyFiltrationMapOfBicomplex_eq triple 0

example : horizontalTotalHomologyFiltrationStepMap K 0 0 ≫
    horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex triple 0 0 =
      horizontalZeroPrevTotalHomologyFiltrationMapOfBicomplex triple 0 ≫
        horizontalTotalHomologyFiltrationStepMap K 0 0 :=
  horizontalTotalHomologyFiltrationStepMap_naturality_zero triple 0

example : horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex
    (triple ≫ triple) 1 0 (by decide) =
      horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex triple 1 0 (by decide) ≫
        horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex triple 1 0 (by decide) :=
  horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex_comp triple triple 1 0 (by decide)

example : horizontalPrevTotalHomologyFiltrationMapOfBicomplex (triple ≫ triple) 0 0 =
    horizontalPrevTotalHomologyFiltrationMapOfBicomplex triple 0 0 ≫
      horizontalPrevTotalHomologyFiltrationMapOfBicomplex triple 0 0 :=
  horizontalPrevTotalHomologyFiltrationMapOfBicomplex_comp triple triple 0 0

example : horizontalTotalHomologyFiltrationStepMap K 1 0 ≫
    horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex triple 1 0 =
      horizontalPrevTotalHomologyFiltrationMapOfBicomplex triple 1 0 ≫
        horizontalTotalHomologyFiltrationStepMap K 1 0 :=
  horizontalTotalHomologyFiltrationStepMap_naturality triple 1 0

example : (horizontalTotalHomologyFiltrationStepSquareOfBicomplex triple 0 0).left =
    horizontalPrevTotalHomologyFiltrationMapOfBicomplex triple 0 0 :=
  horizontalTotalHomologyFiltrationStepSquareOfBicomplex_left triple 0 0

example : (horizontalTotalHomologyFiltrationStepSquareOfBicomplex triple 0 0).right =
    horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex triple 0 0 :=
  horizontalTotalHomologyFiltrationStepSquareOfBicomplex_right triple 0 0

example : (horizontalPrevTotalHomologyFiltrationFunctor (C := ModuleCat ℤ) 0 0).map triple =
    horizontalPrevTotalHomologyFiltrationMapOfBicomplex triple 0 0 :=
  horizontalPrevTotalHomologyFiltrationFunctor_map triple 0 0

example : (horizontalCurrentTotalHomologyFiltrationFunctor (C := ModuleCat ℤ) 0 0).map triple =
    horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex triple 0 0 :=
  horizontalCurrentTotalHomologyFiltrationFunctor_map triple 0 0

example : (horizontalTotalHomologyFiltrationStepNatTrans (C := ModuleCat ℤ) 0 0).app K =
    horizontalTotalHomologyFiltrationStepMap K 0 0 :=
  horizontalTotalHomologyFiltrationStepNatTrans_app K 0 0

example : (horizontalTotalHomologyFiltrationStepArrowFunctor (C := ModuleCat ℤ) 0 0).map triple =
    horizontalTotalHomologyFiltrationStepSquareOfBicomplex triple 0 0 :=
  horizontalTotalHomologyFiltrationStepArrowFunctor_map triple 0 0

example : (horizontalTotalHomologyGradedPieceFunctor (C := ModuleCat ℤ) 0 0).map triple =
    horizontalTotalHomologyGradedPieceMapOfBicomplex triple 0 0 :=
  horizontalTotalHomologyGradedPieceFunctor_map triple 0 0

example : horizontalTotalHomologyGradedPieceMapOfBicomplex (triple ≫ triple) 0 0 =
    horizontalTotalHomologyGradedPieceMapOfBicomplex triple 0 0 ≫
      horizontalTotalHomologyGradedPieceMapOfBicomplex triple 0 0 :=
  horizontalTotalHomologyGradedPieceMapOfBicomplex_comp triple triple 0 0

example : horizontalCompleteHomologyImageMapOfBicomplex triple 0 (horizontalFirstPageUpperIndex 0) =
    horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex triple 0 0 :=
  horizontalCompleteHomologyImageMapOfBicomplex_eq_current triple 0 0

example : horizontalCanonicalAbutmentCurrentImageMapOfBicomplex triple 0 0 ≫
    (horizontalCanonicalAbutmentCurrentImageIso K 0 0).hom =
      (horizontalCanonicalAbutmentCurrentImageIso K 0 0).hom ≫
        horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex triple 0 0 :=
  horizontalCanonicalAbutmentCurrentImageIso_naturality_of_bicomplex triple 0 0

example : (horizontalBottomStageShortComplexMapOfBicomplex triple (0 : EInt)).τ₂ =
    (horizontalCompleteFiltrationCochainDiagramNatTrans triple).app (0 : EInt) :=
  horizontalBottomStageShortComplexMapOfBicomplex_τ₂ triple (0 : EInt)

end MathlibExtTest.Algebra.Homology.FirstQuadrantGradedFunctorClients
