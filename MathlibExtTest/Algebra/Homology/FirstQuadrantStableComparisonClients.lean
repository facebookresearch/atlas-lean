/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua -/

module

public import MathlibExt.Algebra.Homology.FirstQuadrantSpectralComparison
public import MathlibExtTest.Algebra.Homology.FirstQuadrantGradedFunctorClients

/-!
# Natural stable-page comparisons on nonzero graded homology

The integer doubling bicomplex has nonzero graded homology in bidegree (0,0).
Coefficient tripling exercises the stable, canonical-abutment, cokernel and image-quotient
comparisons on this actual model. Negation is a genuine nonidentity bicomplex isomorphism;
its graded maps are earned by functoriality, and the general graded comparison criterion
then proves its total map is a quasi-isomorphism. No global comparison outcome is assumed.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex₂
open MathlibExtTest.Algebra.Homology.FirstQuadrantFirstPageFocusedClients
open MathlibExtTest.Algebra.Homology.FirstQuadrantFiltrationHomotopyBoundary
open MathlibExtTest.Algebra.Homology.FirstQuadrantGradedFunctorClients

namespace MathlibExtTest.Algebra.Homology.FirstQuadrantStableComparisonClients

/-- A concrete nonidentity coefficient isomorphism of the doubling bicomplex. -/
def negativeIso : K ≅ K where
  hom := -𝟙 K
  inv := -𝟙 K
  hom_inv_id := by simp
  inv_hom_id := by simp

/-- Negation induces isomorphisms on every actual total-homology graded piece. -/
lemma negative_graded_isIso (p q : ℕ) :
    IsIso (horizontalTotalHomologyGradedPieceMapOfBicomplex negativeIso.hom p q) := by
  let _ : IsIso negativeIso.hom := negativeIso.isIso_hom
  change IsIso ((horizontalTotalHomologyGradedPieceFunctor (C := ModuleCat ℤ) p q).map
    negativeIso.hom)
  infer_instance

example : ((negativeIso.hom.f 1).f 0).hom (1 : ℤ) = (-1 : ℤ) := rfl

example : negativeIso.hom ≠ 𝟙 K := by
  intro h
  have h1 := congrArg (fun f : K ⟶ K => ((f.f 1).f 0).hom (1 : ℤ)) h
  change (-1 : ℤ) = 1 at h1
  exact (by decide : (-1 : ℤ) ≠ 1) h1

example : QuasiIso (total.map negativeIso.hom (ComplexShape.down ℕ)) :=
  quasiIso_totalMap_of_isIso_horizontalGradedPieceMap_firstQuadrant negativeIso.hom
    negative_graded_isIso

example : IsIso (horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex
    negativeIso.hom 0 0) :=
  isIso_horizontalPositiveCurrent_of_isIso_gradedPieceMap negativeIso.hom
    negative_graded_isIso 0 0

example : ¬ IsZero
    ((horizontalTotalHomologyGradedPieceFunctor (C := ModuleCat ℤ) 0 0).obj K) :=
  graded_functor_object_nonzero

example : ((triple.f 1).f 0).hom (1 : ℤ) = (3 : ℤ) := rfl

example : (((triple ≫ triple).f 1).f 0).hom (1 : ℤ) = (9 : ℤ) := rfl

example : horizontalStablePageMapOfBicomplex triple 0 0 ≫
    (horizontalStablePageGradedIsoAtIndex K 0 0).hom =
      (horizontalStablePageGradedIsoAtIndex K 0 0).hom ≫
        horizontalTotalHomologyGradedPieceMapOfBicomplex triple 0 0 :=
  horizontalStablePageGradedIsoAtIndex_naturality triple 0 0

example : horizontalCanonicalAbutmentBiprodCokernelMapOfBicomplex triple 0 0 ≫
    (horizontalCanonicalAbutmentCokernelIso K 0 0).hom =
      (horizontalCanonicalAbutmentCokernelIso K 0 0).hom ≫
        horizontalCanonicalAbutmentMapOfBicomplex triple 0 0 :=
  horizontalCanonicalAbutmentCokernelIso_naturality triple 0 0

example : horizontalCanonicalAbutmentMapOfBicomplex triple 0 0 ≫
    (horizontalCanonicalAbutmentImageQuotientIso K 0 0).hom =
      (horizontalCanonicalAbutmentImageQuotientIso K 0 0).hom ≫
        horizontalCanonicalAbutmentImageQuotientMapOfBicomplex triple 0 0 :=
  horizontalCanonicalAbutmentImageQuotientIso_naturality triple 0 0

example : horizontalCanonicalAbutmentPreviousImageMapOfBicomplex triple 0 0 ≫
    (horizontalCanonicalAbutmentPreviousImageIso K 0 0).hom =
      (horizontalCanonicalAbutmentPreviousImageIso K 0 0).hom ≫
        horizontalPrevTotalHomologyFiltrationMapOfBicomplex triple 0 0 :=
  horizontalCanonicalAbutmentPreviousImageIso_naturality_of_bicomplex triple 0 0

example : horizontalCanonicalAbutmentImageQuotientMapOfBicomplex triple 0 0 ≫
    (horizontalCanonicalAbutmentImageQuotientGradedIso K 0 0).hom =
      (horizontalCanonicalAbutmentImageQuotientGradedIso K 0 0).hom ≫
        horizontalTotalHomologyGradedPieceMapOfBicomplex triple 0 0 :=
  horizontalCanonicalAbutmentImageQuotientGradedIso_naturality triple 0 0

example : horizontalCanonicalAbutmentMapOfBicomplex triple 0 0 ≫
    (horizontalCanonicalAbutmentGradedIso K 0 0).hom =
      (horizontalCanonicalAbutmentGradedIso K 0 0).hom ≫
        horizontalTotalHomologyGradedPieceMapOfBicomplex triple 0 0 :=
  horizontalCanonicalAbutmentGradedIso_naturality triple 0 0

example : horizontalCompleteHomologyImageMapOfBicomplex triple 0
    (horizontalFirstPageLowerIndex 0) =
      horizontalPrevTotalHomologyFiltrationMapOfBicomplex triple 0 0 :=
  horizontalCompleteHomologyImageMapOfBicomplex_eq_previous triple 0 0

example : (horizontalFiltrationStepShortComplexMapOfBicomplex triple 0 0).τ₁ =
    horizontalPrevTotalHomologyFiltrationMapOfBicomplex triple 0 0 :=
  horizontalFiltrationStepShortComplexMapOfBicomplex_τ₁ triple 0 0

example : (horizontalFiltrationStepShortComplexMapOfBicomplex triple 0 0).τ₂ =
    horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex triple 0 0 :=
  horizontalFiltrationStepShortComplexMapOfBicomplex_τ₂ triple 0 0

example : (horizontalFiltrationStepShortComplexMapOfBicomplex triple 0 0).τ₃ =
    horizontalTotalHomologyGradedPieceMapOfBicomplex triple 0 0 :=
  horizontalFiltrationStepShortComplexMapOfBicomplex_τ₃ triple 0 0

example : horizontalStablePageMapOfBicomplex triple 0 0 =
    (horizontalPageMapOfBicomplex triple (horizontalStablePageIndex 0 0)
      (horizontalStablePageIndex_one_le 0 0)).f (0, 0) :=
  horizontalStablePageMapOfBicomplex_eq_pageMap triple 0 0

end MathlibExtTest.Algebra.Homology.FirstQuadrantStableComparisonClients
