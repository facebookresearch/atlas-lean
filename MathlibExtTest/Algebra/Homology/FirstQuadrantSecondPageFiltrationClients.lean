/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua -/

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFirstPageCoherentXNaturality
public import MathlibExt.Algebra.Homology.FirstQuadrantFirstPageRowNaturality
public import MathlibExt.Algebra.Homology.FirstQuadrantHomologyFiltrationNaturality
public import MathlibExt.Algebra.Homology.FirstQuadrantStablePage
public import MathlibExtTest.Algebra.Homology.FirstQuadrantFiltrationHomotopyBoundary
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# A nonzero second page and its coefficient and filtration maps

The integer doubling bicomplex has a nonzero second-page object in bidegree (0,0).
The proof uses the canonical second-page comparison, native zero-differential row homology,
and the fact that doubling the integers is not surjective; no page outcome is assumed.
Tripling and its square supply the actual nonidentity coefficient maps. The same example
checks normalized first-page rows, second-page composition, exhaustive homology filtration,
negative-cut vanishing and the concrete stable-page bounds.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex₂
open MathlibExtTest.Algebra.Homology.FirstQuadrantFirstPageFocusedClients
open MathlibExtTest.Algebra.Homology.FirstQuadrantFiltrationHomotopyBoundary

namespace MathlibExtTest.Algebra.Homology.FirstQuadrantSecondPageFiltrationClients

/-- The actual horizontal complex of degree-zero vertical row homology. -/
abbrev V := K.verticalHomologyComplex 0

/-- The row coefficient identification, earned from zero-differential homology data. -/
def rowHomologyIso : row.homology 0 ≅ Z :=
  (ShortComplex.HomologyData.ofZeros (row.sc 0) (by rfl) (by rfl)).left.homologyIso

lemma vertical_doubling : V.d 1 0 = 𝟙 (row.homology 0) + 𝟙 (row.homology 0) := by
  rw [verticalHomologyComplex_d]
  rw [show K.d 1 0 = double from ChainComplex.mk_d_1_0 _ _ _ _ _ _ _]
  change HomologicalComplex.homologyMap (𝟙 row + 𝟙 row) 0 = _
  exact (HomologicalComplex.homologyMap_add (𝟙 row) (𝟙 row) 0).trans
    (congrArg₂ (fun f g : row.homology 0 ⟶ row.homology 0 => f + g)
      (HomologicalComplex.homologyMap_id row 0) (HomologicalComplex.homologyMap_id row 0))

lemma vertical_zero : V.d 0 0 = 0 := V.shape 0 0 (by decide)

lemma vertical_not_surjective : ¬ Function.Surjective (V.d 1 0).hom := by
  intro hs
  obtain ⟨x, hx⟩ := hs (rowHomologyIso.inv.hom (1 : ℤ))
  have hv := congrArg (fun y => rowHomologyIso.hom.hom y) hx
  rw [vertical_doubling] at hv
  change rowHomologyIso.hom.hom (x + x) =
    rowHomologyIso.hom.hom (rowHomologyIso.inv.hom (1 : ℤ)) at hv
  have he : rowHomologyIso.hom.hom (rowHomologyIso.inv.hom (1 : ℤ)) = (1 : ℤ) := by
    have h := congrArg (fun f : Z ⟶ Z => f.hom (1 : ℤ)) rowHomologyIso.inv_hom_id
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
      LinearMap.id_apply] using h
  have hsum : (rowHomologyIso.hom.hom x : ℤ) + rowHomologyIso.hom.hom x = (1 : ℤ) :=
    (rowHomologyIso.hom.hom.map_add x x).symm.trans (hv.trans he)
  omega

lemma vertical_homology_nonzero : ¬ IsZero (V.homology 0) := by
  intro hz
  have hExact : V.ExactAt 0 := (V.exactAt_iff_isZero_homology 0).mpr hz
  have hShort : (V.sc' 1 0 0).Exact :=
    (V.exactAt_iff' (i := 1) (j := 0) (k := 0) rfl rfl).mp hExact
  have hElem := (ShortComplex.moduleCat_exact_iff (V.sc' 1 0 0)).mp hShort
  apply vertical_not_surjective
  intro z
  obtain ⟨x, hx⟩ := hElem z (by
    change (V.d 0 0).hom z = 0
    rw [vertical_zero]
    rfl)
  exact ⟨x, hx⟩

/-- The actual second-page term is nonzero, via its native iterated-homology comparison. -/
theorem second_page_nonzero :
    ¬ IsZero (((horizontalFirstQuadrantSpectralSequence K).page 2).X (0, 0)) := by
  intro hz
  exact vertical_homology_nonzero (IsZero.of_iso hz
    (horizontalSecondPageVerticalHorizontalHomologyIso K 0 0).symm)

example : ((triple.f 1).f 0).hom (1 : ℤ) = (3 : ℤ) := rfl

example : (((triple ≫ triple).f 1).f 0).hom (1 : ℤ) = (9 : ℤ) := rfl

example : (horizontalFirstPageNormalizedVerticalHomologyIso K 1 0).hom =
    (((1 : ℤ) * ((0 : ℤ) + 1)).negOnePow) •
      (horizontalFirstPageCoherentVerticalHomologyIso K 1 0).hom :=
  horizontalFirstPageNormalizedVerticalHomologyIso_hom K 1 0

example : ((horizontalFirstQuadrantSpectralSequence K).page 1).d (1, 0) (0, 0) ≫
    (horizontalFirstPageNormalizedVerticalHomologyIso K 0 0).hom =
      (horizontalFirstPageNormalizedVerticalHomologyIso K 1 0).hom ≫
        horizontalFirstPageHorizontalHomologyMap K 0 0 :=
  horizontalFirstPage_d_normalizedVerticalHomology K 0 0

example : (horizontalFirstPageRowMapOfBicomplex triple 0).f 1 =
    (horizontalPageMapOfBicomplex triple 1 (le_refl 1)).f (1, 0) :=
  horizontalFirstPageRowMapOfBicomplex_f triple 1 0

example : horizontalFirstPageRowMapOfBicomplex (triple ≫ triple) 0 =
    horizontalFirstPageRowMapOfBicomplex triple 0 ≫
      horizontalFirstPageRowMapOfBicomplex triple 0 :=
  horizontalFirstPageRowMapOfBicomplex_comp triple triple 0

example : horizontalSecondPageMapOfBicomplex (triple ≫ triple) 0 0 =
    horizontalSecondPageMapOfBicomplex triple 0 0 ≫
      horizontalSecondPageMapOfBicomplex triple 0 0 :=
  horizontalSecondPageMapOfBicomplex_comp triple triple 0 0

example : horizontalPageMapOfBicomplex (triple ≫ triple) 2 (by decide) =
    horizontalPageMapOfBicomplex triple 2 (by decide) ≫
      horizontalPageMapOfBicomplex triple 2 (by decide) :=
  horizontalPageMapOfBicomplex_comp triple triple 2 (by decide)

example : horizontalSecondPageMapOfBicomplex triple 0 0 =
    (horizontalSecondPageXIso K 0 0).hom ≫ horizontalSecondPageEMapOfBicomplex triple 0 0 ≫
      (horizontalSecondPageXIso K 0 0).inv :=
  horizontalSecondPageMapOfBicomplex_eq triple 0 0

example : Nonempty (((horizontalFirstQuadrantSpectralSequence K).page 2).X (0, 0) ≅
    (K.verticalHomologyComplex 0).homology 0) :=
  ⟨horizontalSecondPageVerticalHorizontalHomologyIso K 0 0⟩

example : ¬ IsZero (((horizontalFirstQuadrantSpectralSequence K).page 2).X (0, 0)) :=
  second_page_nonzero

example : IsIso ((horizontalTotalHomologyFiltration K 0).ι.app ((0 : ℤ) : EInt)) :=
  horizontalTotalHomologyFiltration_exhaustive K 0

example : IsZero ((horizontalTotalHomologyFiltration K 0).obj ((-1 : ℤ) : EInt)) :=
  horizontalTotalHomologyFiltration_obj_isZero_of_neg K (-1) (by decide) 0

example : (ShortComplex.cokernelSequence
    (horizontalTotalHomologyFiltrationStepMap K 0 0)).ShortExact :=
  horizontalTotalHomologyFiltrationStepShortExact K 0 0

example : (horizontalCompleteFiniteHomologyFiltrationDiagramIso K 0).hom.app 0 ≫
    (horizontalFiniteTotalHomologyFiltration K 0).ι.app 0 =
      (horizontalTotalHomologyFiltration K 0).ι.app ((0 : ℤ) : EInt) :=
  horizontalCompleteFiniteHomologyFiltrationDiagramIso_hom_ι K 0 0

example : horizontalStablePageIndex 0 0 = (2 : ℤ) := by decide

example : horizontalStablePageIndex 2 3 = (5 : ℤ) := by decide

example : Nonempty (((horizontalFirstQuadrantSpectralSequence K).page
    (horizontalStablePageIndex 0 0)).X (0, 0) ≅ horizontalFirstQuadrantAbutmentTerm K 0 0) :=
  ⟨horizontalStablePageAbutmentIsoAtIndex K 0 0⟩

end MathlibExtTest.Algebra.Homology.FirstQuadrantSecondPageFiltrationClients
