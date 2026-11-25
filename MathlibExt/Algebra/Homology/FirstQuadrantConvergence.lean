/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantBottomRelativeHomology

/-!
# Bounded convergence of a first-quadrant bicomplex spectral sequence

The finite abutment image quotient is transported, using natural
bottom-relative/stage-homology isomorphisms, to the filtration induced on
total homology.  Consequently every page
`r ≥ max (p+1) (q+2)` is canonically isomorphic to the `p`th associated
graded piece of `H_{p+q}(Tot K)`.

This is a filtered abutment theorem; it does not assert a splitting of total
homology into a direct sum of stable page terms.
-/

@[expose] public section

open CategoryTheory Limits
open CategoryTheory.ComposableArrows

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

/-- The finite upper abutment stage is one above total degree `p+q`. -/
theorem horizontalAbutmentUpperIndex_eq_succ (p q : ℕ) :
    horizontalAbutmentUpperIndex p q =
      ((((p + q : ℕ) : ℤ) + 1) : EInt) := by
  apply congrArg (@WithBotTop.coe ℤ)
  push_cast
  omega

/-- Homology of the finite upper abutment stage is total homology in degree
`p+q`. -/
noncomputable def horizontalAbutmentUpperHomologyToTotalIso (p q : ℕ) :
    (horizontalCompleteFilteredTotalComplex K
      (horizontalAbutmentUpperIndex p q)).homology (p + q) ≅
      (K.total (ComplexShape.down ℕ)).homology (p + q) := by
  have hIso : IsIso (horizontalCompleteHomologyToTotal K (p + q)
      (horizontalAbutmentUpperIndex p q)) := by
    rw [horizontalAbutmentUpperIndex_eq_succ]
    exact horizontalCompleteHomologyToTotal_isIso_succ K (p + q)
  let _ := hIso
  exact asIso (horizontalCompleteHomologyToTotal K (p + q)
    (horizontalAbutmentUpperIndex p q))

/-- Bottom-relative homology of the finite upper stage is total homology. -/
noncomputable def horizontalBottomRelativeHomologyToTotalIso (p q : ℕ) :
    ((horizontalCompleteFiltrationSpectralObject K).H
      (-((p + q : ℕ) : ℤ))).obj
        (mk₁ (horizontalCanonicalAbutmentTotalMap p q)) ≅
      (K.total (ComplexShape.down ℕ)).homology (p + q) :=
  horizontalBottomRelativeHomologyStageIso K
      (horizontalAbutmentUpperIndex p q) (p + q) ≪≫
    horizontalAbutmentUpperHomologyToTotalIso K p q

/-- Naturality of the bottom-relative-to-total comparison for every stage
below the finite upper stage. -/
theorem horizontalBottomRelativeHomologyToTotal_naturality
    (p q : ℕ) (i : EInt)
    (h : i ≤ horizontalAbutmentUpperIndex p q) :
    (horizontalBottomRelativeHomologyStageIso K i (p + q)).hom ≫
        horizontalCompleteHomologyToTotal K (p + q) i =
      ((horizontalCompleteFiltrationSpectralObject K).H
        (-((p + q : ℕ) : ℤ))).map
          (twoδ₂Toδ₁
            (horizontalBottomToStageMap i)
            (homOfLE h)
            (horizontalCanonicalAbutmentTotalMap p q)
            (Subsingleton.elim _ _)) ≫
        (horizontalBottomRelativeHomologyToTotalIso K p q).hom := by
  have hstage := horizontalBottomRelativeHomologyStageIso_naturality K h (p + q)
  have hstage' :
      ((horizontalCompleteFiltrationSpectralObject K).H
        (-((p : ℤ) + (q : ℤ)))).map
          (twoδ₂Toδ₁
            (horizontalBottomToStageMap i)
            (homOfLE h)
            (horizontalCanonicalAbutmentTotalMap p q)
            (Subsingleton.elim _ _)) ≫
        (horizontalBottomRelativeHomologyStageIso K
          (horizontalAbutmentUpperIndex p q) (p + q)).hom =
      (horizontalBottomRelativeHomologyStageIso K i (p + q)).hom ≫
        HomologicalComplex.homologyMap
          (horizontalCompleteFilteredTotalMap K h) (p + q) := by
    push_cast at hstage
    exact hstage
  have htotal := horizontalCompleteHomologyToTotal_naturality K (p + q) (homOfLE h)
  change HomologicalComplex.homologyMap
      (horizontalCompleteFilteredTotalMap K h) (p + q) ≫
        horizontalCompleteHomologyToTotal K (p + q)
          (horizontalAbutmentUpperIndex p q) =
      horizontalCompleteHomologyToTotal K (p + q) i at htotal
  rw [horizontalCompleteHomologyToTotal_eq K (p + q) i] at htotal ⊢
  rw [horizontalCompleteHomologyToTotal_eq K (p + q)
    (horizontalAbutmentUpperIndex p q)] at htotal
  dsimp [horizontalBottomRelativeHomologyToTotalIso,
    horizontalAbutmentUpperHomologyToTotalIso]
  rw [horizontalCompleteHomologyToTotal_eq K (p + q)
    (horizontalAbutmentUpperIndex p q)]
  rw [reassoc_of% hstage', htotal]

/-- Direct map from the preceding stage's bottom-relative homology to the
finite upper stage's bottom-relative homology. -/
noncomputable abbrev horizontalCanonicalAbutmentPreviousToUpperHomologyMap
    (p q : ℕ) :=
  ((horizontalCompleteFiltrationSpectralObject K).H
    (-((p + q : ℕ) : ℤ))).map
      (twoδ₂Toδ₁
        (horizontalCanonicalAbutmentLowerMap p)
        (homOfLE (show horizontalFirstPageLowerIndex p ≤
          horizontalAbutmentUpperIndex p q from
            (horizontalFirstPageIndex_le p).trans
              (horizontalAbutmentIndices_le p q).2))
        (horizontalCanonicalAbutmentTotalMap p q)
        (Subsingleton.elim _ _))

/-- The preceding-to-current and current-to-upper homology maps compose to
the direct preceding-to-upper map. -/
theorem horizontalCanonicalAbutmentPrevious_comp_toUpper (p q : ℕ) :
    horizontalCanonicalAbutmentPreviousHomologyMap K p q ≫
        horizontalCanonicalAbutmentToUpperHomologyMap K p q =
      horizontalCanonicalAbutmentPreviousToUpperHomologyMap K p q := by
  rw [← Functor.map_comp]
  apply Functor.congr_map
  apply Subsingleton.elim

/-- Arrow isomorphism from the current-stage relative-homology map to the
current-stage map into total homology. -/
noncomputable def horizontalCanonicalAbutmentCurrentArrowIso (p q : ℕ) :
    Arrow.mk (horizontalCanonicalAbutmentToUpperHomologyMap K p q) ≅
      Arrow.mk (horizontalCompleteHomologyToTotal K (p + q)
        (horizontalFirstPageUpperIndex p)) :=
  Arrow.isoMk'
    (horizontalCanonicalAbutmentToUpperHomologyMap K p q)
    (horizontalCompleteHomologyToTotal K (p + q)
      (horizontalFirstPageUpperIndex p))
    (horizontalBottomRelativeHomologyStageIso K
      (horizontalFirstPageUpperIndex p) (p + q))
    (horizontalBottomRelativeHomologyToTotalIso K p q)
    (horizontalBottomRelativeHomologyToTotal_naturality K p q
      (horizontalFirstPageUpperIndex p)
      (horizontalAbutmentIndices_le p q).2)

/-- Arrow isomorphism from the preceding-stage relative-homology composite
to the preceding-stage map into total homology. -/
noncomputable def horizontalCanonicalAbutmentPreviousArrowIso (p q : ℕ) :
    Arrow.mk (horizontalCanonicalAbutmentPreviousHomologyMap K p q ≫
      horizontalCanonicalAbutmentToUpperHomologyMap K p q) ≅
      Arrow.mk (horizontalCompleteHomologyToTotal K (p + q)
        (horizontalFirstPageLowerIndex p)) :=
  Arrow.isoMk'
    (horizontalCanonicalAbutmentPreviousHomologyMap K p q ≫
      horizontalCanonicalAbutmentToUpperHomologyMap K p q)
    (horizontalCompleteHomologyToTotal K (p + q)
      (horizontalFirstPageLowerIndex p))
    (horizontalBottomRelativeHomologyStageIso K
      (horizontalFirstPageLowerIndex p) (p + q))
    (horizontalBottomRelativeHomologyToTotalIso K p q) (by
      rw [horizontalCanonicalAbutmentPrevious_comp_toUpper]
      exact horizontalBottomRelativeHomologyToTotal_naturality K p q
        (horizontalFirstPageLowerIndex p)
        ((horizontalFirstPageIndex_le p).trans
          (horizontalAbutmentIndices_le p q).2))

/-- Transport of the current-stage image to the induced total-homology
filtration. -/
noncomputable def horizontalCanonicalAbutmentCurrentImageIso (p q : ℕ) :
    image (horizontalCanonicalAbutmentToUpperHomologyMap K p q) ≅
      (horizontalTotalHomologyFiltration K (p + q)).obj
        (horizontalFirstPageUpperIndex p) :=
  (Limits.im (C := C)).mapIso
    (horizontalCanonicalAbutmentCurrentArrowIso K p q)

/-- Transport of the preceding-stage image to the induced total-homology
filtration. -/
noncomputable def horizontalCanonicalAbutmentPreviousImageIso (p q : ℕ) :
    image (horizontalCanonicalAbutmentPreviousHomologyMap K p q ≫
      horizontalCanonicalAbutmentToUpperHomologyMap K p q) ≅
      (horizontalTotalHomologyFiltration K (p + q)).obj
        (horizontalFirstPageLowerIndex p) :=
  (Limits.im (C := C)).mapIso
    (horizontalCanonicalAbutmentPreviousArrowIso K p q)

/-- The transported endpoint isomorphisms commute with the inclusions of
nested images. -/
theorem horizontalCanonicalAbutmentImageSquare (p q : ℕ) :
    CategoryTheory.imageCompMap
        (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
        (horizontalCanonicalAbutmentToUpperHomologyMap K p q) ≫
      (horizontalCanonicalAbutmentCurrentImageIso K p q).hom =
    (horizontalCanonicalAbutmentPreviousImageIso K p q).hom ≫
      horizontalTotalHomologyFiltrationStepMap K p q := by
  let F := horizontalTotalHomologyFiltration K (p + q)
  let lower : EInt := horizontalFirstPageLowerIndex p
  let upper : EInt := horizontalFirstPageUpperIndex p
  have hcurrent := image.map_ι
    (horizontalCanonicalAbutmentCurrentArrowIso K p q).hom
  change (horizontalCanonicalAbutmentCurrentImageIso K p q).hom ≫
      image.ι (horizontalCompleteHomologyToTotal K (p + q) upper) =
    image.ι (horizontalCanonicalAbutmentToUpperHomologyMap K p q) ≫
      (horizontalBottomRelativeHomologyToTotalIso K p q).hom at hcurrent
  have hprevious := image.map_ι
    (horizontalCanonicalAbutmentPreviousArrowIso K p q).hom
  change (horizontalCanonicalAbutmentPreviousImageIso K p q).hom ≫
      image.ι (horizontalCompleteHomologyToTotal K (p + q) lower) =
    image.ι (horizontalCanonicalAbutmentPreviousHomologyMap K p q ≫
      horizontalCanonicalAbutmentToUpperHomologyMap K p q) ≫
      (horizontalBottomRelativeHomologyToTotalIso K p q).hom at hprevious
  have hstep := MonoOver.w (F.toMonoOver.map
    (homOfLE (horizontalTotalHomologyPrevIndex_le p)))
  change horizontalTotalHomologyFiltrationStepMap K p q ≫
      image.ι (horizontalCompleteHomologyToTotal K (p + q) upper) =
    image.ι (horizontalCompleteHomologyToTotal K (p + q) lower) at hstep
  apply (cancel_mono (image.ι
    (horizontalCompleteHomologyToTotal K (p + q) upper))).1
  calc
    _ = CategoryTheory.imageCompMap
          (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
          (horizontalCanonicalAbutmentToUpperHomologyMap K p q) ≫
        image.ι (horizontalCanonicalAbutmentToUpperHomologyMap K p q) ≫
        (horizontalBottomRelativeHomologyToTotalIso K p q).hom := by
      simpa only [Category.assoc] using
        CategoryTheory.imageCompMap
          (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
          (horizontalCanonicalAbutmentToUpperHomologyMap K p q) ≫= hcurrent
    _ = image.ι (horizontalCanonicalAbutmentPreviousHomologyMap K p q ≫
          horizontalCanonicalAbutmentToUpperHomologyMap K p q) ≫
        (horizontalBottomRelativeHomologyToTotalIso K p q).hom := by
      simpa only [Category.assoc] using
        CategoryTheory.imageCompMap_ι
          (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
          (horizontalCanonicalAbutmentToUpperHomologyMap K p q) =≫
            (horizontalBottomRelativeHomologyToTotalIso K p q).hom
    _ = (horizontalCanonicalAbutmentPreviousImageIso K p q).hom ≫
        image.ι (horizontalCompleteHomologyToTotal K (p + q) lower) :=
      hprevious.symm
    _ = _ :=
      (((horizontalCanonicalAbutmentPreviousImageIso K p q).hom ≫=
        hstep).symm).trans (Category.assoc _ _ _).symm

/-- The spectral-object nested-image quotient is the associated graded piece
of total homology. -/
noncomputable def horizontalCanonicalAbutmentImageQuotientGradedIso
    (p q : ℕ) :
    horizontalCanonicalAbutmentImageQuotient K p q ≅
      horizontalTotalHomologyGradedPiece K p q :=
  cokernel.mapIso
    (CategoryTheory.imageCompMap
      (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
      (horizontalCanonicalAbutmentToUpperHomologyMap K p q))
    (horizontalTotalHomologyFiltrationStepMap K p q)
    (horizontalCanonicalAbutmentPreviousImageIso K p q)
    (horizontalCanonicalAbutmentCurrentImageIso K p q)
    (horizontalCanonicalAbutmentImageSquare K p q)

/-- The canonical finite abutment term is the associated graded piece of
total homology. -/
noncomputable def horizontalCanonicalAbutmentGradedIso (p q : ℕ) :
    horizontalFirstQuadrantCanonicalAbutmentTerm K p q ≅
      horizontalTotalHomologyGradedPiece K p q :=
  horizontalCanonicalAbutmentImageQuotientIso K p q ≪≫
    horizontalCanonicalAbutmentImageQuotientGradedIso K p q

/-- Every sufficiently late page term is the corresponding associated graded
piece of total homology. -/
noncomputable def horizontalStablePageGradedIso
    (r : ℤ) (hr : 1 ≤ r) (p q : ℕ)
    (hlower : (p : ℤ) + 1 ≤ r) (hupper : (q : ℤ) + 2 ≤ r) :
    ((horizontalFirstQuadrantSpectralSequence K).page r).X (p, q) ≅
      horizontalTotalHomologyGradedPiece K p q :=
  horizontalStablePageCanonicalAbutmentIso K r hr p q hlower hupper ≪≫
    horizontalCanonicalAbutmentGradedIso K p q

/-- Stable-page/associated-graded comparison at the first page satisfying
both bidegree bounds. -/
noncomputable def horizontalStablePageGradedIsoAtIndex (p q : ℕ) :
    ((horizontalFirstQuadrantSpectralSequence K).page
      (horizontalStablePageIndex p q)).X (p, q) ≅
      horizontalTotalHomologyGradedPiece K p q :=
  horizontalStablePageGradedIso K (horizontalStablePageIndex p q)
    (horizontalStablePageIndex_one_le p q) p q
    (horizontalStablePageIndex_lower_bound p q)
    (horizontalStablePageIndex_upper_bound p q)

end HomologicalComplex₂
