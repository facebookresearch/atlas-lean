/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.Algebra.Homology.FirstQuadrantCanonicalAbutmentCurrentImageNaturality

/-!
# Naturality of the canonical-abutment previous image

The generic complete-stage homology image map at the preceding filtration
index is the unified predecessor map, including in column zero.  The
canonical previous relative-homology image comparison is consequently
natural under bicomplex morphisms.

This file does not assemble the final canonical-abutment associated-graded
square.
-/

@[expose] public section

open CategoryTheory Limits ComposableArrows

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- At the first-page lower index, the generic complete-stage image map is
the unified predecessor total-homology filtration map. -/
@[simp]
theorem horizontalCompleteHomologyImageMapOfBicomplex_eq_previous
    (f : K ⟶ L) (p q : ℕ) :
    horizontalCompleteHomologyImageMapOfBicomplex f (p + q)
        (horizontalFirstPageLowerIndex p) =
      horizontalPrevTotalHomologyFiltrationMapOfBicomplex f p q := by
  let lower : EInt := horizontalFirstPageLowerIndex p
  let upper : EInt := horizontalFirstPageUpperIndex p
  let stepK := horizontalTotalHomologyFiltrationStepMap K p q
  let stepL := horizontalTotalHomologyFiltrationStepMap L p q
  let current :=
    horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex f p q
  let previous := horizontalPrevTotalHomologyFiltrationMapOfBicomplex f p q
  let totalMap := HomologicalComplex.homologyMap
    (total.map f (ComplexShape.down ℕ)) (p + q)
  have hcurrent :=
    horizontalCompleteHomologyImageMapOfBicomplex_ι f (p + q) upper
  rw [horizontalCompleteHomologyImageMapOfBicomplex_eq_current] at hcurrent
  have hstepK := MonoOver.w
    ((horizontalTotalHomologyFiltration K (p + q)).toMonoOver.map
      (homOfLE (horizontalTotalHomologyPrevIndex_le p)))
  change stepK ≫
      image.ι (horizontalCompleteHomologyToTotal K (p + q) upper) =
    image.ι (horizontalCompleteHomologyToTotal K (p + q) lower) at hstepK
  have hstepL := MonoOver.w
    ((horizontalTotalHomologyFiltration L (p + q)).toMonoOver.map
      (homOfLE (horizontalTotalHomologyPrevIndex_le p)))
  change stepL ≫
      image.ι (horizontalCompleteHomologyToTotal L (p + q) upper) =
    image.ι (horizontalCompleteHomologyToTotal L (p + q) lower) at hstepL
  change horizontalCompleteHomologyImageMapOfBicomplex f (p + q) lower =
    previous
  apply (cancel_mono
    (image.ι (horizontalCompleteHomologyToTotal L (p + q) lower))).1
  rw [horizontalCompleteHomologyImageMapOfBicomplex_ι]
  symm
  calc
    previous ≫
          image.ι (horizontalCompleteHomologyToTotal L (p + q) lower) =
        previous ≫
          (stepL ≫ image.ι
            (horizontalCompleteHomologyToTotal L (p + q) upper)) := by
      rw [hstepL]
    _ = (previous ≫ stepL) ≫
        image.ι (horizontalCompleteHomologyToTotal L (p + q) upper) := by
      simp only [Category.assoc]
    _ = (stepK ≫ current) ≫
        image.ι (horizontalCompleteHomologyToTotal L (p + q) upper) := by
      rw [horizontalTotalHomologyFiltrationStepMap_naturality]
    _ = stepK ≫
        (current ≫ image.ι
          (horizontalCompleteHomologyToTotal L (p + q) upper)) :=
      Category.assoc _ _ _
    _ = stepK ≫
        (image.ι (horizontalCompleteHomologyToTotal K (p + q) upper) ≫
          totalMap) := by
      rw [hcurrent]
    _ = (stepK ≫
          image.ι (horizontalCompleteHomologyToTotal K (p + q) upper)) ≫
        totalMap := (Category.assoc _ _ _).symm
    _ = image.ι
          (horizontalCompleteHomologyToTotal K (p + q) lower) ≫
        totalMap := by
      rw [hstepK]

/-- The relative-homology square for the previous canonical-abutment image
induced by a bicomplex morphism. -/
noncomputable def horizontalCanonicalAbutmentPreviousHomologySquareOfBicomplex
    (f : K ⟶ L) (p q : ℕ) :
    Arrow.mk (horizontalCanonicalAbutmentPreviousHomologyMap K p q ≫
      horizontalCanonicalAbutmentToUpperHomologyMap K p q) ⟶
      Arrow.mk (horizontalCanonicalAbutmentPreviousHomologyMap L p q ≫
        horizontalCanonicalAbutmentToUpperHomologyMap L p q) := by
  let φ := horizontalCompleteFiltrationSpectralObjectMap f
  let n : ℤ := -((p + q : ℕ) : ℤ)
  let d := twoδ₂Toδ₁
    (horizontalCanonicalAbutmentLowerMap p)
    (homOfLE ((horizontalFirstPageIndex_le p).trans
      (horizontalAbutmentIndices_le p q).2))
    (horizontalCanonicalAbutmentTotalMap p q)
    (Subsingleton.elim _ _)
  refine Arrow.homMk
    ((φ.hom n).app (mk₁ (horizontalCanonicalAbutmentLowerMap p)))
    ((φ.hom n).app (mk₁ (horizontalCanonicalAbutmentTotalMap p q))) ?_
  rw [horizontalCanonicalAbutmentPrevious_comp_toUpper K p q,
    horizontalCanonicalAbutmentPrevious_comp_toUpper L p q]
  exact ((φ.hom n).naturality d).symm

/-- The map between previous canonical-abutment images induced by a
bicomplex morphism. -/
noncomputable def horizontalCanonicalAbutmentPreviousImageMapOfBicomplex
    (f : K ⟶ L) (p q : ℕ) :
    image (horizontalCanonicalAbutmentPreviousHomologyMap K p q ≫
        horizontalCanonicalAbutmentToUpperHomologyMap K p q) ⟶
      image (horizontalCanonicalAbutmentPreviousHomologyMap L p q ≫
        horizontalCanonicalAbutmentToUpperHomologyMap L p q) :=
  image.map
    (horizontalCanonicalAbutmentPreviousHomologySquareOfBicomplex f p q)

/-- The previous canonical-abutment image map commutes with the canonical
inclusions. -/
@[reassoc (attr := simp)]
theorem horizontalCanonicalAbutmentPreviousImageMapOfBicomplex_ι
    (f : K ⟶ L) (p q : ℕ) :
    horizontalCanonicalAbutmentPreviousImageMapOfBicomplex f p q ≫
        image.ι (horizontalCanonicalAbutmentPreviousHomologyMap L p q ≫
          horizontalCanonicalAbutmentToUpperHomologyMap L p q) =
      image.ι (horizontalCanonicalAbutmentPreviousHomologyMap K p q ≫
          horizontalCanonicalAbutmentToUpperHomologyMap K p q) ≫
        ((horizontalCompleteFiltrationSpectralObjectMap f).hom
          (-((p + q : ℕ) : ℤ))).app
            (mk₁ (horizontalCanonicalAbutmentTotalMap p q)) :=
  image.map_ι
    (horizontalCanonicalAbutmentPreviousHomologySquareOfBicomplex f p q)

/-- The comparison from the previous canonical-abutment image to the
previous total-homology filtration stage is natural in the bicomplex. -/
theorem horizontalCanonicalAbutmentPreviousImageIso_naturality_of_bicomplex
    (f : K ⟶ L) (p q : ℕ) :
    horizontalCanonicalAbutmentPreviousImageMapOfBicomplex f p q ≫
        (horizontalCanonicalAbutmentPreviousImageIso L p q).hom =
      (horizontalCanonicalAbutmentPreviousImageIso K p q).hom ≫
        horizontalPrevTotalHomologyFiltrationMapOfBicomplex f p q := by
  let sourceSquare :=
    horizontalCanonicalAbutmentPreviousHomologySquareOfBicomplex f p q
  let targetSquare :=
    horizontalCompleteHomologyToTotalSquareOfBicomplex f (p + q)
      (horizontalFirstPageLowerIndex p)
  let eK := horizontalCanonicalAbutmentPreviousArrowIso K p q
  let eL := horizontalCanonicalAbutmentPreviousArrowIso L p q
  have hArrow : sourceSquare ≫ eL.hom = eK.hom ≫ targetSquare := by
    apply Arrow.hom_ext
    · change
        ((horizontalCompleteFiltrationSpectralObjectMap f).hom
            (-((p + q : ℕ) : ℤ))).app
              (mk₁ (horizontalCanonicalAbutmentLowerMap p)) ≫
            (horizontalBottomRelativeHomologyStageIso L
              (horizontalFirstPageLowerIndex p) (p + q)).hom =
          (horizontalBottomRelativeHomologyStageIso K
              (horizontalFirstPageLowerIndex p) (p + q)).hom ≫
            HomologicalComplex.homologyMap
              (horizontalCompleteFilteredTotalComplexMapOfBicomplex f
                (horizontalFirstPageLowerIndex p)) (p + q)
      have h :=
        horizontalBottomRelativeHomologyStageIso_naturality_of_bicomplex
          f (horizontalFirstPageLowerIndex p) (p + q)
      have hbottom :
          horizontalBottomToStageMap (horizontalFirstPageLowerIndex p) =
            horizontalCanonicalAbutmentLowerMap p :=
        Subsingleton.elim _ _
      rw [hbottom] at h
      simpa only [sourceSquare, targetSquare, eK, eL,
        horizontalCanonicalAbutmentPreviousHomologySquareOfBicomplex,
        horizontalCompleteHomologyToTotalSquareOfBicomplex,
        horizontalCanonicalAbutmentPreviousArrowIso,
        Arrow.comp_left, Arrow.homMk_left, Arrow.isoMk_hom_left] using h
    · change
        ((horizontalCompleteFiltrationSpectralObjectMap f).hom
            (-((p + q : ℕ) : ℤ))).app
              (mk₁ (horizontalCanonicalAbutmentTotalMap p q)) ≫
            (horizontalBottomRelativeHomologyToTotalIso L p q).hom =
          (horizontalBottomRelativeHomologyToTotalIso K p q).hom ≫
            HomologicalComplex.homologyMap
              (total.map f (ComplexShape.down ℕ)) (p + q)
      simpa only [sourceSquare, targetSquare, eK, eL,
        horizontalCanonicalAbutmentPreviousHomologySquareOfBicomplex,
        horizontalCompleteHomologyToTotalSquareOfBicomplex,
        horizontalCanonicalAbutmentPreviousArrowIso,
        Arrow.comp_right, Arrow.homMk_right, Arrow.isoMk_hom_right] using
        horizontalBottomRelativeHomologyToTotalIso_naturality_of_bicomplex
          f p q
  rw [← horizontalCompleteHomologyImageMapOfBicomplex_eq_previous f p q]
  change (Limits.im (C := C)).map sourceSquare ≫
      ((Limits.im (C := C)).mapIso eL).hom =
    ((Limits.im (C := C)).mapIso eK).hom ≫
      (Limits.im (C := C)).map targetSquare
  simpa only [Functor.map_comp, Functor.mapIso_hom] using
    congrArg (fun k => (Limits.im (C := C)).map k) hArrow

end HomologicalComplex₂

end
