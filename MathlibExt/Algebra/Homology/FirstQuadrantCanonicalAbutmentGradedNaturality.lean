/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.Algebra.Homology.FirstQuadrantCanonicalAbutmentImageQuotientNaturality
public import
  MathlibExt.Algebra.Homology.FirstQuadrantCanonicalAbutmentPreviousImageNaturality

/-!
# Naturality of the canonical-abutment associated-graded comparison

The previous and current canonical-abutment image maps form a square between
the nested-image inclusions.  Passing to cokernels identifies the canonical
nested-image quotient map with the landed associated-graded map.  Combining
this square with canonical-abutment/image-quotient naturality gives the final
canonical-abutment/associated-graded naturality theorem.

No stable-page comparison is composed in this file.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- The square between the canonical nested-image inclusions induced by a
bicomplex morphism. -/
noncomputable def horizontalCanonicalAbutmentImageCompSquareOfBicomplex
    (f : K ⟶ L) (p q : ℕ) :
    Arrow.mk (CategoryTheory.imageCompMap
      (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
      (horizontalCanonicalAbutmentToUpperHomologyMap K p q)) ⟶
      Arrow.mk (CategoryTheory.imageCompMap
        (horizontalCanonicalAbutmentPreviousHomologyMap L p q)
        (horizontalCanonicalAbutmentToUpperHomologyMap L p q)) :=
  Arrow.homMk
    (horizontalCanonicalAbutmentPreviousImageMapOfBicomplex f p q)
    (horizontalCanonicalAbutmentCurrentImageMapOfBicomplex f p q)
    (by
      apply (cancel_mono (image.ι
        (horizontalCanonicalAbutmentToUpperHomologyMap L p q))).1
      calc
        (horizontalCanonicalAbutmentPreviousImageMapOfBicomplex f p q ≫
            CategoryTheory.imageCompMap
              (horizontalCanonicalAbutmentPreviousHomologyMap L p q)
              (horizontalCanonicalAbutmentToUpperHomologyMap L p q)) ≫
              image.ι (horizontalCanonicalAbutmentToUpperHomologyMap L p q) =
          horizontalCanonicalAbutmentPreviousImageMapOfBicomplex f p q ≫
            (CategoryTheory.imageCompMap
              (horizontalCanonicalAbutmentPreviousHomologyMap L p q)
              (horizontalCanonicalAbutmentToUpperHomologyMap L p q) ≫
                image.ι
                  (horizontalCanonicalAbutmentToUpperHomologyMap L p q)) :=
            Category.assoc _ _ _
        _ = horizontalCanonicalAbutmentPreviousImageMapOfBicomplex f p q ≫
            image.ι (horizontalCanonicalAbutmentPreviousHomologyMap L p q ≫
              horizontalCanonicalAbutmentToUpperHomologyMap L p q) := by
          rw [CategoryTheory.imageCompMap_ι]
        _ = image.ι
              (horizontalCanonicalAbutmentPreviousHomologyMap K p q ≫
                horizontalCanonicalAbutmentToUpperHomologyMap K p q) ≫
            ((horizontalCompleteFiltrationSpectralObjectMap f).hom
              (-((p + q : ℕ) : ℤ))).app
                (ComposableArrows.mk₁
                  (horizontalCanonicalAbutmentTotalMap p q)) := by
          rw [horizontalCanonicalAbutmentPreviousImageMapOfBicomplex_ι]
        _ = (CategoryTheory.imageCompMap
              (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
              (horizontalCanonicalAbutmentToUpperHomologyMap K p q) ≫
                image.ι
                  (horizontalCanonicalAbutmentToUpperHomologyMap K p q)) ≫
            ((horizontalCompleteFiltrationSpectralObjectMap f).hom
              (-((p + q : ℕ) : ℤ))).app
                (ComposableArrows.mk₁
                  (horizontalCanonicalAbutmentTotalMap p q)) := by
          rw [CategoryTheory.imageCompMap_ι]
        _ = CategoryTheory.imageCompMap
              (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
              (horizontalCanonicalAbutmentToUpperHomologyMap K p q) ≫
            (image.ι (horizontalCanonicalAbutmentToUpperHomologyMap K p q) ≫
              ((horizontalCompleteFiltrationSpectralObjectMap f).hom
                (-((p + q : ℕ) : ℤ))).app
                  (ComposableArrows.mk₁
                    (horizontalCanonicalAbutmentTotalMap p q))) :=
          Category.assoc _ _ _
        _ = CategoryTheory.imageCompMap
              (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
              (horizontalCanonicalAbutmentToUpperHomologyMap K p q) ≫
            (horizontalCanonicalAbutmentCurrentImageMapOfBicomplex f p q ≫
              image.ι
                (horizontalCanonicalAbutmentToUpperHomologyMap L p q)) := by
          rw [horizontalCanonicalAbutmentCurrentImageMapOfBicomplex_ι]
        _ = (CategoryTheory.imageCompMap
              (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
              (horizontalCanonicalAbutmentToUpperHomologyMap K p q) ≫
            horizontalCanonicalAbutmentCurrentImageMapOfBicomplex f p q) ≫
              image.ι
                (horizontalCanonicalAbutmentToUpperHomologyMap L p q) :=
          (Category.assoc _ _ _).symm)

/-- The specialized nested-image quotient map is the cokernel-functor map
of the canonical nested-image square. -/
@[simp]
theorem horizontalCanonicalAbutmentImageQuotientMapOfBicomplex_eq_coker_map
    (f : K ⟶ L) (p q : ℕ) :
    horizontalCanonicalAbutmentImageQuotientMapOfBicomplex f p q =
      (Limits.coker C).map
        (horizontalCanonicalAbutmentImageCompSquareOfBicomplex f p q) := by
  let sq := horizontalCanonicalAbutmentImageCompSquareOfBicomplex f p q
  apply (cancel_epi (cokernel.π (CategoryTheory.imageCompMap
    (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
    (horizontalCanonicalAbutmentToUpperHomologyMap K p q)))).1
  rw [horizontalCanonicalAbutmentImageQuotientMapOfBicomplex_π]
  exact (Limits.coker.π C).naturality sq

/-- The canonical nested-image quotient/associated-graded comparison is
natural under bicomplex morphisms. -/
theorem horizontalCanonicalAbutmentImageQuotientGradedIso_naturality
    (f : K ⟶ L) (p q : ℕ) :
    horizontalCanonicalAbutmentImageQuotientMapOfBicomplex f p q ≫
        (horizontalCanonicalAbutmentImageQuotientGradedIso L p q).hom =
      (horizontalCanonicalAbutmentImageQuotientGradedIso K p q).hom ≫
        horizontalTotalHomologyGradedPieceMapOfBicomplex f p q := by
  let sourceSquare :=
    horizontalCanonicalAbutmentImageCompSquareOfBicomplex f p q
  let targetSquare :=
    horizontalTotalHomologyFiltrationStepSquareOfBicomplex f p q
  let eK : Arrow.mk (CategoryTheory.imageCompMap
        (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
        (horizontalCanonicalAbutmentToUpperHomologyMap K p q)) ≅
      Arrow.mk (horizontalTotalHomologyFiltrationStepMap K p q) :=
    Arrow.isoMk'
      (CategoryTheory.imageCompMap
        (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
        (horizontalCanonicalAbutmentToUpperHomologyMap K p q))
      (horizontalTotalHomologyFiltrationStepMap K p q)
      (horizontalCanonicalAbutmentPreviousImageIso K p q)
      (horizontalCanonicalAbutmentCurrentImageIso K p q)
      (horizontalCanonicalAbutmentImageSquare K p q).symm
  let eL : Arrow.mk (CategoryTheory.imageCompMap
        (horizontalCanonicalAbutmentPreviousHomologyMap L p q)
        (horizontalCanonicalAbutmentToUpperHomologyMap L p q)) ≅
      Arrow.mk (horizontalTotalHomologyFiltrationStepMap L p q) :=
    Arrow.isoMk'
      (CategoryTheory.imageCompMap
        (horizontalCanonicalAbutmentPreviousHomologyMap L p q)
        (horizontalCanonicalAbutmentToUpperHomologyMap L p q))
      (horizontalTotalHomologyFiltrationStepMap L p q)
      (horizontalCanonicalAbutmentPreviousImageIso L p q)
      (horizontalCanonicalAbutmentCurrentImageIso L p q)
      (horizontalCanonicalAbutmentImageSquare L p q).symm
  have hArrow : sourceSquare ≫ eL.hom = eK.hom ≫ targetSquare := by
    apply Arrow.hom_ext
    · exact horizontalCanonicalAbutmentPreviousImageIso_naturality_of_bicomplex
        f p q
    · exact horizontalCanonicalAbutmentCurrentImageIso_naturality_of_bicomplex
        f p q
  rw [horizontalCanonicalAbutmentImageQuotientMapOfBicomplex_eq_coker_map]
  change (Limits.coker C).map sourceSquare ≫
      ((Limits.coker C).mapIso eL).hom =
    ((Limits.coker C).mapIso eK).hom ≫
      (Limits.coker C).map targetSquare
  simpa only [Functor.map_comp, Functor.mapIso_hom] using
    congrArg (fun k => (Limits.coker C).map k) hArrow

/-- The canonical-abutment/associated-graded comparison is natural under
bicomplex morphisms. -/
theorem horizontalCanonicalAbutmentGradedIso_naturality
    (f : K ⟶ L) (p q : ℕ) :
    horizontalCanonicalAbutmentMapOfBicomplex f p q ≫
        (horizontalCanonicalAbutmentGradedIso L p q).hom =
      (horizontalCanonicalAbutmentGradedIso K p q).hom ≫
        horizontalTotalHomologyGradedPieceMapOfBicomplex f p q := by
  have hImageQuotient :=
    horizontalCanonicalAbutmentImageQuotientIso_naturality f p q
  have hGraded :=
    horizontalCanonicalAbutmentImageQuotientGradedIso_naturality f p q
  dsimp only [horizontalCanonicalAbutmentGradedIso, Iso.trans_hom]
  calc
    horizontalCanonicalAbutmentMapOfBicomplex f p q ≫
          ((horizontalCanonicalAbutmentImageQuotientIso L p q).hom ≫
            (horizontalCanonicalAbutmentImageQuotientGradedIso L p q).hom) =
        (horizontalCanonicalAbutmentMapOfBicomplex f p q ≫
          (horizontalCanonicalAbutmentImageQuotientIso L p q).hom) ≫
            (horizontalCanonicalAbutmentImageQuotientGradedIso L p q).hom :=
      (Category.assoc _ _ _).symm
    _ = ((horizontalCanonicalAbutmentImageQuotientIso K p q).hom ≫
          horizontalCanonicalAbutmentImageQuotientMapOfBicomplex f p q) ≫
        (horizontalCanonicalAbutmentImageQuotientGradedIso L p q).hom := by
      rw [hImageQuotient]
    _ = (horizontalCanonicalAbutmentImageQuotientIso K p q).hom ≫
        (horizontalCanonicalAbutmentImageQuotientMapOfBicomplex f p q ≫
          (horizontalCanonicalAbutmentImageQuotientGradedIso L p q).hom) :=
      Category.assoc _ _ _
    _ = (horizontalCanonicalAbutmentImageQuotientIso K p q).hom ≫
        ((horizontalCanonicalAbutmentImageQuotientGradedIso K p q).hom ≫
          horizontalTotalHomologyGradedPieceMapOfBicomplex f p q) := by
      rw [hGraded]
    _ = ((horizontalCanonicalAbutmentImageQuotientIso K p q).hom ≫
          (horizontalCanonicalAbutmentImageQuotientGradedIso K p q).hom) ≫
        horizontalTotalHomologyGradedPieceMapOfBicomplex f p q :=
      (Category.assoc _ _ _).symm

end HomologicalComplex₂

end
