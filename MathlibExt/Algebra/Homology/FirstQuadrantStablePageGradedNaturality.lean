/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.Algebra.Homology.FirstQuadrantCanonicalAbutmentGradedNaturality

/-!
# Naturality of the stable-page associated-graded comparison

At the first page satisfying the two first-quadrant stability bounds, the
page map induced by a bicomplex morphism commutes with the canonical
identification of the stable term with the associated graded of total
homology.  The proof composes the reviewed stable-to-canonical and
canonical-to-graded squares.

The stable map is the fixed `pageXIso`-conjugated `EMap`; no successor-page or
full spectral-sequence morphism API is used.
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

/-- The stable-page/associated-graded comparison at the canonical stable
index is natural under bicomplex morphisms. -/
theorem horizontalStablePageGradedIsoAtIndex_naturality
    (f : K ⟶ L) (p q : ℕ) :
    horizontalStablePageMapOfBicomplex f p q ≫
        (horizontalStablePageGradedIsoAtIndex L p q).hom =
      (horizontalStablePageGradedIsoAtIndex K p q).hom ≫
        horizontalTotalHomologyGradedPieceMapOfBicomplex f p q := by
  have hStable :
      horizontalStablePageMapOfBicomplex f p q ≫
          (horizontalStablePageCanonicalAbutmentIso L
            (horizontalStablePageIndex p q)
            (horizontalStablePageIndex_one_le p q) p q
            (horizontalStablePageIndex_lower_bound p q)
            (horizontalStablePageIndex_upper_bound p q)).hom =
        (horizontalStablePageCanonicalAbutmentIso K
            (horizontalStablePageIndex p q)
            (horizontalStablePageIndex_one_le p q) p q
            (horizontalStablePageIndex_lower_bound p q)
            (horizontalStablePageIndex_upper_bound p q)).hom ≫
          horizontalCanonicalAbutmentMapOfBicomplex f p q := by
    simpa [horizontalStablePageMapOfBicomplex,
      horizontalFirstQuadrantSpectralSequence] using
      horizontalStablePageCanonicalAbutmentIso_naturality f
        (horizontalStablePageIndex p q)
        (horizontalStablePageIndex_one_le p q) p q
        (horizontalStablePageIndex_lower_bound p q)
        (horizontalStablePageIndex_upper_bound p q)
  have hGraded := horizontalCanonicalAbutmentGradedIso_naturality f p q
  dsimp only [horizontalStablePageGradedIsoAtIndex,
    horizontalStablePageGradedIso, Iso.trans_hom]
  calc
    horizontalStablePageMapOfBicomplex f p q ≫
          ((horizontalStablePageCanonicalAbutmentIso L
              (horizontalStablePageIndex p q)
              (horizontalStablePageIndex_one_le p q) p q
              (horizontalStablePageIndex_lower_bound p q)
              (horizontalStablePageIndex_upper_bound p q)).hom ≫
            (horizontalCanonicalAbutmentGradedIso L p q).hom) =
      (horizontalStablePageMapOfBicomplex f p q ≫
          (horizontalStablePageCanonicalAbutmentIso L
            (horizontalStablePageIndex p q)
            (horizontalStablePageIndex_one_le p q) p q
            (horizontalStablePageIndex_lower_bound p q)
            (horizontalStablePageIndex_upper_bound p q)).hom) ≫
        (horizontalCanonicalAbutmentGradedIso L p q).hom :=
      (Category.assoc _ _ _).symm
    _ = ((horizontalStablePageCanonicalAbutmentIso K
            (horizontalStablePageIndex p q)
            (horizontalStablePageIndex_one_le p q) p q
            (horizontalStablePageIndex_lower_bound p q)
            (horizontalStablePageIndex_upper_bound p q)).hom ≫
          horizontalCanonicalAbutmentMapOfBicomplex f p q) ≫
        (horizontalCanonicalAbutmentGradedIso L p q).hom := by
      rw [hStable]
    _ = (horizontalStablePageCanonicalAbutmentIso K
            (horizontalStablePageIndex p q)
            (horizontalStablePageIndex_one_le p q) p q
            (horizontalStablePageIndex_lower_bound p q)
            (horizontalStablePageIndex_upper_bound p q)).hom ≫
        (horizontalCanonicalAbutmentMapOfBicomplex f p q ≫
          (horizontalCanonicalAbutmentGradedIso L p q).hom) :=
      Category.assoc _ _ _
    _ = (horizontalStablePageCanonicalAbutmentIso K
            (horizontalStablePageIndex p q)
            (horizontalStablePageIndex_one_le p q) p q
            (horizontalStablePageIndex_lower_bound p q)
            (horizontalStablePageIndex_upper_bound p q)).hom ≫
        ((horizontalCanonicalAbutmentGradedIso K p q).hom ≫
          horizontalTotalHomologyGradedPieceMapOfBicomplex f p q) := by
      rw [hGraded]
    _ = ((horizontalStablePageCanonicalAbutmentIso K
            (horizontalStablePageIndex p q)
            (horizontalStablePageIndex_one_le p q) p q
            (horizontalStablePageIndex_lower_bound p q)
            (horizontalStablePageIndex_upper_bound p q)).hom ≫
          (horizontalCanonicalAbutmentGradedIso K p q).hom) ≫
        horizontalTotalHomologyGradedPieceMapOfBicomplex f p q :=
      (Category.assoc _ _ _).symm

end HomologicalComplex₂

end
