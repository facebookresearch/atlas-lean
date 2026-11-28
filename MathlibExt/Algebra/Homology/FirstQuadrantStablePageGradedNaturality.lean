/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua -/

module

public import
  MathlibExt.Algebra.Homology.FirstQuadrantCanonicalAbutmentGradedNaturality

/-!
# Naturality of the bounded stable-page associated-graded comparison

Let f : K → L be a map of nonnegative homological bicomplexes in an
abelian category C. At bidegree (p,q), put n=p+q and
r₀=max(p+1,q+2).

The comparison E^(r₀)_(p,q) ≅ gr_p H_n(Tot(K)) is natural:
χ_L ∘ m_(r₀)(f) = gr_p H_n(Tot(f)) ∘ χ_K.
The graded piece is the cokernel of the preceding-to-current
induced homology filtration inclusion. The comparison passes
through the bottom-indexed canonical abutment term and preserves
the actual fixed stable-page map.
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

/-- For a map f : K → L of nonnegative homological bicomplexes
in an abelian category, p,q∈ℕ and r₀=max(p+1,q+2), the maps
χ_K : E^(r₀)_K(p,q) ≅ gr_p H_(p+q)(Tot(K)) and χ_L satisfy
χ_L ∘ m_(r₀)(f) = gr_p H_(p+q)(Tot(f)) ∘ χ_K.
The map on the right is induced on the homology filtration quotient. -/
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
