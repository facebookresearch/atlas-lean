/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.FirstQuadrantSpectralSequenceSupport

/-!
# The first page of the first-quadrant spectral sequence

The page-one object in bidegree `(p,q)` is canonically the relative homology
of the consecutive filtration stages `F_{p-1} → F_p`, in cochain degree
`-(p+q)`.  The extended-integer convention makes `F_{-1}=0`, so the same
formula covers the zeroth column.

The subsequent first-page column modules identify this relative term with
vertical homology and compute the actual page differential.
-/

@[expose] public section

open CategoryTheory Limits

attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

noncomputable section

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

/-- Lower extended filtration index for the `p`th graded piece. -/
def horizontalFirstPageLowerIndex (p : ℕ) : EInt :=
  @WithBotTop.coe ℤ ((p : ℤ) - 1)

/-- Upper extended filtration index for the `p`th graded piece. -/
def horizontalFirstPageUpperIndex (p : ℕ) : EInt :=
  @WithBotTop.coe ℤ (p : ℤ)

theorem horizontalFirstPageIndex_le (p : ℕ) :
    horizontalFirstPageLowerIndex p ≤ horizontalFirstPageUpperIndex p :=
  WithBotTop.coe_monotone (by lia)

/-- Relative homology of consecutive horizontal filtration stages in the
degree belonging to bidegree `(p,q)`. -/
abbrev horizontalFirstPageRelativeHomology (p q : ℕ) : C :=
  ((horizontalCompleteFiltrationSpectralObject K).H (-(p : ℤ) - q)).obj
    (ComposableArrows.mk₁ (homOfLE (horizontalFirstPageIndex_le p)))

/-- The canonical first-page identification with relative filtration
homology. -/
noncomputable def horizontalFirstPageXIso (p q : ℕ) :
    ((horizontalFirstQuadrantSpectralSequence K).page 1).X (p, q) ≅
      horizontalFirstPageRelativeHomology K p q :=
  (horizontalCompleteFiltrationSpectralObject K).spectralSequenceFirstPageXIso
    CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological
    (p, q)
    (horizontalFirstPageLowerIndex p)
    (horizontalFirstPageUpperIndex p)
    rfl rfl (-(p : ℤ) - q) rfl

end HomologicalComplex₂

end
