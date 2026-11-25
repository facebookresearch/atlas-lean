/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantSecondPage

/-! # Tests for the second-page bicomplex comparison -/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂.FirstQuadrantSecondPageTests

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

example (p q : ℕ) :
    (horizontalFirstPageNormalizedVerticalHomologyIso K p q).hom =
      ((p : ℤ) * ((q : ℤ) + 1)).negOnePow •
        (horizontalFirstPageCoherentVerticalHomologyIso K p q).hom :=
  horizontalFirstPageNormalizedVerticalHomologyIso_hom K p q

example (p q : ℕ) :
    ((horizontalFirstQuadrantSpectralSequence K).page 1).d
        (p + 1, q) (p, q) ≫
      (horizontalFirstPageNormalizedVerticalHomologyIso K p q).hom =
    (horizontalFirstPageNormalizedVerticalHomologyIso K (p + 1) q).hom ≫
      horizontalFirstPageHorizontalHomologyMap K p q :=
  horizontalFirstPage_d_normalizedVerticalHomology K p q

example (q : ℕ) :
    horizontalFirstPageRowComplex K q ≅ K.verticalHomologyComplex q :=
  horizontalFirstPageRowComplexIsoVerticalHomologyComplex K q

example (p q : ℕ) :
    ((horizontalFirstQuadrantSpectralSequence K).page 2).X (p, q) ≅
      (K.verticalHomologyComplex q).homology p :=
  horizontalSecondPageVerticalHorizontalHomologyIso K p q

end HomologicalComplex₂.FirstQuadrantSecondPageTests

end
