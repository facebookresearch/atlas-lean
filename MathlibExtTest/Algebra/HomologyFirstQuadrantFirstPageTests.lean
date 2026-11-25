/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFirstPage

/-! # Tests for the first page of the first-quadrant spectral sequence -/

@[expose] public section

open CategoryTheory Limits

attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

noncomputable section

universe v u

namespace HomologicalComplex₂.FirstQuadrantFirstPageTests

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

example (p q : ℕ) : C :=
  horizontalFirstPageRelativeHomology K p q

example (p q : ℕ) :
    ((horizontalFirstQuadrantSpectralSequence K).page 1).X (p, q) ≅
      horizontalFirstPageRelativeHomology K p q :=
  horizontalFirstPageXIso K p q

example : horizontalFirstPageLowerIndex 0 = (-1 : ℤ) :=
  rfl

end HomologicalComplex₂.FirstQuadrantFirstPageTests

end
