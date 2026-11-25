/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantAbutmentImage

/-! # Tests for the finite abutment image quotient -/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂.FirstQuadrantAbutmentImageTests

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

example (r : ℤ) (hr : 1 ≤ r) (p q : ℕ)
    (hlower : (p : ℤ) + 1 ≤ r) (hupper : (q : ℤ) + 2 ≤ r) :
    ((horizontalFirstQuadrantSpectralSequence K).page r).X (p, q) ≅
      horizontalFirstQuadrantCanonicalAbutmentTerm K p q :=
  horizontalStablePageCanonicalAbutmentIso K r hr p q hlower hupper

example (p q : ℕ) :
    (ShortComplex.mk
      (horizontalCanonicalAbutmentBoundaryMap K p q)
      (horizontalCanonicalAbutmentToUpperHomologyMap K p q)
      (horizontalCanonicalAbutmentBoundary_comp_toUpper K p q)).Exact :=
  horizontalCanonicalAbutmentBoundaryToUpper_exact K p q

example (p q : ℕ) :
    horizontalFirstQuadrantCanonicalAbutmentTerm K p q ≅
      horizontalCanonicalAbutmentImageQuotient K p q :=
  horizontalCanonicalAbutmentImageQuotientIso K p q

end HomologicalComplex₂.FirstQuadrantAbutmentImageTests

end
