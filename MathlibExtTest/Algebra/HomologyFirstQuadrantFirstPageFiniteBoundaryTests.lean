/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFirstPageFiniteBoundary

/-! # Tests for the finite-stage horizontal boundary -/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂.FirstQuadrantFirstPageFiniteBoundaryTests

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

example (p q : ℕ) :
    (K.X (p + 1)).iCycles q ≫
        horizontalFilteredTopInclusion K (p + 1) q ≫
        horizontalFilteredTotalD K (p + 1) (p + 1 + q) (p + q) =
      (K.X (p + 1)).iCycles q ≫ (K.d (p + 1) p).f q ≫
        horizontalFilteredPreviousColumnInclusion K p q :=
  horizontalFilteredTopInclusion_d_eq_previous K p q

example (p q : ℕ) :
    (horizontalDirectColumnCochain K (p + 1)).iCycles
        (-((p + 1 : ℕ) : ℤ) - q) ≫
      (horizontalDirectColumnCochainXIso K (p + 1) q).hom ≫
      horizontalFilteredTopInclusion K (p + 1) q ≫
      horizontalFilteredTotalD K (p + 1) (p + 1 + q) (p + q) =
    (horizontalDirectColumnCochain K (p + 1)).iCycles
        (-((p + 1 : ℕ) : ℤ) - q) ≫
      (horizontalDirectColumnCochainXIso K (p + 1) q).hom ≫
      (K.d (p + 1) p).f q ≫
      horizontalFilteredPreviousColumnInclusion K p q :=
  horizontalDirectColumnTopInclusion_d_eq_previous K p q

end HomologicalComplex₂.FirstQuadrantFirstPageFiniteBoundaryTests

end
