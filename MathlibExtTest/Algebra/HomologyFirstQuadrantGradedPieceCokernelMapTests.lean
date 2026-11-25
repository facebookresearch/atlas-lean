/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantGradedPieceCokernelMap

/-! # Tests for the horizontal graded-piece cokernel map -/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂.FirstQuadrantGradedPieceCokernelMapTests

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

example (p : ℕ) :
    horizontalFirstPageFiltrationMap K p ≫
      horizontalCompleteDirectColumnProjectionMap K p = 0 :=
  horizontalFirstPageFiltrationMap_projection_zero K p

example (p : ℕ) :
    cokernel (horizontalFirstPageFiltrationMap K p) ⟶
      horizontalDirectColumnCochain K p :=
  horizontalFirstPageCokernelToDirectColumn K p

end HomologicalComplex₂.FirstQuadrantGradedPieceCokernelMapTests

end
