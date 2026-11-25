/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFirstPageCokernelSections

/-! # Tests for supported-degree cokernel sections -/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂.FirstQuadrantFirstPageCokernelSectionsTests

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

example (p q : ℕ) :
    (horizontalFirstPageCokernelIso K (p + 1)).inv.f
        (-((p + 1 : ℕ) : ℤ) - q) =
      horizontalCompleteSuccDirectColumnSection K p q ≫
        (cokernel.π (horizontalFirstPageFiltrationMap K (p + 1))).f
          (-((p + 1 : ℕ) : ℤ) - q) :=
  horizontalFirstPageCokernelIso_inv_f_succ K p q

example (q : ℕ) :
    (horizontalFirstPageCokernelIso K 0).inv.f
        (-((0 : ℕ) : ℤ) - q) =
      horizontalCompleteDirectColumnSectionComponent K 0 q ≫
        (cokernel.π (horizontalFirstPageFiltrationMap K 0)).f
          (-((0 : ℕ) : ℤ) - q) :=
  horizontalFirstPageCokernelIso_inv_f_zero K q

end HomologicalComplex₂.FirstQuadrantFirstPageCokernelSectionsTests

end
