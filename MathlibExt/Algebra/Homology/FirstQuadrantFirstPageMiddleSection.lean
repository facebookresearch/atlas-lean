/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFirstPageSections

/-!
# Lifting an adjacent-column class to the middle quotient

The supported-degree section of the stage-to-column projection is followed
by the quotient map to the middle term of the adjacent-column short exact
sequence.  The resulting morphism is a degreewise section of that short
exact sequence's right map.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

/-- The quotient projection onto the right direct column factors through the
right map of the adjacent-column short exact sequence. -/
theorem horizontalFirstPageAdjacentCokernelπ_comp_g (p : ℕ) :
    cokernel.π (horizontalFirstPageFiltrationMap K p ≫
        horizontalFirstPageNextFiltrationMap K p) ≫
      (horizontalFirstPageAdjacentDirectShortComplex K p).g =
    horizontalCompleteDirectColumnProjectionMap K (p + 1) := by
  dsimp [horizontalFirstPageAdjacentDirectShortComplex,
    horizontalFirstPageAdjacentCokernelShortComplex,
    CategoryTheory.cokernelCompShortComplex,
    horizontalFirstPageAdjacentRightIso,
    horizontalFirstPageNextCokernelIso,
    horizontalFirstPageCokernelIso]
  rw [cokernel.π_desc_assoc]
  simp only [Category.id_comp]
  rw [cokernel.mapIso_hom]
  rw [cokernel.π_desc_assoc]
  simp only [Iso.refl_hom, Category.id_comp]
  unfold horizontalFirstPageCokernelToDirectColumn
  rw [cokernel.π_desc]

/-- Degreewise lift of a class in column `p+1` to the middle two-column
quotient. -/
noncomputable def horizontalFirstPageAdjacentMiddleSection (p q : ℕ) :
    (horizontalDirectColumnCochain K (p + 1)).X
        (-((p + 1 : ℕ) : ℤ) - q) ⟶
      (horizontalFirstPageAdjacentDirectShortComplex K p).X₂.X
        (-((p + 1 : ℕ) : ℤ) - q) :=
  horizontalCompleteSuccDirectColumnSection K p q ≫
    (cokernel.π (horizontalFirstPageFiltrationMap K p ≫
      horizontalFirstPageNextFiltrationMap K p)).f
        (-((p + 1 : ℕ) : ℤ) - q)

/-- The middle lift is a section of the adjacent sequence's right map in the
supported degree. -/
theorem horizontalFirstPageAdjacentMiddleSection_g (p q : ℕ) :
    horizontalFirstPageAdjacentMiddleSection K p q ≫
        (horizontalFirstPageAdjacentDirectShortComplex K p).g.f
          (-((p + 1 : ℕ) : ℤ) - q) =
      𝟙 _ := by
  dsimp [horizontalFirstPageAdjacentMiddleSection]
  rw [Category.assoc, ← HomologicalComplex.comp_f,
    horizontalFirstPageAdjacentCokernelπ_comp_g]
  exact horizontalCompleteSuccDirectColumnSection_projection K p q

end HomologicalComplex₂

end
