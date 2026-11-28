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
# A degreewise section of the adjacent-column middle quotient

Let `K` be a first-quadrant bicomplex in an abelian category. The stage-to-column projection
for column `p+1` factors through the middle cokernel of the adjacent-column short exact
sequence.

At cochain degree `-(p+1)-q`, compose the complete-stage column section with this middle
quotient projection. The resulting degreewise lift is a section of the adjacent sequence's
right map.
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

/-- The factorization of a direct-column projection through the middle quotient.

The cokernel projection of the composite filtration map followed by the adjacent sequence's
right map equals the projection onto direct column `p+1`. -/
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

/-- The degreewise lift of a direct-column element to the middle quotient.

At degree `-(p+1)-q`, the complete column section followed by the composite-map cokernel
projection lifts column `p+1` into the adjacent middle term. -/
noncomputable def horizontalFirstPageAdjacentMiddleSection (p q : ℕ) :
    (horizontalDirectColumnCochain K (p + 1)).X
        (-((p + 1 : ℕ) : ℤ) - q) ⟶
      (horizontalFirstPageAdjacentDirectShortComplex K p).X₂.X
        (-((p + 1 : ℕ) : ℤ) - q) :=
  horizontalCompleteSuccDirectColumnSection K p q ≫
    (cokernel.π (horizontalFirstPageFiltrationMap K p ≫
      horizontalFirstPageNextFiltrationMap K p)).f
        (-((p + 1 : ℕ) : ℤ) - q)

/-- The section identity of the adjacent-column middle lift.

The middle section followed by the right quotient map is the identity on the direct-column
term in degree `-(p+1)-q`. -/
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
