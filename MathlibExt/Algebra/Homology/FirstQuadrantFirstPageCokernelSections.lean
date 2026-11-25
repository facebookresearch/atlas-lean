/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFirstPageHorizontalCycles

/-!
# Sections and supported-degree cokernel inverses

In every column, the inverse of the canonical cokernel-to-column isomorphism
is computed in supported degrees by including the top summand into the
filtration stage and then applying the abstract cokernel projection.  The
zero column uses its direct complete-stage presentation; positive columns use
the natural-stage presentation.
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

/-- In column `p+1`, the inverse cokernel comparison is represented by the
supported-degree section followed by the cokernel projection. -/
theorem horizontalFirstPageCokernelIso_inv_f_succ (p q : ℕ) :
    (horizontalFirstPageCokernelIso K (p + 1)).inv.f
        (-((p + 1 : ℕ) : ℤ) - q) =
      horizontalCompleteSuccDirectColumnSection K p q ≫
        (cokernel.π (horizontalFirstPageFiltrationMap K (p + 1))).f
          (-((p + 1 : ℕ) : ℤ) - q) := by
  let n : ℤ := -((p + 1 : ℕ) : ℤ) - q
  apply (cancel_mono
    ((horizontalFirstPageCokernelIso K (p + 1)).hom.f n)).1
  rw [← HomologicalComplex.comp_f,
    (horizontalFirstPageCokernelIso K (p + 1)).inv_hom_id]
  simp only [HomologicalComplex.id_f]
  rw [Category.assoc, ← HomologicalComplex.comp_f]
  change 𝟙 _ = horizontalCompleteSuccDirectColumnSection K p q ≫
    (cokernel.π (horizontalFirstPageFiltrationMap K (p + 1)) ≫
      horizontalFirstPageCokernelToDirectColumn K (p + 1)).f n
  unfold horizontalFirstPageCokernelToDirectColumn
  rw [cokernel.π_desc]
  exact (horizontalCompleteSuccDirectColumnSection_projection K p q).symm

/-- In column zero, the inverse cokernel comparison is represented by the
direct complete-stage section followed by the cokernel projection. -/
theorem horizontalFirstPageCokernelIso_inv_f_zero (q : ℕ) :
    (horizontalFirstPageCokernelIso K 0).inv.f
        (-((0 : ℕ) : ℤ) - q) =
      horizontalCompleteDirectColumnSectionComponent K 0 q ≫
        (cokernel.π (horizontalFirstPageFiltrationMap K 0)).f
          (-((0 : ℕ) : ℤ) - q) := by
  let n : ℤ := -((0 : ℕ) : ℤ) - q
  apply (cancel_mono ((horizontalFirstPageCokernelIso K 0).hom.f n)).1
  rw [← HomologicalComplex.comp_f,
    (horizontalFirstPageCokernelIso K 0).inv_hom_id]
  simp only [HomologicalComplex.id_f]
  rw [Category.assoc, ← HomologicalComplex.comp_f]
  change 𝟙 _ = horizontalCompleteDirectColumnSectionComponent K 0 q ≫
    (cokernel.π (horizontalFirstPageFiltrationMap K 0) ≫
      horizontalFirstPageCokernelToDirectColumn K 0).f n
  unfold horizontalFirstPageCokernelToDirectColumn
  rw [cokernel.π_desc]
  dsimp [horizontalCompleteDirectColumnProjectionMap,
    horizontalDirectColumnProjectionMap]
  have hproj : horizontalDirectColumnProjection K 0
      (-((0 : ℕ) : ℤ) - q) =
        horizontalDirectColumnProjectionComponent K 0 q :=
    horizontalDirectColumnProjection_eq_component K 0 q
  rw [hproj]
  exact (horizontalCompleteDirectColumnSectionComponent_projection K 0 q).symm

end HomologicalComplex₂

end
