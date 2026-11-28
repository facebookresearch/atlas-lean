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
# Supported inverse formulas for the first-page cokernel comparison

Let K be a nonnegative homological bicomplex in an abelian category C.
The quotient of consecutive complete filtration stages
Q_p = coker(F_(p−1) → F_p) is isomorphic to the direct cochain column D_p.

In every supported degree i=−p−q, the inverse D_p^i → Q_p^i is the
degreewise top-column section D_p^i → F_p^i followed by the cokernel
projection. At p=0 this uses the direct complete zero-stage section;
at positive columns it uses the natural finite-stage presentation.
No chain-map section is required for this supported component formula.
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

/-- For a nonnegative homological bicomplex K in an abelian
category and p,q ≥ 0, the inverse comparison
D_(p+1) → coker(F_p → F_(p+1)) has component in degree
i=−(p+1)−q equal to π_i ∘ s_(p+1,q).
Here s is the supported degreewise column section into F_(p+1),
and π is the consecutive-stage cokernel projection. -/
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

/-- For a nonnegative homological bicomplex K in an abelian
category and q ≥ 0, the inverse D_0 → coker(F_(−1) → F_0)
has component in degree −q equal to the direct zero-stage
section followed by the cokernel projection.
The complete lower stage F_(−1) is zero. -/
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
