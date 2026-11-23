/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanAugmentationElementsRowsOf
import MathlibExt.AlgebraicTopology.SimplicialSet.BisimplicialDiagonalWeakEquivalence

/-!
# Actual generalized BK augmentation weakness from full original scalar elements projections

The proved whole original row comparison identifies every actual row
augmentation with its original elements projection. The actual
bisimplicial diagonal theorem and original constant-diagonal isomorphism
therefore prove weakness of the SAME original BK augmentation. No
augmentation outcome or row comparison is assumed as a constructor field.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe uJ vJ w
open CategoryTheory Opposite
open scoped Simplicial
namespace SSet.BousfieldKanRowsOf
variable {J : Type uJ} [Category.{vJ} J]
  {D : J ⥤ SSet.{max uJ vJ w}} {Z : SSet.{max uJ vJ w}}

/-- The actual original weighted-row augmentation is weak from its genuine original projection nerve map. -/
theorem rowAugmentation_weak (τ : D ⟶ (Functor.const J).obj Z) (q : SimplexCategoryᵒᵖ)
    (h : realizationWeakEquivalences
      (nerveMapHomDown.{max uJ vJ w, vJ, max uJ vJ w} (rowProjection τ q))) :
    realizationWeakEquivalences (wbarRowAugmentation τ q) := by
  have hr := realizationWeakEquivalences.comp_mem _ _
    (realizationWeakEquivalences.of_isIso (rowNerveIso D q).hom)
    (realizationWeakEquivalences.comp_mem _ _ h
      (realizationWeakEquivalences.of_isIso (SSet.nerveDiscreteIso (Z.obj q)).hom))
  exact rowAugmentation_projection τ q ▸ hr

/-- The SAME original generalized BK augmentation is weak from the full
original projection nerves in every scalar degree. -/
theorem bkAugmentation_weak (τ : D ⟶ (Functor.const J).obj Z)
    (h : ∀ q : SimplexCategoryᵒᵖ, realizationWeakEquivalences
      (nerveMapHomDown.{max uJ vJ w, vJ, max uJ vJ w} (rowProjection τ q))) :
    realizationWeakEquivalences (bkAugmentationOf τ) := by
  have hRows (n : ℕ) : realizationWeakEquivalences
      ((simplicialTransposeFunctor.map (wbarAugmentationOf τ)).app (op ⦋n⦌)) := by
    have hr := realizationWeakEquivalences.comp_mem _ _
      (realizationWeakEquivalences.of_isIso (wbarRowEvaluationIso D (op ⦋n⦌)).hom)
      (rowAugmentation_weak τ (op ⦋n⦌) (h (op ⦋n⦌)))
    change realizationWeakEquivalences (Functor.whiskerRight (wbarAugmentationOf τ)
      ((evaluation SimplexCategoryᵒᵖ (Type (max uJ vJ w))).obj (op ⦋n⦌)))
    exact wbarRowEvaluationIso_hom_comp_rowAugmentation τ (op ⦋n⦌) ▸ hr
  have hd := simplicialDiagonal_map_mem_realizationWeakEquivalences_of_inner_rows
    (wbarAugmentationOf τ) hRows
  exact realizationWeakEquivalences.comp_mem _ _ hd
    (realizationWeakEquivalences.of_isIso (diagonalConstIso Z).hom)

end SSet.BousfieldKanRowsOf
