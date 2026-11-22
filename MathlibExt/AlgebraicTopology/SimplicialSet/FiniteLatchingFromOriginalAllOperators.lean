/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.AllFiniteLatchingInvariants
import MathlibExt.AlgebraicTopology.SimplicialSet.EquifibredDiagonalPullback

/-!
# Sharp finite latching stages from simplex-operator comparisons

If every row map of a simplicial diagram map is sharp and every simplex-operator relative comparison is a weak equivalence, each finite degeneracy latching-stage map is sharp. Its incoming square with the degree n + 1 row also has a weak pullback-to-homotopy-pullback comparison, for every stage in every degree.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.RezkFiniteFromAllOperators
open SharpComparisonDraft

/-- The finite invariant follows from ALL original operator comparisons and
the original row sharpness; no finite-stage outcome is a hypothesis. -/
theorem all_finite_from_original_operators
    {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (hrows : ∀ n : SimplexCategory, Sharp (eta.app (op n)))
    (hoperators : ∀ {n m : SimplexCategory} (f : n ⟶ m),
      WeakEquivalence (EquifibredDiagonal.relativeComparison eta f)) :
    ∀ (n : ℕ) (r : Fin (n + 1)),
      Sharp (outerLatchingStageMap eta n r) ∧
        WeakEquivalence
          (pullback.lift (outerLatchingStage X n r).ι (outerLatchingStageMap eta n r)
            (outerLatchingStageMap_ι eta n r).symm ≫
            comparison (eta.app (op ⦋n + 1⦌)) (outerLatchingStage Y n r).ι) := by
  apply RezkAllFiniteLatching.all_stage_sharp_and_incoming eta (fun n => hrows ⦋n⦌)
  intro n r
  change WeakEquivalence
    (EquifibredDiagonal.relativeComparison eta (SimplexCategory.σ r) ≫
      comparison (eta.app (op ⦋n + 1⦌)) (Y.σ r))
  exact (weakEquivalence_iff _).2
    ((weakEquivalences SSet.{u}).comp_mem _ _
      ((weakEquivalence_iff _).1 (hoperators (SimplexCategory.σ r)))
      ((weakEquivalence_iff _).1 (hrows ⦋n + 1⦌ _ _)))

end SSet.RezkFiniteFromAllOperators
