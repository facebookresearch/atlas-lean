/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SAMECompletionSmithComparisonData
import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalSmithCSSCompleteComparison
import MathlibExt.AlgebraicTopology.SimplicialSpace.SAMECoreDerivedImageCompleteness

/-!
# Complete Segal targets in the completion comparison

For a Segal space, the diagonal completion, Smith replacement and their common target are
complete Segal spaces and fibrant in the named Rezk model. The Smith unit from the diagonal
completion to the common target is levelwise weak and an intrinsic Dwyer–Kan equivalence.
-/

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory HomotopicalAlgebra Opposite
open scoped Simplicial

namespace SimplicialSpace.RezkCompletionSmithComparison

/-- Both actual completion targets are complete Segal, with the SAME target
derived internally from the original Segal source. -/
theorem complete_endpoints (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    completeSegalSpaces (RezkCompletionData.completion.obj W) ∧
      completeSegalSpaces (OriginalSmithCSS.replacement.obj W) :=
  ⟨RezkCompletionCoreDiagonal.sameCompletion_completeSegal_from_derived_image_fibres W hW,
    OriginalSmithCSS.replacement_completeSegal W⟩

/-- The two actual targets and their common target are fibrant in the
literal named CSS model. -/
theorem all_three_CSSFibrant (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    let _ : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
    IsFibrant (RezkCompletionData.completion.obj W) ∧
      IsFibrant (OriginalSmithCSS.replacement.obj W) ∧
        IsFibrant (commonTarget.obj W) := by
  let _ : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
  exact ⟨(RezkModel.isFibrant_iff_completeSegalSpaces _).mpr (complete_endpoints W hW).1,
    (RezkModel.isFibrant_iff_completeSegalSpaces _).mpr (complete_endpoints W hW).2,
    (RezkModel.isFibrant_iff_completeSegalSpaces _).mpr (commonTarget_completeSegal W)⟩

/-- The actual Smith unit at the constructed SAME completion is weak in every row. -/
theorem completionToCommon_levelwise_weak (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (n : ℕ) :
    SSet.realizationWeakEquivalences ((completionToCommon.app W).hom.app (op ⦋n⦌)) :=
  OriginalSmithCSS.unit_levelwise_weak_of_complete
    (RezkCompletionData.completion.obj W) (complete_endpoints W hW).1 n

/-- The first common-target map is intrinsically DK by its actual complete endpoints. -/
theorem completionToCommon_intrinsicDK (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    IntrinsicDK.isEquivalence (completionToCommon.app W)
      (RezkCompletionAllVertex.sameCompletion_segal W hW)
      (((FiniteCompletenessHorel.completeSegalSpaces_iff_finiteComplete
        (commonTarget.obj W)).mp (commonTarget_completeSegal W)).1) :=
  OriginalSmithCSS.unit_intrinsicDK_of_complete
    (RezkCompletionData.completion.obj W) (complete_endpoints W hW).1

end SimplicialSpace.RezkCompletionSmithComparison
