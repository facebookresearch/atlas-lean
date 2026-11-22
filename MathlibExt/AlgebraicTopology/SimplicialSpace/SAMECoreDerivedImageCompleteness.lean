/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SAMECoreImageFibreComponentCoverage
import MathlibExt.AlgebraicTopology.SimplicialSpace.SAMECoreIdentityLiftWeak
import MathlibExt.AlgebraicTopology.SimplicialSpace.SAMECompletionSegalFromOriginalAllVertexImage
import MathlibExt.AlgebraicTopology.SimplicialSpace.FiniteCompletenessHorelComparison

/-!
# Completeness of the same unlocalized Rezk completion

The actual target Segal theorem is used internally. The original raw identity,
its native beta lift, and the image-fibre factor are genuinely weak by their
constructed comparison proofs. The literal beta-prefixed equation then proves
the original identity and completeness restriction weak. All statements assume
only the original simplicial space and its Segalness.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SimplicialSpace.RezkCompletionCoreDiagonal

/-- The actual target identity is weak behind the same original beta-zero. -/
theorem sameCompletion_identity_weak_from_derived_image_fibres
    (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    SSet.realizationWeakEquivalences
      (SegalHomotopy.equivalenceIdentity (RezkCompletionData.completion.obj W)
        (RezkCompletionAllVertex.sameCompletion_segal W hW)) := by
  let hHat := RezkCompletionAllVertex.sameCompletion_segal W hW
  have hb : SSet.realizationWeakEquivalences (sameBetaZero W) :=
    (sameBetaZero_trivialCofibration W).2
  apply (SSet.realizationWeakEquivalences.precomp_iff (sameBetaZero W) _ hb).mp
  rw [← sameCoreIdentityLift_prefixed_identity W hW hHat]
  exact SSet.realizationWeakEquivalences.comp_mem _ _ hb
    (SSet.realizationWeakEquivalences.comp_mem _ _
      (sameCoreIdentityLift_weak W hW hHat) (sameCoreRectification_factor_weak W hW hHat))

/-- The literal finite completeness generator restriction is weak. -/
theorem sameCompletion_kappa_weak (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    SSet.realizationWeakEquivalences
      (FiniteCompletenessMapping.restriction (RezkCompletionData.completion.obj W)
        SSet.Rezk.FiniteCompleteness.kappa) :=
  (FiniteCompletenessHorel.completeness_tests_iff _
    (RezkCompletionAllVertex.sameCompletion_segal W hW)).2.2.2.mpr
      (sameCompletion_identity_weak_from_derived_image_fibres W hW)

/-- The actual full-E collapse yields a weak constant-map comparison. -/
theorem sameCompletion_fullEConstant_weak (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    SSet.realizationWeakEquivalences
      (FullEEquivalence.constantMap (RezkCompletionData.completion.obj W)) :=
  (FiniteCompletenessHorel.completeness_tests_iff _
    (RezkCompletionAllVertex.sameCompletion_segal W hW)).2.2.1.mp
      (sameCompletion_kappa_weak W hW)

/-- The original full walking-isomorphism completeness restriction is weak. -/
theorem sameCompletion_fullERestriction_weak (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    SSet.realizationWeakEquivalences
      (FiniteCompletenessMapping.restriction (RezkCompletionData.completion.obj W)
        SSet.Rezk.completenessMap) :=
  (FiniteCompletenessHorel.completeness_tests_iff _
    (RezkCompletionAllVertex.sameCompletion_segal W hW)).2.1.mp
      (sameCompletion_kappa_weak W hW)

/-- The same constructed completion is a complete Segal space. -/
theorem sameCompletion_completeSegal_from_derived_image_fibres
    (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    completeSegalSpaces (RezkCompletionData.completion.obj W) := by
  apply (FiniteCompletenessHorel.completeSegalSpaces_iff_finiteComplete _).mpr
  exact ⟨RezkCompletionAllVertex.sameCompletion_segal W hW,
    sameCompletion_kappa_weak W hW⟩

end SimplicialSpace.RezkCompletionCoreDiagonal
