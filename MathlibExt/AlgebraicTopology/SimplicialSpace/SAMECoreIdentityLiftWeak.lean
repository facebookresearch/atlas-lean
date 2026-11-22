/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalRawIdentityCoreWeak

/-!
# Weakness of the actual fixed-beta core identity lift

The original raw identity weakness is derived in its owning module. The
prefix i and the SAME baseline beta-zero are native trivial cofibrations.
The actual betaLift prefix equation then proves weakness of L by two out of
three. Target Segalness remains its independent genuine upstream input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SimplicialSpace.RezkCompletionCoreDiagonal

/-- The actual original raw identity followed by the genuine scalar prefix
is weak, with no provided source-core weakness premise. -/
theorem sameRawIdentityEvaluation_weak (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (hHat : segalSpaces (RezkCompletionData.completion.obj W)) :
    SSet.realizationWeakEquivalences (sameRawIdentityEvaluation W hW hHat) := by
  change SSet.realizationWeakEquivalences
    (rawIdentityCore W hW ≫ (sameCoreRectification W hW hHat).i)
  exact SSet.realizationWeakEquivalences.comp_mem _ _
    (originalRawIdentityCore_weak W hW)
    (sameCoreRectification_prefix_trivialCofibration W hW hHat).2

/-- The previously constructed native SAME lift L is weak by its literal
beta-prefix equation and the genuinely weak baseline beta-zero. -/
theorem sameCoreIdentityLift_weak (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (hHat : segalSpaces (RezkCompletionData.completion.obj W)) :
    SSet.realizationWeakEquivalences (sameCoreIdentityLift W hW hHat) := by
  have hb : SSet.realizationWeakEquivalences (sameBetaZero W) :=
    (sameBetaZero_trivialCofibration W).2
  apply (SSet.realizationWeakEquivalences.precomp_iff (sameBetaZero W)
    (sameCoreIdentityLift W hW hHat) hb).mp
  rw [sameCoreIdentityLift_prefixed_raw]
  exact sameRawIdentityEvaluation_weak W hW hHat

end SimplicialSpace.RezkCompletionCoreDiagonal
