/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.InnerProductSpace.ClosedRangeAdjoint
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Tests for the closed-range theorem for adjoints
-/

namespace ClosedRangeAdjointTest

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- The adjoint of the zero operator has closed range. -/
example : IsClosed (LinearMap.range (ContinuousLinearMap.adjoint (0 : E →L[𝕜] E)).toLinearMap :
    Set E) := by
  have h : IsClosed (LinearMap.range (0 : E →L[𝕜] E).toLinearMap : Set E) := by
    simp
  exact (ContinuousLinearMap.isClosed_range_adjoint_iff (0 : E →L[𝕜] E)).mp h

/-- The adjoint of the identity operator has closed range. -/
example : IsClosed (LinearMap.range (ContinuousLinearMap.adjoint (ContinuousLinearMap.id 𝕜 E)).toLinearMap :
    Set E) := by
  have h : IsClosed (LinearMap.range (ContinuousLinearMap.id 𝕜 E).toLinearMap : Set E) := by
    simp
  exact (ContinuousLinearMap.isClosed_range_adjoint_iff (ContinuousLinearMap.id 𝕜 E)).mp h

/-- The reverse direction of the iff, for the identity operator. -/
example : IsClosed (LinearMap.range (ContinuousLinearMap.id 𝕜 E).toLinearMap : Set E) := by
  apply (ContinuousLinearMap.isClosed_range_adjoint_iff (ContinuousLinearMap.id 𝕜 E)).mpr
  rw [ContinuousLinearMap.adjoint_id]
  simp

/-- In finite dimensions every range is closed, so the iff transfers closedness
to the adjoint. -/
example (T : EuclideanSpace 𝕜 (Fin 2) →L[𝕜] EuclideanSpace 𝕜 (Fin 2)) :
    IsClosed (LinearMap.range (ContinuousLinearMap.adjoint T).toLinearMap :
      Set (EuclideanSpace 𝕜 (Fin 2))) := by
  apply (ContinuousLinearMap.isClosed_range_adjoint_iff T).mp
  exact Submodule.closed_of_finiteDimensional _

/-- The kernel-complement restriction does not change the range. -/
example (S : E →L[𝕜] E) :
    Set.range (S.comp (Submodule.subtypeL (LinearMap.ker S.toLinearMap)ᗮ)) = Set.range S :=
  ContinuousLinearMap.range_comp_subtypeL_orthogonalComplement_ker S

#print axioms ContinuousLinearMap.isClosed_range_adjoint_iff

end ClosedRangeAdjointTest
