/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.OperatorTheory.HilbertAdjointClosedRange

namespace MathlibExt.Analysis.OperatorTheory.HilbertAdjointClosedRangeWanted

-- Projection onto a complete subspace is surjective. Its adjoint is the inclusion,
-- whose range can be a proper subspace of the ambient Hilbert space.
example {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    (K : Submodule ℂ X) [CompleteSpace K] : IsClosed (Set.range K.subtypeL) := by
  rw [← K.adjoint_orthogonalProjectionOnto]
  apply isClosed_range_adjoint_of_isClosed_range K.orthogonalProjectionOnto
  have h : Function.Surjective K.orthogonalProjectionOnto :=
    fun x ↦ ⟨x, K.orthogonalProjectionOnto_mem_subspace_eq_self x⟩
  change IsClosed (Set.range K.orthogonalProjectionOnto)
  rw [h.range_eq]
  exact isClosed_univ

end MathlibExt.Analysis.OperatorTheory.HilbertAdjointClosedRangeWanted
