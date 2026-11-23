/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.OperatorTheory.AdjointCompFredholmClosedRange

namespace MathlibExt.Analysis.OperatorTheory.AdjointCompFredholmClosedRangeWanted

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

-- A linear isometry may have range of infinite codimension.
example (T : X →ₗᵢ[ℂ] Y) : IsClosed (Set.range T) := by
  apply isClosed_range_of_isFredholm_adjoint_comp T.toContinuousLinearMap
  rw [T.adjoint_comp_self]
  exact ContinuousLinearMap.IsFredholm.id

-- The zero map from a complex line has a nontrivial kernel.
example : IsClosed (Set.range (0 : ℂ →L[ℂ] Y)) := by
  apply isClosed_range_of_isFredholm_adjoint_comp (0 : ℂ →L[ℂ] Y)
  rw [ContinuousLinearMap.comp_zero]
  exact ContinuousLinearMap.IsIdempotentElem.isFredholm IsIdempotentElem.zero

end MathlibExt.Analysis.OperatorTheory.AdjointCompFredholmClosedRangeWanted
