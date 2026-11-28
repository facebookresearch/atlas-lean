/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

import MathlibExt.Analysis.CStarAlgebra.GNS.NullSubmodule

/-!
# A concrete positive-functional GNS nullspace

First-coordinate evaluation on the actual product C-star algebra ℂ × ℂ
is positive. Its closed GNS nullspace is exactly the second-coordinate
axis, so it contains a nonzero vector and excludes a different unit
coordinate. Left multiplication and the zero-functional case use the
same actual kernel carrier. This client is freshly authored.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped ComplexOrder

namespace GNSNullSubmoduleSmoke

private def firstCoordinate : (ℂ × ℂ) →ₚ[ℂ] ℂ where
  toLinearMap := LinearMap.fst ℂ ℂ ℂ
  monotone' := fun _ _ h => h.1

private theorem mem_firstCoordinate_null (a : ℂ × ℂ) :
    a ∈ firstCoordinate.gnsNullSubmodule ↔ a.1 = 0 := by
  rw [PositiveLinearMap.mem_gnsNullSubmodule]
  change star a.1 * a.1 = 0 ↔ a.1 = 0
  simp only [mul_eq_zero, star_eq_zero, or_self]

example : ((0, 1) : ℂ × ℂ) ∈ firstCoordinate.gnsNullSubmodule := by
  rw [mem_firstCoordinate_null]

example : ((1, 0) : ℂ × ℂ) ∉ firstCoordinate.gnsNullSubmodule := by
  rw [mem_firstCoordinate_null]
  exact one_ne_zero

example (a : ℂ × ℂ) : a * (0, 1) ∈ firstCoordinate.gnsNullSubmodule := by
  exact firstCoordinate.mul_mem_gnsNullSubmodule a
    ((mem_firstCoordinate_null (0, 1)).mpr rfl)

example :
    PositiveLinearMap.gnsNullSubmodule (0 : (ℂ × ℂ) →ₚ[ℂ] ℂ) =
      (⊤ : ClosedSubmodule ℂ (ℂ × ℂ)) :=
  PositiveLinearMap.gnsNullSubmodule_zero

end GNSNullSubmoduleSmoke
