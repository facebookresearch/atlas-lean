/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Algebra.Quaternion.Centralizer

open scoped Quaternion

namespace QuaternionCentralizerTest

/-- Consumer with the original binders and hypotheses. -/
theorem exactSource
    {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (α : ℍ[ℚ, a, b])
    (hnc : ¬ (α.imI = 0 ∧ α.imJ = 0 ∧ α.imK = 0)) (x : ℍ[ℚ, a, b]) :
    x * α = α * x ↔ ∃ c e : ℚ, x = c • (1 : ℍ[ℚ, a, b]) + e • α :=
  QuaternionAlgebra.commute_iff_exists_eq_smul_one_add_smul ha hb α hnc x

/-- The non-scalar hypothesis matters: every quaternion commutes with
`1`, but a pure imaginary quaternion is not in the span of `1`. -/
example :
    (⟨0, 1, 0, 0⟩ : ℍ[ℚ, 1, 1]) * (1 : ℍ[ℚ, 1, 1]) =
        (1 : ℍ[ℚ, 1, 1]) * (⟨0, 1, 0, 0⟩ : ℍ[ℚ, 1, 1]) ∧
      ¬ ∃ c e : ℚ, (⟨0, 1, 0, 0⟩ : ℍ[ℚ, 1, 1]) =
        c • (1 : ℍ[ℚ, 1, 1]) + e • (1 : ℍ[ℚ, 1, 1]) := by
  refine ⟨by simp, ?_⟩
  rintro ⟨c, e, hce⟩
  have h1 := congrArg QuaternionAlgebra.imI hce
  simp at h1

end QuaternionCentralizerTest
