/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.SingularValuePerturbation

@[expose] public section

open MathlibExt.Analysis.InnerProductSpace.SingularValuePerturbation

namespace MathlibExtTest.Analysis.InnerProductSpace.SingularValuePerturbation

/-- The identity of `ℝ²` has largest singular value `1`. -/
example : (LinearMap.id : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)).singularValues 0
    = 1 := by
  rw [← opNorm_eq_singularValues_zero]
  have : (LinearMap.id : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] _).toContinuousLinearMap =
      ContinuousLinearMap.id ℝ _ := rfl
  rw [this, ContinuousLinearMap.norm_id]

/-- The zero map has all singular values zero, so Weyl's inequality bounds every singular value
of `T` by `‖T‖₂`. -/
example (T : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) (k : ℕ) :
    T.singularValues k ≤ ‖T.toContinuousLinearMap‖ := by
  have h := abs_singularValues_sub_le T 0 k
  rw [LinearMap.singularValues_zero, Finsupp.coe_zero, Pi.zero_apply, sub_zero, sub_zero] at h
  exact (le_abs_self _).trans h

/-- A perturbation of norm at most `ε` moves each singular value by at most `ε`. -/
example (T E : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) (ε : ℝ)
    (hE : ‖E.toContinuousLinearMap‖ ≤ ε) (k : ℕ) :
    |(T + E).singularValues k - T.singularValues k| ≤ ε := by
  have := abs_singularValues_sub_le (T + E) T k
  rw [add_sub_cancel_left] at this
  exact this.trans hE

end MathlibExtTest.Analysis.InnerProductSpace.SingularValuePerturbation
