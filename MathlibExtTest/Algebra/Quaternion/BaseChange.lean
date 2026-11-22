/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Quaternion.BaseChange

@[expose] public section

open scoped TensorProduct Quaternion

namespace QuaternionAlgebra

/-- Base change from `ℤ` to `ℚ` for `ℍ[ℤ, -1, 0, -1]`, with all three
coefficient hypotheses instantiated by `simp`. -/
example :
    (QuaternionAlgebra.baseChange (R := ℤ) (S := ℚ) (c₁ := -1) (c₂ := 0)
      (c₃ := -1) (d₁ := -1) (d₂ := 0) (d₃ := -1) (by simp) (by simp) (by simp))
        ((2 : ℚ) ⊗ₜ[ℤ] (⟨0, 1, 0, 0⟩ : ℍ[ℤ, -1, 0, -1])) =
      (⟨0, 2, 0, 0⟩ : ℍ[ℚ, -1, 0, -1]) := by
  rw [QuaternionAlgebra.baseChange_tmul]
  ext <;> simp

/-- The inverse base-change map recovers a pure tensor. -/
example (q : ℍ[ℚ, -1, 0, -1]) :
    (QuaternionAlgebra.baseChange (R := ℤ) (S := ℚ) (c₁ := -1) (c₂ := 0)
      (c₃ := -1) (d₁ := -1) (d₂ := 0) (d₃ := -1) (by simp) (by simp)
      (by simp)).symm q =
      q.re ⊗ₜ[ℤ] (1 : ℍ[ℤ, -1, 0, -1]) +
        q.imI ⊗ₜ[ℤ] (⟨0, 1, 0, 0⟩ : ℍ[ℤ, -1, 0, -1]) +
        q.imJ ⊗ₜ[ℤ] (⟨0, 0, 1, 0⟩ : ℍ[ℤ, -1, 0, -1]) +
        q.imK ⊗ₜ[ℤ] (⟨0, 0, 0, 1⟩ : ℍ[ℤ, -1, 0, -1]) :=
  QuaternionAlgebra.baseChange_symm_apply _ _ _ q

end QuaternionAlgebra
