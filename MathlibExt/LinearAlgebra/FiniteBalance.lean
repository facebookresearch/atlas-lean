/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Pi

/-!
# Linear balance maps

A linear functional vanishing on every column of `A` vanishes on every `A *ᵥ ξ`.

This is pure algebra: which functionals count as physically conserved quantities is supplied
separately, and no claim is made that a vector `ξ` is a chemically realizable set of reaction
extents.
-/

@[expose] public section

open scoped Matrix

namespace MathlibExt.LinearAlgebra.FiniteBalance

/-- A linear functional vanishing on every column of `A` vanishes on every real
combination of those columns, i.e. on every `A *ᵥ ξ`. -/
theorem map_mulVec_eq_zero_of_forall_col_eq_zero {κ ι : Type*} [Fintype ι]
    (φ : (κ → ℝ) →ₗ[ℝ] ℝ) (A : Matrix κ ι ℝ)
    (h : ∀ s, φ (A.col s) = 0) (ξ : ι → ℝ) :
    φ (A *ᵥ ξ) = 0 := by
  rw [Matrix.mulVec_eq_sum, map_sum]
  exact Finset.sum_eq_zero fun s _ => by
    rw [IsCentralScalar.op_smul_eq_smul, map_smul]
    change ξ s • φ (A.col s) = 0
    rw [h, smul_zero]

end MathlibExt.LinearAlgebra.FiniteBalance
