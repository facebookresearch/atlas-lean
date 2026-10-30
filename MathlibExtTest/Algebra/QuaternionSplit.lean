/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Quaternion.Split

open scoped Quaternion

/-- The quaternion algebra `ℍ[ℚ, 1, 1]` splits, since its norm form takes
the value `0` at `(1, 1, 0, 0)` without all entries vanishing. -/
example : Nonempty (ℍ[ℚ, 1, 1] ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℚ) :=
  QuaternionAlgebra.nonempty_algEquiv_matrix_of_normForm_eq_zero ℚ (by norm_num) 1 1
    (by norm_num) (by norm_num) 1 1 0 0 (by simp) (by norm_num)
