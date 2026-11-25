/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicGeometry.EllipticCurve.IsWeilNumberOfRamanujan

namespace MetaMathlibExt.IsWeilNumberOfRamanujanTest

open Matrix Polynomial

/-- Applying the theorem to the `1 × 1` zero matrix with `q = 1` and
`α = Complex.I`: `Complex.I` is an algebraic integer and both roots of its
minimal polynomial have absolute value `1`. -/
example :
    IsIntegral ℤ Complex.I ∧
      ∀ β ∈ (minpoly ℚ Complex.I).aroots ℂ, ‖β‖ = Real.sqrt 1 := by
  apply MetaMathlibExt.isWeilNumber_of_ramanujan (0 : Matrix (Fin 1) (Fin 1) ℤ)
    (μ := (0 : ℂ)) (α := Complex.I) (q := 1)
  · exact Matrix.isSymm_zero
  · intro μ hμ _
    have hμ0 : μ = 0 := by simpa [Matrix.charpoly_zero] using hμ
    rw [hμ0]
    simp
  · simp [Matrix.charpoly_zero]
  · norm_num
  · simp

/-- Applying the theorem to the `1 × 1` zero matrix with `q = 0` and
`α = 0`: the degenerate case in which the only conjugate is `0` and
`√0 = 0`. -/
example :
    IsIntegral ℤ (0 : ℂ) ∧
      ∀ β ∈ (minpoly ℚ (0 : ℂ)).aroots ℂ, ‖β‖ = Real.sqrt 0 := by
  apply MetaMathlibExt.isWeilNumber_of_ramanujan (0 : Matrix (Fin 1) (Fin 1) ℤ)
    (μ := (0 : ℂ)) (α := (0 : ℂ)) (q := 0)
  · exact Matrix.isSymm_zero
  · intro μ hμ _
    have hμ0 : μ = 0 := by simpa [Matrix.charpoly_zero] using hμ
    rw [hμ0]
    simp
  · simp [Matrix.charpoly_zero]
  · norm_num
  · simp

end MetaMathlibExt.IsWeilNumberOfRamanujanTest
