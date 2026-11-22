/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Calculus.DotProductGradient

/-!
# Tests for gradients of real functions on `ι → ℝ`

* `dotL ![1, 2]` applied to `![3, 4]` is `11`.
* The linear form `w ↦ w ⬝ᵥ x` has gradient `x`, as a Fréchet derivative on `Fin 2 → ℝ` and in
  Mathlib's `HasGradientAt` API on `EuclideanSpace ℝ (Fin 2)`.
* Its directional derivative along `v` is `v ⬝ᵥ x`.
-/

namespace MathlibExtTest.DotProductGradient

open Real

example : dotL ![(1 : ℝ), 2] ![3, 4] = 11 := by
  simp [dotProduct, Fin.sum_univ_two]
  norm_num

example (x z : Fin 2 → ℝ) :
    HasGradientAt (fun w : EuclideanSpace ℝ (Fin 2) => WithLp.ofLp w ⬝ᵥ x) (WithLp.toLp 2 x)
      (WithLp.toLp 2 z) :=
  hasGradientAt_ofLp (hasFDerivAt_dotProduct x z)

example (x z v : Fin 2 → ℝ) : HasDerivAt (fun t : ℝ => (z + t • v) ⬝ᵥ x) (v ⬝ᵥ x) 0 :=
  hasDerivAt_line_of_hasFDerivAt (hasFDerivAt_dotProduct x z) v

end MathlibExtTest.DotProductGradient
