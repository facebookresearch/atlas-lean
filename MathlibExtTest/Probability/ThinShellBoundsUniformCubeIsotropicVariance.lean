/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.ThinShellBoundsUniformCubeIsotropicVariance

/-!
# Tests for the isotropic cube

These examples check the two-dimensional cube's coordinate products and show that the
thin-shell variance constant is at least `4 / 5`.
-/

open MeasureTheory MathlibExt.Probability.ThinShell
open scoped ENNReal

namespace MathlibExtTest.Probability.ThinShellBoundsUniformCubeIsotropicVariance

example :
    (∫ x : EuclideanSpace ℝ (Fin 2), x 0 * x 1 ∂ProbabilityTheory.cond volume
      {x | ∀ i : Fin 2, |x i| ≤ Real.sqrt 3}) = 0 := by
  simpa using ((uniformCube_isotropic_variance 2 (by decide)).1.2.2.2 0 1).2

example : ENNReal.ofReal (4 / 5) ≤ thinShellVarianceConstant := by
  rw [← (uniformCube_isotropic_variance 2 (by decide)).2]
  exact normalizedRadiusVariance_le_constant (by decide)
    (uniformCube_isotropic_variance 2 (by decide)).1

end MathlibExtTest.Probability.ThinShellBoundsUniformCubeIsotropicVariance
