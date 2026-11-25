/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.Matrix.RandomizedRangeFinder

/-!
# Tests for the randomized range finder

Identity and zero samples give opposite extremes for the projection of an identity matrix.
The smallest admissible oversampling parameter gives the stated factor and tail indices.
-/

open MeasureTheory

namespace MathlibExt.LinearAlgebra.Matrix.RandomizedRangeFinderWanted.Tests

example (n : ℕ) :
    residualFrobenius (1 : Matrix (Fin n) (Fin n) ℝ) (1 : Matrix (Fin n) (Fin n) ℝ) = 0 := by
  simp [residualFrobenius, residual, Matrix.toEuclideanLin, Matrix.toLpLin_one,
    Submodule.starProjection_top]

example (n l : ℕ) :
    residualFrobenius (1 : Matrix (Fin n) (Fin n) ℝ) (0 : Matrix (Fin n) (Fin l) ℝ) =
      Real.sqrt n := by
  simp [residualFrobenius, residual, Matrix.toEuclideanLin, Matrix.toLpLin_one,
    EuclideanSpace.single, PiLp.norm_single]

example (A : Matrix (Fin 4) (Fin 4) ℝ) :
    (∫ ω, residualFrobenius A (Matrix.of fun i j => ω (i, j)) ∂gaussianMatrixLaw 4 4) ≤
      Real.sqrt 3 * Real.sqrt ((Matrix.toEuclideanLin A).singularValues 2 ^ 2 +
        (Matrix.toEuclideanLin A).singularValues 3 ^ 2) := by
  have h := integral_residualFrobenius_le (k := 2) (p := 2) (hk := by decide)
    (hp := by decide) (hkp := by decide) A
  norm_num [Finset.sum_Ico_succ_top, Finset.Ico_self] at h ⊢
  exact h

end MathlibExt.LinearAlgebra.Matrix.RandomizedRangeFinderWanted.Tests
