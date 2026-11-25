/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Distribution.NewtonPotential

open Laplacian
open MathlibExt.Analysis.Distribution.NewtonPotentialWanted

-- Use three coordinates indexed by `Option Bool` and a point at radius two.
example :
    Δ (fun y : EuclideanSpace ℝ (Option Bool) => -1 / (4 * Real.pi * ‖y‖))
      (EuclideanSpace.single none (-2 : ℝ)) = 0 := by
  simpa [div_eq_mul_inv] using newton_potential_harmonic
    (E := EuclideanSpace ℝ (Option Bool)) (by simp) (EuclideanSpace.single none (-2 : ℝ))
    (by simp [EuclideanSpace.single])

-- The totalized potential takes its prescribed value at the origin.
example : -(4 * Real.pi * ‖(0 : EuclideanSpace ℝ (Option Bool))‖)⁻¹ = 0 := by
  simp
