/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.ControlTheory.Unicycle
import Mathlib.Analysis.Calculus.Deriv.Mul

open ControlTheory

-- Heading `Real.pi / 2` with speed `3`: the trace `x = 0`,
-- `y = 3t` satisfies the unicycle equations at `t = 0`,
-- and the lateral velocity vanishes.
example :
    -Real.sin (Real.pi / 2) * (3 * Real.cos (Real.pi / 2))
      + Real.cos (Real.pi / 2) * (3 * Real.sin (Real.pi / 2)) = 0 :=
  unicycle_no_lateral_velocity (x := fun _ : ℝ => (0 : ℝ)) (y := fun t : ℝ => 3 * t)
    (θ := fun _ : ℝ => Real.pi / 2) (t := 0) (v := 3)
    (by
      have hz : (3 : ℝ) * Real.cos (Real.pi / 2) = 0 := by simp
      rw [hz]
      exact hasDerivAt_const (0 : ℝ) (0 : ℝ))
    (by
      have hs : (3 : ℝ) * Real.sin (Real.pi / 2) = 3 := by simp
      rw [hs]
      have h := HasDerivAt.const_mul (3 : ℝ) (hasDerivAt_id (0 : ℝ))
      simpa using h)

-- Zero speed: constant traces satisfy the equations for
-- any heading, and the lateral velocity vanishes.
example :
    -Real.sin ((fun _ : ℝ => (0 : ℝ)) 1) * (0 * Real.cos ((fun _ : ℝ => (0 : ℝ)) 1))
      + Real.cos ((fun _ : ℝ => (0 : ℝ)) 1) * (0 * Real.sin ((fun _ : ℝ => (0 : ℝ)) 1)) = 0 :=
  unicycle_no_lateral_velocity (x := fun _ : ℝ => (0 : ℝ)) (y := fun _ : ℝ => (0 : ℝ))
    (θ := fun _ : ℝ => (0 : ℝ)) (t := 1) (v := 0)
    (by
      have hz : (0 : ℝ) * Real.cos (0 : ℝ) = 0 := by simp
      rw [hz]
      exact hasDerivAt_const (1 : ℝ) (0 : ℝ))
    (by
      have hz : (0 : ℝ) * Real.sin (0 : ℝ) = 0 := by simp
      rw [hz]
      exact hasDerivAt_const (1 : ℝ) (0 : ℝ))

-- Negative speed at heading `Real.pi / 2`: the trace `x = 0`,
-- `y = -3t` satisfies the equations, and the lateral
-- velocity still vanishes.
example :
    -Real.sin (Real.pi / 2) * (-3 * Real.cos (Real.pi / 2))
      + Real.cos (Real.pi / 2) * (-3 * Real.sin (Real.pi / 2)) = 0 :=
  unicycle_no_lateral_velocity (x := fun _ : ℝ => (0 : ℝ)) (y := fun t : ℝ => -3 * t)
    (θ := fun _ : ℝ => Real.pi / 2) (t := 0) (v := -3)
    (by
      have hz : (-3 : ℝ) * Real.cos (Real.pi / 2) = 0 := by simp
      rw [hz]
      exact hasDerivAt_const (0 : ℝ) (0 : ℝ))
    (by
      have hs : (-3 : ℝ) * Real.sin (Real.pi / 2) = -3 := by simp
      rw [hs]
      have h := HasDerivAt.const_mul (-3 : ℝ) (hasDerivAt_id (0 : ℝ))
      simpa using h)

#print axioms unicycle_no_lateral_velocity
