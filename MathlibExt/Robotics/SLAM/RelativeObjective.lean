/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.GroupTheory.GroupAction.Basic
public import MathlibExt.Robotics.SLAM.RelativeObservation

/-!
# Observation-factorized objective gauge invariance

An objective that sums per-pair losses of the relative
observations `g⁻¹ • l i` against fixed data does not
change under a common gauge transform of all poses and
landmarks.
-/

@[expose] public section

namespace Robotics.SLAM

/-- Observation-factorized objective gauge invariance.
For finitely many observed pose-landmark pairs with fixed
data `d`, an objective that is a sum of per-pair losses of
the relative observations `(g i)⁻¹ • l i` does not change
when every pose and landmark is transformed by a common
`h`: each relative observation, and hence every summand,
is unchanged. -/
theorem objective_invariant_of_relative {G ι L D : Type*}
    [Group G] [MulAction G L] [Fintype ι]
    (g : ι → G) (h : G) (l : ι → L) (d : ι → D) (loss : L → D → ℝ) :
    (∑ i, loss ((h * g i)⁻¹ • (h • l i)) (d i))
      = ∑ i, loss ((g i)⁻¹ • l i) (d i) := by
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact relativeObservation_invariant h (g i) (l i)

end Robotics.SLAM
