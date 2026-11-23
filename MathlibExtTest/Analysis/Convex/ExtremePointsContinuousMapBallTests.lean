/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.ExtremePointsContinuousMapBall
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for extreme points of the closed unit ball of `C(X, ℝ)`
-/

@[expose] public section

open Set Metric

namespace MathlibExt.Analysis.Convex.ExtremePointsContinuousMapBallTests

open MathlibExt.Analysis.Convex.ExtremePointsContinuousMapBall

/-- The constant function `1` on `C([0, 1], ℝ)` is an extreme point of the
closed unit ball. -/
example : (1 : C(Set.Icc (0 : ℝ) 1, ℝ)) ∈
    (Metric.closedBall (0 : C(Set.Icc (0 : ℝ) 1, ℝ)) 1).extremePoints ℝ := by
  rw [extremePoints_closedBall_continuousMap]
  intro x
  simp

/-- The constant function `-1` on `C([0, 1], ℝ)` is an extreme point of the
closed unit ball. -/
example : (-1 : C(Set.Icc (0 : ℝ) 1, ℝ)) ∈
    (Metric.closedBall (0 : C(Set.Icc (0 : ℝ) 1, ℝ)) 1).extremePoints ℝ := by
  rw [extremePoints_closedBall_continuousMap]
  intro x
  simp

/-- The constant function `1 / 2` on `C([0, 1], ℝ)` is not an extreme
point of the closed unit ball, since its value has absolute value `< 1`. -/
example : (ContinuousMap.const (Set.Icc (0 : ℝ) 1) (1 / 2 : ℝ)) ∉
    (Metric.closedBall (0 : C(Set.Icc (0 : ℝ) 1, ℝ)) 1).extremePoints ℝ := by
  rw [extremePoints_closedBall_continuousMap]
  intro h
  have h0 := h ⟨0, by norm_num⟩
  simp [ContinuousMap.const_apply] at h0

/-- The identity function on `C([0, 1], ℝ)` is not an extreme point of the
closed unit ball: it vanishes at `0`. -/
example : (⟨fun x : Set.Icc (0 : ℝ) 1 => (x : ℝ), continuous_subtype_val⟩ :
    C(Set.Icc (0 : ℝ) 1, ℝ)) ∉
    (Metric.closedBall (0 : C(Set.Icc (0 : ℝ) 1, ℝ)) 1).extremePoints ℝ := by
  rw [extremePoints_closedBall_continuousMap]
  intro h
  have h0 := h ⟨0, by norm_num⟩
  simp at h0

/-- On the two-point discrete space, the function taking the values `1`
and `-1` is an extreme point of the closed unit ball. -/
example : (⟨![1, -1], continuous_of_discreteTopology⟩ : C(Fin 2, ℝ)) ∈
    (Metric.closedBall (0 : C(Fin 2, ℝ)) 1).extremePoints ℝ := by
  rw [extremePoints_closedBall_continuousMap]
  intro i
  fin_cases i <;> simp

/-- On the two-point discrete space, the function taking the values `1`
and `1 / 2` is not an extreme point of the closed unit ball. -/
example : (⟨![1, 1 / 2], continuous_of_discreteTopology⟩ : C(Fin 2, ℝ)) ∉
    (Metric.closedBall (0 : C(Fin 2, ℝ)) 1).extremePoints ℝ := by
  rw [extremePoints_closedBall_continuousMap]
  intro h
  have h1 := h 1
  simp at h1

/-- The membership form: the constant function `1` on `C([0, 1], ℝ)`
satisfies the pointwise criterion. -/
example : ∀ x : Set.Icc (0 : ℝ) 1, |(1 : C(Set.Icc (0 : ℝ) 1, ℝ)) x| = 1 := by
  intro x
  have h : (1 : C(Set.Icc (0 : ℝ) 1, ℝ)) ∈
      (Metric.closedBall (0 : C(Set.Icc (0 : ℝ) 1, ℝ)) 1).extremePoints ℝ := by
    rw [extremePoints_closedBall_continuousMap]
    intro _
    simp
  exact (mem_extremePoints_closedBall_continuousMap.mp h) x

end MathlibExt.Analysis.Convex.ExtremePointsContinuousMapBallTests
