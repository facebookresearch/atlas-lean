/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Planning.MotionPlanning.MinkowskiCObs
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace CSLibExtTest.Planning.MotionPlanning

open Cslib.Planning.MotionPlanning Pointwise


/-- Test point: the first basis vector of the plane. -/
noncomputable def testVec : plane := EuclideanSpace.single 0 1

/-- C-obstacle membership with explicit witness: `0` collides since `0 + 0 ∈ O`. -/
theorem test_cObs_mem_zero :
    (0 : plane) ∈ cObs plane plane
      (translatePlacement plane {0, testVec}) {0} := by
  rw [mem_cObs_translatePlacement]
  exact ⟨0, by simp, by simp⟩

/-- Pointwise-side membership with explicit witnesses: `0 = 0 + -0`. -/
theorem test_pointwise_mem_zero :
    (0 : plane) ∈ ({0} : Set plane) + (-({0, testVec} : Set plane)) := by
  exact ⟨0, Set.mem_singleton 0, 0, by simp, by simp⟩

/-- C-obstacle membership with a two-point obstacle set. -/
theorem test_cObs_mem_two_point :
    testVec ∈ cObs plane plane
      (translatePlacement plane {0, testVec}) {0, testVec} := by
  rw [mem_cObs_translatePlacement]
  exact ⟨0, by simp, by simp⟩

/-- Pointwise-side membership with a two-point obstacle set:
`testVec = testVec + -0`. -/
theorem test_pointwise_mem_two_point :
    testVec ∈ ({0, testVec} : Set plane) + (-({0, testVec} : Set plane)) := by
  exact ⟨testVec, by simp, 0, by simp, by simp⟩

/-- Point-robot instance on the plane. -/
theorem test_point_robot :
    cObs plane plane (translatePlacement plane {0}) {0} = ({0} : Set plane) :=
  cObs_translate_singleton_zero plane {0}

/-- Point-robot membership instance on the plane. -/
theorem test_point_robot_mem :
    (0 : plane) ∈ cObs plane plane (translatePlacement plane {0}) {0} := by
  rw [test_point_robot]
  exact Set.mem_singleton 0

/-- Sign-sensitive membership over `ℝ`: `-1 = 0 + (-1)`, so `-1` collides. -/
theorem test_sign_mem_neg_one :
    (-1 : ℝ) ∈ cObs ℝ ℝ (translatePlacement ℝ {1}) {0} := by
  rw [mem_cObs_translatePlacement]
  exact ⟨1, by simp, by simp⟩

/-- Sign-sensitive non-membership over `ℝ`: `1 + 1 ≠ 0`, so `1` is free. -/
theorem test_sign_notmem_one :
    (1 : ℝ) ∉ cObs ℝ ℝ (translatePlacement ℝ {1}) {0} := by
  rw [mem_cObs_translatePlacement]
  rintro ⟨a, ha, hy⟩
  simp only [Set.mem_singleton_iff] at ha hy
  rw [ha] at hy
  norm_num at hy

-- Axiom probes (scratch acceptance evidence).
#print axioms mem_cObs_translatePlacement
#print axioms cObs_translate
#print axioms cObs_translate_singleton_zero
#print axioms cFree_translate
#print axioms test_cObs_mem_zero
#print axioms test_pointwise_mem_zero
#print axioms test_cObs_mem_two_point
#print axioms test_pointwise_mem_two_point
#print axioms test_point_robot
#print axioms test_point_robot_mem
#print axioms test_sign_mem_neg_one
#print axioms test_sign_notmem_one

end CSLibExtTest.Planning.MotionPlanning
