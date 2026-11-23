/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Planning.MotionPlanning.MinkowskiCObs
public meta import CSLibExt.Planning.MotionPlanning.MinkowskiCObs

namespace Cslib.Planning.MotionPlanning


/-- Test point: the first basis vector of the plane. -/
noncomputable def testVec : plane := EuclideanSpace.single 0 1

/-- C-obstacle membership with explicit witness: `0` collides since `0 + 0 ∈ O`. -/
theorem test_cObs_mem_zero :
    (0 : plane) ∈ cObs plane plane
      (translatePlacement plane {0, testVec}) {0} := by
  rw [mem_cObs_translatePlacement]
  exact ⟨0, by simp, by simp⟩

/-- Minkowski-side membership with explicit witnesses: `0 = 0 + -0`. -/
theorem test_minkSum_mem_zero :
    (0 : plane) ∈ minkSum plane {0} (negSet plane {0, testVec}) := by
  exact ⟨0, Set.mem_singleton 0, 0, ⟨0, by simp, by simp⟩, by simp⟩

/-- C-obstacle membership with a two-point obstacle set. -/
theorem test_cObs_mem_two_point :
    testVec ∈ cObs plane plane
      (translatePlacement plane {0, testVec}) {0, testVec} := by
  rw [mem_cObs_translatePlacement]
  exact ⟨0, by simp, by simp⟩

/-- Minkowski-side membership with a two-point obstacle set:
`testVec = testVec + -0`. -/
theorem test_minkSum_mem_two_point :
    testVec ∈ minkSum plane {0, testVec} (negSet plane {0, testVec}) := by
  exact ⟨testVec, by simp, 0, ⟨0, by simp, by simp⟩, by simp⟩

/-- Point-robot instance on the plane. -/
theorem test_point_robot :
    cObs plane plane (translatePlacement plane {0}) {0} = ({0} : Set plane) :=
  cObs_translate_singleton_zero plane {0}

/-- Point-robot membership instance on the plane. -/
theorem test_point_robot_mem :
    (0 : plane) ∈ cObs plane plane (translatePlacement plane {0}) {0} := by
  rw [test_point_robot]
  exact Set.mem_singleton 0

-- Axiom probes (scratch acceptance evidence).
#print axioms mem_cObs_translatePlacement
#print axioms mem_minkSum_neg
#print axioms cObs_translate
#print axioms cObs_translate_singleton_zero
#print axioms cFree_translate
#print axioms test_cObs_mem_zero
#print axioms test_minkSum_mem_zero
#print axioms test_cObs_mem_two_point
#print axioms test_minkSum_mem_two_point
#print axioms test_point_robot
#print axioms test_point_robot_mem

end Cslib.Planning.MotionPlanning
