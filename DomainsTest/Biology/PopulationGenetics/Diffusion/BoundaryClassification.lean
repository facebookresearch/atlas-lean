/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Diffusion.BoundaryClassification
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Topology.ContinuousOn

@[expose] public section

namespace MathlibExtTest.Biology.PopulationGenetics.Diffusion.BoundaryClassification

open MathlibExt.Biology.PopulationGenetics.Diffusion

example : IsExitBoundaryAtZero
    (fun x : ℝ => (0 * (1 - x) - 1 / 2 * x) / 2 + 0 * (x * (1 - x)))
    (fun x : ℝ => x * (1 - x)) (1 / 2 : ℝ) := by
  apply boundaryAtZero_selectionMutation_exit
  · norm_num [Set.mem_Ioo]
  · rfl

example : IsRegularBoundaryAtZero
    (fun x : ℝ => (1 / 2 * (1 - x) - 1 / 2 * x) / 2 + 0 * (x * (1 - x)))
    (fun x : ℝ => x * (1 - x)) (1 / 2 : ℝ) := by
  apply boundaryAtZero_selectionMutation_regular
  · norm_num [Set.mem_Ioo]
  · norm_num

example : IsEntranceBoundaryAtZero
    (fun x : ℝ => (1 * (1 - x) - 1 / 2 * x) / 2 + 0 * (x * (1 - x)))
    (fun x : ℝ => x * (1 - x)) (1 / 2 : ℝ) := by
  apply boundaryAtZero_selectionMutation_entrance
  · norm_num [Set.mem_Ioo]
  · norm_num

example : IsEntranceBoundaryAtZero
    (fun x : ℝ => (2 * (1 - x) - 1 / 2 * x) / 2 + 0 * (x * (1 - x)))
    (fun x : ℝ => x * (1 - x)) (1 / 2 : ℝ) := by
  apply boundaryAtZero_selectionMutation_entrance
  · norm_num [Set.mem_Ioo]
  · norm_num

example : IsExitBoundaryAtOne
    (fun x : ℝ => (1 / 2 * (1 - x) - 0 * x) / 2 + 0 * (x * (1 - x)))
    (fun x : ℝ => x * (1 - x)) (1 / 2 : ℝ) := by
  apply boundaryAtOne_selectionMutation_exit
  · norm_num [Set.mem_Ioo]
  · rfl

example : IsRegularBoundaryAtOne
    (fun x : ℝ => (1 / 2 * (1 - x) - 1 / 2 * x) / 2 + 0 * (x * (1 - x)))
    (fun x : ℝ => x * (1 - x)) (1 / 2 : ℝ) := by
  apply boundaryAtOne_selectionMutation_regular
  · norm_num [Set.mem_Ioo]
  · norm_num

example : IsEntranceBoundaryAtOne
    (fun x : ℝ => (1 / 2 * (1 - x) - 1 * x) / 2 + 0 * (x * (1 - x)))
    (fun x : ℝ => x * (1 - x)) (1 / 2 : ℝ) := by
  apply boundaryAtOne_selectionMutation_entrance
  · norm_num [Set.mem_Ioo]
  · norm_num

example : IsEntranceBoundaryAtOne
    (fun x : ℝ => (1 / 2 * (1 - x) - 2 * x) / 2 + 0 * (x * (1 - x)))
    (fun x : ℝ => x * (1 - x)) (1 / 2 : ℝ) := by
  apply boundaryAtOne_selectionMutation_entrance
  · norm_num [Set.mem_Ioo]
  · norm_num

example : IsRegularBoundaryAtZero (fun _ : ℝ => 0) (fun _ : ℝ => 1) (1 / 3 : ℝ) ↔
    IsRegularBoundaryAtZero (fun _ : ℝ => 0) (fun _ : ℝ => 1) (1 / 2 : ℝ) := by
  apply isRegularBoundaryAtZero_basepoint_iff
  · intro x _
    exact zero_lt_one
  · exact continuousOn_const
  · exact continuousOn_const
  · norm_num [Set.mem_Ioo]
  · norm_num [Set.mem_Ioo]

example : IsNaturalBoundaryAtOne (fun _ : ℝ => 0) (fun _ : ℝ => 1) (1 / 3 : ℝ) ↔
    IsNaturalBoundaryAtOne (fun _ : ℝ => 0) (fun _ : ℝ => 1) (1 / 2 : ℝ) := by
  apply isNaturalBoundaryAtOne_basepoint_iff
  · intro x _
    exact zero_lt_one
  · exact continuousOn_const
  · exact continuousOn_const
  · norm_num [Set.mem_Ioo]
  · norm_num [Set.mem_Ioo]

#print axioms
  MathlibExt.Biology.PopulationGenetics.Diffusion.isRegularBoundaryAtZero_basepoint_iff
#print axioms
  MathlibExt.Biology.PopulationGenetics.Diffusion.isExitBoundaryAtZero_basepoint_iff
#print axioms
  MathlibExt.Biology.PopulationGenetics.Diffusion.isEntranceBoundaryAtZero_basepoint_iff
#print axioms
  MathlibExt.Biology.PopulationGenetics.Diffusion.isNaturalBoundaryAtZero_basepoint_iff
#print axioms
  MathlibExt.Biology.PopulationGenetics.Diffusion.isRegularBoundaryAtOne_basepoint_iff
#print axioms
  MathlibExt.Biology.PopulationGenetics.Diffusion.isExitBoundaryAtOne_basepoint_iff
#print axioms
  MathlibExt.Biology.PopulationGenetics.Diffusion.isEntranceBoundaryAtOne_basepoint_iff
#print axioms
  MathlibExt.Biology.PopulationGenetics.Diffusion.isNaturalBoundaryAtOne_basepoint_iff
#print axioms
  MathlibExt.Biology.PopulationGenetics.Diffusion.boundaryAtZero_selectionMutation_exit
#print axioms
  MathlibExt.Biology.PopulationGenetics.Diffusion.boundaryAtZero_selectionMutation_regular
#print axioms
  MathlibExt.Biology.PopulationGenetics.Diffusion.boundaryAtZero_selectionMutation_entrance
#print axioms
  MathlibExt.Biology.PopulationGenetics.Diffusion.boundaryAtOne_selectionMutation_exit
#print axioms
  MathlibExt.Biology.PopulationGenetics.Diffusion.boundaryAtOne_selectionMutation_regular
#print axioms
  MathlibExt.Biology.PopulationGenetics.Diffusion.boundaryAtOne_selectionMutation_entrance

end MathlibExtTest.Biology.PopulationGenetics.Diffusion.BoundaryClassification
