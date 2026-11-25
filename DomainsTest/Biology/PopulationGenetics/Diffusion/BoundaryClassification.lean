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
open MathlibExt.Probability.Diffusion

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

-- The selection-mutation coefficients satisfy the standing hypotheses at an interior basepoint.
example : IsFellerAdmissible
    (fun x : ℝ => (1 / 2 * (1 - x) - 1 / 2 * x) / 2 + 0 * (x * (1 - x)))
    (fun x : ℝ => x * (1 - x)) (1 / 2 : ℝ) :=
  isFellerAdmissible_selectionMutation 0 (1 / 2) (1 / 2) (1 / 2) (by norm_num [Set.mem_Ioo])

-- An endpoint basepoint is rejected, although `Ioo 0 0` and `Ioo 1 1` are empty.
example : ¬ IsRegularBoundaryAtZero
    (fun x : ℝ => (1 / 2 * (1 - x) - 1 / 2 * x) / 2 + 0 * (x * (1 - x)))
    (fun x : ℝ => x * (1 - x)) 0 :=
  fun h => lt_irrefl 0 h.1.mem_Ioo.1

example : ¬ IsRegularBoundaryAtOne
    (fun x : ℝ => (1 / 2 * (1 - x) - 1 / 2 * x) / 2 + 0 * (x * (1 - x)))
    (fun x : ℝ => x * (1 - x)) 1 :=
  fun h => lt_irrefl 1 h.1.mem_Ioo.2

#print axioms
  MathlibExt.Biology.PopulationGenetics.Diffusion.isFellerAdmissible_selectionMutation
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
