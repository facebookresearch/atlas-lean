/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.MetricSpace.TreeCoding
public import Mathlib.Topology.Algebra.Order.Group

/-!
# Tests for real trees coded by functions

Boundary cases of the coding: a constant function codes a single point (all distances `0`), the
identity codes the real line (`d(s, t) = |s - t|`), and `|x|` codes a tree in which `-1` and `1`
are at distance `2` through the root `0`; and non-vacuity of `0`-hyperbolicity and of the
Lipschitz bound.
-/

open Set

namespace MathlibExtTest.Topology.MetricSpace.TreeCoding

open MathlibExt.TreeCoding

/-- A constant function codes a single point. -/
example (c s t : ℝ) : treeDist (fun _ ↦ c) s t = 0 := by
  have h : treeMin (fun _ : ℝ ↦ c) s t = c :=
    le_antisymm (treeMin_le_left continuous_const s t) (le_treeMin fun _ _ ↦ le_rfl)
  simp [treeDist, h]
  ring

/-- The identity codes the real line: `d_id(s, t) = |s - t|`. -/
example (s t : ℝ) : treeDist id s t = |s - t| := by
  have h : treeMin id s t = min s t := by
    refine le_antisymm (treeMin_le continuous_id ⟨le_rfl, min_le_max⟩)
      (le_treeMin fun x hx ↦ hx.1)
  simp only [treeDist, h, id]
  rcases le_total s t with hst | hst
  · rw [min_eq_left hst, abs_of_nonpos (by linarith)]
    ring
  · rw [min_eq_right hst, abs_of_nonneg (by linarith)]
    ring

/-- Under `|x|`, the points `-1` and `1` are at distance `2` (the path goes through `0`). -/
example : treeDist (fun x : ℝ ↦ |x|) (-1) 1 = 2 := by
  have h : treeMin (fun x : ℝ ↦ |x|) (-1) 1 = 0 :=
    le_antisymm
      ((treeMin_le (g := fun x : ℝ ↦ |x|) continuous_abs (s := -1) (t := 1) (x := 0)
        (by rw [uIcc_of_le (by norm_num)]; norm_num)).trans_eq abs_zero)
      (le_treeMin fun x _ ↦ abs_nonneg x)
  simp [treeDist, h]
  norm_num

/-- Non-vacuity: the tree coded by `|x|` is `0`-hyperbolic. -/
example : haveI : Fact (Continuous fun x : ℝ ↦ |x|) := ⟨continuous_abs⟩
    Metric.IsDeltaHyperbolic (CodedTree fun x : ℝ ↦ |x|) 0 := by
  have : Fact (Continuous fun x : ℝ ↦ |x|) := ⟨continuous_abs⟩
  exact isDeltaHyperbolic_zero _

/-- The Lipschitz bound between `|x|` and `|x| + 1/2`, which differ by `1/2` everywhere. -/
example (s t : ℝ) :
    |treeDist (fun x : ℝ ↦ |x|) s t - treeDist (fun x : ℝ ↦ |x| + 1 / 2) s t| ≤ 4 * (1 / 2) :=
  abs_treeDist_sub_le continuous_abs (continuous_abs.add continuous_const)
    (fun x ↦ by norm_num) s t

end MathlibExtTest.Topology.MetricSpace.TreeCoding
