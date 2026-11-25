/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.MetricSpace.QuasiIsometry
public import Mathlib.Topology.Instances.Int
public import Mathlib.Algebra.Order.Floor.Ring

@[expose] public section

namespace MathlibExtTest.QuasiIsometry

open Metric

/-- The inclusion `ℤ → ℝ` is a `(1, 1)`-quasi-isometry: it is an isometric embedding and every real
number is within `1` of an integer. -/
theorem isQuasiIsometry_intCast : IsQuasiIsometry (fun n : ℤ => (n : ℝ)) 1 1 := by
  refine ⟨(Isometry.of_dist_eq Int.dist_cast_real).isQuasiIsometricEmbedding.mono le_rfl
    zero_le_one, fun y => ⟨⌊y⌋, ?_⟩⟩
  rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith [Int.floor_le y])]
  linarith [Int.lt_floor_add_one y]

/-- `ℤ` and `ℝ` are quasi-isometric, in both directions (non-degenerate instance of the
equivalence-relation API). -/
example : QuasiIsometric ℤ ℝ := ⟨_, _, _, isQuasiIsometry_intCast⟩

example : QuasiIsometric ℝ ℤ := QuasiIsometric.symm ⟨_, _, _, isQuasiIsometry_intCast⟩

example : QuasiIsometric ℤ ℤ :=
  QuasiIsometric.trans (Y := ℝ) ⟨_, _, _, isQuasiIsometry_intCast⟩
    (QuasiIsometric.symm ⟨_, _, _, isQuasiIsometry_intCast⟩)

/-- A quasi-inverse of `ℤ → ℝ` exists with the advertised constants. -/
example : ∃ g : ℝ → ℤ, IsQuasiIsometry g 1 (3 * 1 * 1) ∧
    (∀ y, dist ((g y : ℤ) : ℝ) y ≤ 1) ∧ ∀ x : ℤ, dist (g x) x ≤ 2 * 1 * 1 :=
  isQuasiIsometry_intCast.exists_quasiInverse

end MathlibExtTest.QuasiIsometry
