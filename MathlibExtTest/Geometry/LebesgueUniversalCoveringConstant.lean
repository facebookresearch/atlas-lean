/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.LebesgueUniversalCoveringConstant
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Tests for `MathlibExt.Geometry.LebesgueUniversalCoveringConstant` -/

namespace MathlibExtTest.LebesgueUniversalCoveringConstant

open MathlibExt.Geometry.LebesgueUniversalCoveringConstantWanted

-- A closed disk of radius `1/2` is a nonempty convex set of diameter `1`.
example : IsUnitDiameterConvexSet (Metric.closedBall (0 : Plane) (1 / 2)) := by
  refine ⟨Metric.nonempty_closedBall.2 (by norm_num), convex_closedBall _ _, ?_⟩
  rw [Metric.diam_closedBall_eq _ (by norm_num)]
  norm_num

-- `planarArea` is the usual area: a closed disk of radius `1/2` has area `π/4`.
example : planarArea (Metric.closedBall (0 : Plane) (1 / 2)) = ENNReal.ofReal (Real.pi / 4) := by
  rw [planarArea, EuclideanSpace.volume_closedBall_fin_two, ← ENNReal.ofReal_pow (by norm_num),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

-- Every set covers a congruent copy of itself, through the identity isometry.
example (K : Set Plane) : CoversCongruentCopy K K := by
  refine ⟨IsometryEquiv.refl _, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact hx

-- The disk lower bound for each cover: every universal convex cover has area at least `π/4`.
example {Ω : Set Plane} (hΩ : IsUniversalConvexCover Ω) :
    ENNReal.ofReal (Real.pi / 4) ≤ planarArea Ω :=
  le_trans trivialUnitDiskLowerBound_holds (sInf_le ⟨Ω, hΩ, rfl⟩)

-- The closed disk of radius `1` about the origin is a universal convex cover: translating a
-- point of a set of diameter `1` to the origin moves the whole set into the disk.
private theorem isUniversalConvexCover_closedBall_one :
    IsUniversalConvexCover (Metric.closedBall (0 : Plane) 1) := by
  refine ⟨Metric.nonempty_closedBall.2 zero_le_one, convex_closedBall _ _, ?_⟩
  rintro K ⟨⟨p, hp⟩, -, hK⟩
  have hb : Bornology.IsBounded K := by
    by_contra h
    rw [Metric.diam_eq_zero_of_unbounded h] at hK
    exact zero_ne_one hK
  refine ⟨IsometryEquiv.subRight p, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [IsometryEquiv.subRight_apply, Metric.mem_closedBall, dist_zero_right, ← dist_eq_norm]
  exact hK ▸ Metric.dist_le_diam_of_mem hb hx hp

-- Hence the constant is finite, between `π/4` and `π`: the disk lower bound is not a statement
-- about an empty family of covers, whose infimum would be `∞`.
example : ENNReal.ofReal (Real.pi / 4) ≤ lebesgueUniversalCoveringConstant ∧
    lebesgueUniversalCoveringConstant ≤ ENNReal.ofReal Real.pi := by
  refine ⟨trivialUnitDiskLowerBound_holds, ?_⟩
  refine sInf_le_of_le ⟨_, isUniversalConvexCover_closedBall_one, rfl⟩ ?_
  simp [planarArea]

end MathlibExtTest.LebesgueUniversalCoveringConstant
