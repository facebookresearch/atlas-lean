/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.ConvexProjection
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Tests for the convex-set nearest-point projection

* On `Set.Icc 0 1` in `ℝ`: the projection of `2` is `1` and the projection
  of `-1` is `0`.
* On the closed unit ball in `ℝ`: the projection fixes `1 / 2`.
* The `∃!` form, the variational inequality, idempotence, the Lipschitz
  bound, and firm nonexpansiveness, including numeric checks.
* Generic-space checks: membership, the variational inequality,
  idempotence, and the Lipschitz bound in an arbitrary real inner product
  space.
-/

open Set Filter Topology
open scoped InnerProductSpace
open MathlibExt.Analysis.InnerProductSpace.ConvexProjection

namespace MathlibExtTest.Analysis.InnerProductSpace.ConvexProjectionTests

private theorem iInf_norm_sub_Icc_eq_of_le_zero {a : ℝ} (ha : a ≤ 0) :
    ⨅ w : Set.Icc (0 : ℝ) 1, ‖a - (w : ℝ)‖ = -a := by
  have : Nonempty ↥(Set.Icc (0 : ℝ) 1) := ⟨⟨0, by norm_num [Set.mem_Icc]⟩⟩
  apply le_antisymm
  · have h : (⨅ w : ↥(Set.Icc (0 : ℝ) 1), ‖a - (w : ℝ)‖)
        ≤ ‖a - ((⟨0, by norm_num [Set.mem_Icc]⟩ : ↥(Set.Icc (0 : ℝ) 1)) : ℝ)‖ :=
      ciInf_le (f := fun w : ↥(Set.Icc (0 : ℝ) 1) => ‖a - (w : ℝ)‖)
        ⟨0, Set.forall_mem_range.2 fun w => norm_nonneg _⟩
        ⟨0, by norm_num [Set.mem_Icc]⟩
    simpa [Real.norm_eq_abs, abs_of_nonpos ha] using h
  · apply le_ciInf
    intro w
    have hw0 : (0 : ℝ) ≤ (w : ℝ) := (Set.mem_Icc.mp w.2).1
    rw [Real.norm_eq_abs, abs_of_nonpos (by linarith : a - (w : ℝ) ≤ 0)]
    linarith

private theorem iInf_norm_sub_Icc_eq_of_one_le {a : ℝ} (ha : 1 ≤ a) :
    ⨅ w : Set.Icc (0 : ℝ) 1, ‖a - (w : ℝ)‖ = a - 1 := by
  have : Nonempty ↥(Set.Icc (0 : ℝ) 1) := ⟨⟨0, by norm_num [Set.mem_Icc]⟩⟩
  apply le_antisymm
  · have h : (⨅ w : ↥(Set.Icc (0 : ℝ) 1), ‖a - (w : ℝ)‖)
        ≤ ‖a - ((⟨1, by norm_num [Set.mem_Icc]⟩ : ↥(Set.Icc (0 : ℝ) 1)) : ℝ)‖ :=
      ciInf_le (f := fun w : ↥(Set.Icc (0 : ℝ) 1) => ‖a - (w : ℝ)‖)
        ⟨0, Set.forall_mem_range.2 fun w => norm_nonneg _⟩
        ⟨1, by norm_num [Set.mem_Icc]⟩
    simpa [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ a - 1)] using h
  · apply le_ciInf
    intro w
    have hw1 : (w : ℝ) ≤ 1 := (Set.mem_Icc.mp w.2).2
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ a - (w : ℝ))]
    linarith

/-- The `∃!` form on `Set.Icc 0 1` at `2`. -/
example :
    ∃! p, p ∈ Set.Icc (0 : ℝ) 1 ∧
      ‖(2 : ℝ) - p‖ = ⨅ w : Set.Icc (0 : ℝ) 1, ‖(2 : ℝ) - w‖ := by
  apply exists_unique_nearest_point_of_complete_convex
  · exact Set.nonempty_Icc.mpr zero_le_one
  · exact isClosed_Icc.isComplete
  · exact convex_Icc 0 1

/-- The projection of `2` onto `Set.Icc 0 1` is `1`. -/
private theorem convexProjection_Icc_two :
    convexProjection (Set.Icc (0 : ℝ) 1) 2 = 1 := by
  have hKne : (Set.Icc (0 : ℝ) 1).Nonempty := Set.nonempty_Icc.mpr zero_le_one
  have hKc : IsComplete (Set.Icc (0 : ℝ) 1) := isClosed_Icc.isComplete
  have hKv : Convex ℝ (Set.Icc (0 : ℝ) 1) := convex_Icc 0 1
  refine convexProjection_eq_of_isNearestPoint hKne hKc hKv (p := 1)
    (by norm_num [Set.mem_Icc]) ?_
  rw [iInf_norm_sub_Icc_eq_of_one_le (by norm_num : (1 : ℝ) ≤ 2)]
  norm_num

/-- The projection of `-1` onto `Set.Icc 0 1` is `0`. -/
private theorem convexProjection_Icc_neg_one :
    convexProjection (Set.Icc (0 : ℝ) 1) (-1) = 0 := by
  have hKne : (Set.Icc (0 : ℝ) 1).Nonempty := Set.nonempty_Icc.mpr zero_le_one
  have hKc : IsComplete (Set.Icc (0 : ℝ) 1) := isClosed_Icc.isComplete
  have hKv : Convex ℝ (Set.Icc (0 : ℝ) 1) := convex_Icc 0 1
  refine convexProjection_eq_of_isNearestPoint hKne hKc hKv (p := 0)
    (by norm_num [Set.mem_Icc]) ?_
  rw [iInf_norm_sub_Icc_eq_of_le_zero (by norm_num : (-1 : ℝ) ≤ 0)]
  norm_num

/-- The projection onto the closed unit ball fixes `1 / 2`. -/
example : convexProjection (Metric.closedBall (0 : ℝ) 1) (1 / 2) = 1 / 2 := by
  have hKne : (Metric.closedBall (0 : ℝ) 1).Nonempty :=
    ⟨0, by simp [Metric.mem_closedBall]⟩
  have hKc : IsComplete (Metric.closedBall (0 : ℝ) 1) :=
    Metric.isClosed_closedBall.isComplete
  have hKv : Convex ℝ (Metric.closedBall (0 : ℝ) 1) := convex_closedBall 0 1
  exact convexProjection_eq_self_of_mem hKne hKc hKv (by norm_num [Metric.mem_closedBall, dist_eq_norm])

/-- Variational inequality, numerically: `⟪2 - 1, 1 / 2 - 1⟫ = -1 / 2 ≤ 0`. -/
example :
    ⟪(2 : ℝ) - convexProjection (Set.Icc (0 : ℝ) 1) 2,
      (1 / 2 : ℝ) - convexProjection (Set.Icc (0 : ℝ) 1) 2⟫_ℝ ≤ 0 := by
  have hKne : (Set.Icc (0 : ℝ) 1).Nonempty := Set.nonempty_Icc.mpr zero_le_one
  have hKc : IsComplete (Set.Icc (0 : ℝ) 1) := isClosed_Icc.isComplete
  have hKv : Convex ℝ (Set.Icc (0 : ℝ) 1) := convex_Icc 0 1
  have h := convexProjection_variational hKne hKc hKv (2 : ℝ) (1 / 2)
    (by norm_num [Set.mem_Icc])
  rw [convexProjection_Icc_two] at h ⊢
  exact h

/-- Idempotence on `Set.Icc 0 1` at `2`. -/
example : convexProjection (Set.Icc (0 : ℝ) 1)
    (convexProjection (Set.Icc (0 : ℝ) 1) 2)
      = convexProjection (Set.Icc (0 : ℝ) 1) 2 := by
  have hKne : (Set.Icc (0 : ℝ) 1).Nonempty := Set.nonempty_Icc.mpr zero_le_one
  have hKc : IsComplete (Set.Icc (0 : ℝ) 1) := isClosed_Icc.isComplete
  have hKv : Convex ℝ (Set.Icc (0 : ℝ) 1) := convex_Icc 0 1
  exact convexProjection_idem hKne hKc hKv 2

/-- Lipschitz bound, numerically: `dist 1 0 = 1 ≤ 3 = dist 2 (-1)`. -/
example : dist (convexProjection (Set.Icc (0 : ℝ) 1) 2)
    (convexProjection (Set.Icc (0 : ℝ) 1) (-1)) ≤ dist (2 : ℝ) (-1) := by
  have hKne : (Set.Icc (0 : ℝ) 1).Nonempty := Set.nonempty_Icc.mpr zero_le_one
  have hKc : IsComplete (Set.Icc (0 : ℝ) 1) := isClosed_Icc.isComplete
  have hKv : Convex ℝ (Set.Icc (0 : ℝ) 1) := convex_Icc 0 1
  have h := (lipschitzWith_convexProjection hKne hKc hKv).dist_le_mul 2 (-1)
  rw [convexProjection_Icc_two, convexProjection_Icc_neg_one] at h ⊢
  simpa using h

/-- Firm nonexpansiveness, numerically: `1 + 4 ≤ 9`. -/
example :
    ‖convexProjection (Set.Icc (0 : ℝ) 1) 2
        - convexProjection (Set.Icc (0 : ℝ) 1) (-1)‖ ^ 2 +
      ‖((2 : ℝ) - convexProjection (Set.Icc (0 : ℝ) 1) 2)
        - ((-1 : ℝ) - convexProjection (Set.Icc (0 : ℝ) 1) (-1))‖ ^ 2
      ≤ ‖(2 : ℝ) - (-1)‖ ^ 2 := by
  have hKne : (Set.Icc (0 : ℝ) 1).Nonempty := Set.nonempty_Icc.mpr zero_le_one
  have hKc : IsComplete (Set.Icc (0 : ℝ) 1) := isClosed_Icc.isComplete
  have hKv : Convex ℝ (Set.Icc (0 : ℝ) 1) := convex_Icc 0 1
  have h := convexProjection_firmly_nonexpansive hKne hKc hKv (2 : ℝ) (-1)
  rw [convexProjection_Icc_two, convexProjection_Icc_neg_one] at h ⊢
  exact h

/-- Generic-space check: membership, the variational inequality, and
idempotence in an arbitrary real inner product space. -/
example {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {K : Set F} (hKne : K.Nonempty) (hKc : IsComplete K) (hKv : Convex ℝ K)
    (x : F) :
    convexProjection K x ∈ K ∧
      (∀ w ∈ K, ⟪x - convexProjection K x, w - convexProjection K x⟫_ℝ ≤ 0) ∧
      convexProjection K (convexProjection K x) = convexProjection K x :=
  ⟨convexProjection_mem hKne hKc hKv x,
    convexProjection_variational hKne hKc hKv x,
    convexProjection_idem hKne hKc hKv x⟩

/-- Generic-space check: the projection is `1`-Lipschitz. -/
example {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {K : Set F} (hKne : K.Nonempty) (hKc : IsComplete K) (hKv : Convex ℝ K)
    (x y : F) :
    dist (convexProjection K x) (convexProjection K y) ≤ dist x y := by
  have h := (lipschitzWith_convexProjection hKne hKc hKv).dist_le_mul x y
  simpa using h

end MathlibExtTest.Analysis.InnerProductSpace.ConvexProjectionTests
