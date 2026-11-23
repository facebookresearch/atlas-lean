/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Planning.MotionPlanning.TwoSquares
public meta import CSLibExt.Planning.MotionPlanning.TwoSquares
public import Mathlib.Tactic.NormNum.RealSqrt

/-!
# Two-squares visibility tests

Obstacle boundary/interior membership checks, both feasible routes exercised
through the production theorems, and axiom probes for
`CSLibExt.Planning.MotionPlanning.TwoSquares`.
-/

open EuclideanSpace Matrix WithLp Topology Filter Metric Set Cslib.Planning.MotionPlanning.PathShortening

namespace Cslib.Planning.MotionPlanning.VisibilityInstance

-- Numeric sanity checks.
example : dist s cTopL = Real.sqrt 5 / 2 := dist_s_topL
example : dist cTopL cTopR = 3 := dist_top_mid

-- A corner and an edge-midpoint of each square are in G.
example : (WithLp.toLp 2 ![(1 : ℝ), (1 : ℝ)] : plane) ∈ G := by
  apply mem_G_of_y_eq_one
  simp
example : (WithLp.toLp 2 ![(1 / 2 : ℝ), (0 : ℝ)] : plane) ∈ G := by
  apply mem_G_of_y_eq_zero
  simp
example : (WithLp.toLp 2 ![(2 : ℝ), (0 : ℝ)] : plane) ∈ G := by
  apply mem_G_of_y_eq_zero
  simp
example : (WithLp.toLp 2 ![(5 / 2 : ℝ), (1 : ℝ)] : plane) ∈ G := by
  apply mem_G_of_y_eq_one
  simp

-- Coordinate distances are bounded by the ambient distance.
lemma coord_dist_le (q c : plane) (i : Fin 2) :
    dist (q i : ℝ) (c i : ℝ) ≤ dist q c := by
  have hle : dist (q i : ℝ) (c i : ℝ) ^ 2 ≤ ∑ j, dist (q j : ℝ) (c j : ℝ) ^ 2 :=
    Finset.single_le_sum (f := fun j => dist (q j : ℝ) (c j : ℝ) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  rw [EuclideanSpace.dist_eq]
  exact Real.le_sqrt_of_sq_le hle

lemma mem_interior_union_of_ball (c : plane) (r : ℝ) (hr : 0 < r)
    (h : Metric.ball c r ⊆ O1 ∪ O2) : c ∈ interior (O1 ∪ O2) :=
  mem_interior_iff_mem_nhds.mpr (Metric.mem_nhds_iff.mpr ⟨r, hr, h⟩)

lemma not_mem_G_of_mem_interior (p : plane) (h : p ∈ interior (O1 ∪ O2)) :
    p ∉ G := by
  simp only [G, mem_compl_iff, not_not]
  exact h

-- The center of each square is not in G.
noncomputable def o1c : plane := WithLp.toLp 2 ![(1 / 2 : ℝ), (1 / 2 : ℝ)]
noncomputable def o2c : plane := WithLp.toLp 2 ![(5 / 2 : ℝ), (1 / 2 : ℝ)]

lemma o1c_ball : Metric.ball o1c (1 / 2 : ℝ) ⊆ O1 := by
  intro q hq
  rw [Metric.mem_ball] at hq
  have hc0 : (o1c 0 : ℝ) = 1 / 2 := by simp [o1c]
  have hc1 : (o1c 1 : ℝ) = 1 / 2 := by simp [o1c]
  have h0 := coord_dist_le q o1c 0
  have h1 := coord_dist_le q o1c 1
  rw [hc0, dist_eq_norm, Real.norm_eq_abs] at h0
  rw [hc1, dist_eq_norm, Real.norm_eq_abs] at h1
  have hb0 := lt_of_le_of_lt h0 hq
  have hb1 := lt_of_le_of_lt h1 hq
  rw [abs_lt] at hb0 hb1
  obtain ⟨hb0l, hb0r⟩ := hb0
  obtain ⟨hb1l, hb1r⟩ := hb1
  simp only [O1, mem_ofPred_eq]
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

lemma o1c_not_mem_G : o1c ∉ G :=
  not_mem_G_of_mem_interior o1c
    (mem_interior_union_of_ball o1c (1 / 2) (by norm_num)
      (o1c_ball.trans subset_union_left))

lemma o2c_ball : Metric.ball o2c (1 / 2 : ℝ) ⊆ O2 := by
  intro q hq
  rw [Metric.mem_ball] at hq
  have hc0 : (o2c 0 : ℝ) = 5 / 2 := by simp [o2c]
  have hc1 : (o2c 1 : ℝ) = 1 / 2 := by simp [o2c]
  have h0 := coord_dist_le q o2c 0
  have h1 := coord_dist_le q o2c 1
  rw [hc0, dist_eq_norm, Real.norm_eq_abs] at h0
  rw [hc1, dist_eq_norm, Real.norm_eq_abs] at h1
  have hb0 := lt_of_le_of_lt h0 hq
  have hb1 := lt_of_le_of_lt h1 hq
  rw [abs_lt] at hb0 hb1
  obtain ⟨hb0l, hb0r⟩ := hb0
  obtain ⟨hb1l, hb1r⟩ := hb1
  simp only [O2, mem_ofPred_eq]
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

example : o2c ∉ G :=
  not_mem_G_of_mem_interior o2c
    (mem_interior_union_of_ball o2c (1 / 2) (by norm_num)
      (o2c_ball.trans subset_union_right))

-- A point just inside O1 near its top edge is not in G; the edge point above it is.
noncomputable def o1inner : plane := WithLp.toLp 2 ![(1 / 2 : ℝ), (9 / 10 : ℝ)]

lemma o1inner_ball : Metric.ball o1inner (1 / 10 : ℝ) ⊆ O1 := by
  intro q hq
  rw [Metric.mem_ball] at hq
  have hc0 : (o1inner 0 : ℝ) = 1 / 2 := by simp [o1inner]
  have hc1 : (o1inner 1 : ℝ) = 9 / 10 := by simp [o1inner]
  have h0 := coord_dist_le q o1inner 0
  have h1 := coord_dist_le q o1inner 1
  rw [hc0, dist_eq_norm, Real.norm_eq_abs] at h0
  rw [hc1, dist_eq_norm, Real.norm_eq_abs] at h1
  have hb0 := lt_of_le_of_lt h0 hq
  have hb1 := lt_of_le_of_lt h1 hq
  rw [abs_lt] at hb0 hb1
  obtain ⟨hb0l, hb0r⟩ := hb0
  obtain ⟨hb1l, hb1r⟩ := hb1
  simp only [O1, mem_ofPred_eq]
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

example : o1inner ∉ G :=
  not_mem_G_of_mem_interior o1inner
    (mem_interior_union_of_ball o1inner (1 / 10) (by norm_num)
      (o1inner_ball.trans subset_union_left))

example : (WithLp.toLp 2 ![(1 / 2 : ℝ), (1 : ℝ)] : plane) ∈ G := by
  apply mem_G_of_y_eq_one
  simp

-- Both witness routes, through the production theorems.
example : Feasible G [s, cTopL, cTopR, t] := top_feasible
example : polyLen [s, cTopL, cTopR, t] = 3 + Real.sqrt 5 := top_length
example : Feasible G [s, cBotL, cBotR, t] := bottom_feasible
example : polyLen [s, cBotL, cBotR, t] = 3 + Real.sqrt 5 := bottom_length

-- The direct segment runs through the interior of O1, so it is not feasible.
lemma o1c_mem_segment_st : o1c ∈ segment ℝ s t := by
  rw [segment_eq_image_lineMap]
  refine ⟨3 / 10, ⟨by norm_num, by norm_num⟩, ?_⟩
  ext i
  fin_cases i
  · show ((AffineMap.lineMap s t (3 / 10)) 0 : ℝ) = (o1c 0 : ℝ)
    have hs0 : (s 0 : ℝ) = -1 := by simp [s]
    have ht0 : (t 0 : ℝ) = 4 := by simp [t]
    have ho0 : (o1c 0 : ℝ) = 1 / 2 := by simp [o1c]
    rw [lineMap_coord, hs0, ht0, ho0]
    norm_num
  · show ((AffineMap.lineMap s t (3 / 10)) 1 : ℝ) = (o1c 1 : ℝ)
    have hs1 : (s 1 : ℝ) = 1 / 2 := by simp [s]
    have ht1 : (t 1 : ℝ) = 1 / 2 := by simp [t]
    have ho1 : (o1c 1 : ℝ) = 1 / 2 := by simp [o1c]
    rw [lineMap_coord, hs1, ht1, ho1]
    norm_num

theorem direct_segment_not_feasible : ¬ (segment ℝ s t ⊆ G) := by
  intro hsub
  exact o1c_not_mem_G (hsub o1c_mem_segment_st)

#print axioms top_feasible
#print axioms top_length
#print axioms bottom_feasible
#print axioms bottom_length
#print axioms endpoints_corners_mem
#print axioms top_middle_visible
#print axioms bottom_middle_visible

end Cslib.Planning.MotionPlanning.VisibilityInstance
