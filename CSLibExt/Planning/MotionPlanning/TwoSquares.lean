/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Planning.MotionPlanning.PathShortening
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Topology.Bornology.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.Data.Real.Sqrt
public import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

-- Two-square visibility witness (upper-bound half only).
-- Imports: Mathlib.
-- Plane is EuclideanSpace over Fin 2; obstacles are closed unit squares
-- O1 = [0,1]x[0,1] and O2 = [2,3]x[0,1]; free space G is the complement
-- of the interior of their union. Witnesses are the top route through
-- y = 1 and the reflected bottom route through y = 0.

open EuclideanSpace Matrix WithLp Topology Filter Metric Set


namespace Cslib.Planning.MotionPlanning.VisibilityInstance

-- Polyline API comes from the provider module (imported at integration).
open Cslib.Planning.MotionPlanning.PathShortening

-- Closed square obstacles as sets of the plane.
def O1 : Set plane :=
  {p | 0 ≤ (p 0 : ℝ) ∧ (p 0 : ℝ) ≤ 1 ∧ 0 ≤ (p 1 : ℝ) ∧ (p 1 : ℝ) ≤ 1}
def O2 : Set plane :=
  {p | 2 ≤ (p 0 : ℝ) ∧ (p 0 : ℝ) ≤ 3 ∧ 0 ≤ (p 1 : ℝ) ∧ (p 1 : ℝ) ≤ 1}

-- Free closed set: complement of the interior of the union.
def G : Set plane := (interior (O1 ∪ O2))ᶜ

-- Start, goal, and the four obstacle corners used by the witnesses.
noncomputable def s : plane := WithLp.toLp 2 ![(-1 : ℝ), (1 / 2 : ℝ)]
noncomputable def t : plane := WithLp.toLp 2 ![(4 : ℝ), (1 / 2 : ℝ)]
noncomputable def cTopL : plane := WithLp.toLp 2 ![(0 : ℝ), (1 : ℝ)]
noncomputable def cTopR : plane := WithLp.toLp 2 ![(3 : ℝ), (1 : ℝ)]
noncomputable def cBotL : plane := WithLp.toLp 2 ![(0 : ℝ), (0 : ℝ)]
noncomputable def cBotR : plane := WithLp.toLp 2 ![(3 : ℝ), (0 : ℝ)]

-- Point with its y-coordinate shifted by d.
noncomputable def perturbY (p : plane) (δ : ℝ) : plane :=
  WithLp.toLp 2 (Function.update (WithLp.ofLp p) 1 ((p 1 : ℝ) + δ))

lemma perturbY_one (p : plane) (δ : ℝ) :
    ((perturbY p δ) 1 : ℝ) = (p 1 : ℝ) + δ := by
  simp [perturbY]

lemma perturbY_dist (p : plane) (δ : ℝ) : dist (perturbY p δ) p = |δ| := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  have h0 : dist ((perturbY p δ) 0 : ℝ) (p 0 : ℝ) = 0 := by simp [perturbY]
  have h1 : dist ((perturbY p δ) 1 : ℝ) (p 1 : ℝ) = |δ| := by
    have h : ((perturbY p δ) 1 : ℝ) = (p 1 : ℝ) + δ := by simp [perturbY]
    rw [h, dist_eq_norm, Real.norm_eq_abs]
    congr 1
    ring
  rw [h0, h1]
  simp [Real.sqrt_sq_eq_abs]

-- Coordinates of an affine line interpolation.
lemma lineMap_coord (x y : plane) (t : ℝ) (i : Fin 2) :
    ((AffineMap.lineMap x y t) i : ℝ)
      = t * ((y i : ℝ) - (x i : ℝ)) + (x i : ℝ) := by
  rw [AffineMap.lineMap_apply]
  simp [vadd_eq_add, vsub_eq_sub, PiLp.add_apply, PiLp.sub_apply,
    PiLp.smul_apply, smul_eq_mul]

-- Points strictly outside the union are in G.
lemma mem_G_of_not_mem (p : plane) (h : p ∉ O1 ∪ O2) : p ∈ G := by
  simp only [G, mem_compl_iff]
  intro hinter
  exact h (interior_subset hinter)

-- Points at height 1 are boundary-or-outside points, hence in G.
lemma mem_G_of_y_eq_one (p : plane) (h1 : (p 1 : ℝ) = 1) : p ∈ G := by
  simp only [G, mem_compl_iff]
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  rintro ⟨ε, hε, hsub⟩
  have hδ : (0 : ℝ) < ε / 2 := by linarith
  set q := perturbY p (ε / 2) with hq
  have hqmem : q ∈ Metric.ball p ε := by
    rw [Metric.mem_ball, hq, perturbY_dist, abs_of_pos hδ]
    linarith
  have hqU := hsub hqmem
  have hqy : ((q 1 : ℝ)) = 1 + ε / 2 := by
    rw [hq, perturbY_one, h1]
  simp only [O1, O2, mem_union, mem_ofPred_eq] at hqU
  rcases hqU with ⟨_, _, _, hle⟩ | ⟨_, _, _, hle⟩ <;> linarith

-- Points at height 0 are boundary-or-outside points, hence in G.
lemma mem_G_of_y_eq_zero (p : plane) (h0 : (p 1 : ℝ) = 0) : p ∈ G := by
  simp only [G, mem_compl_iff]
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  rintro ⟨ε, hε, hsub⟩
  have hδ : (0 : ℝ) < ε / 2 := by linarith
  set q := perturbY p (-(ε / 2)) with hq
  have hqmem : q ∈ Metric.ball p ε := by
    rw [Metric.mem_ball, hq, perturbY_dist, abs_neg, abs_of_pos hδ]
    linarith
  have hqU := hsub hqmem
  have hqy : ((q 1 : ℝ)) = 0 - ε / 2 := by
    rw [hq, perturbY_one, h0]
    ring
  simp only [O1, O2, mem_union, mem_ofPred_eq] at hqU
  rcases hqU with ⟨_, _, hge, _⟩ | ⟨_, _, hge, _⟩ <;> linarith

-- Start and goal lie strictly outside the obstacles.
lemma s_mem_G : s ∈ G := by
  apply mem_G_of_not_mem
  simp only [O1, O2, mem_union, mem_ofPred_eq]
  have hx : (s 0 : ℝ) = -1 := by simp [s]
  rintro (⟨hge, _, _, _⟩ | ⟨hge, _, _, _⟩) <;> linarith

lemma t_mem_G : t ∈ G := by
  apply mem_G_of_not_mem
  simp only [O1, O2, mem_union, mem_ofPred_eq]
  have hx : (t 0 : ℝ) = 4 := by simp [t]
  rintro (⟨_, hle, _, _⟩ | ⟨_, hle, _, _⟩) <;> linarith

-- The four corners used are boundary points at height 0 or 1.
lemma cTopL_mem_G : cTopL ∈ G := by
  apply mem_G_of_y_eq_one
  simp [cTopL]

lemma cTopR_mem_G : cTopR ∈ G := by
  apply mem_G_of_y_eq_one
  simp [cTopR]

lemma cBotL_mem_G : cBotL ∈ G := by
  apply mem_G_of_y_eq_zero
  simp [cBotL]

lemma cBotR_mem_G : cBotR ∈ G := by
  apply mem_G_of_y_eq_zero
  simp [cBotR]

theorem endpoints_corners_mem :
    s ∈ G ∧ t ∈ G ∧ cTopL ∈ G ∧ cTopR ∈ G ∧ cBotL ∈ G ∧ cBotR ∈ G :=
  ⟨s_mem_G, t_mem_G, cTopL_mem_G, cTopR_mem_G, cBotL_mem_G, cBotR_mem_G⟩

-- Top-left slanted side: x stays at or left of 0.
lemma seg_top_left : segment ℝ s cTopL ⊆ G := by
  intro q hq
  rw [segment_eq_image_lineMap] at hq
  obtain ⟨tt, ⟨ht0, ht1⟩, rfl⟩ := hq
  have hx0 : (s 0 : ℝ) = -1 := by simp [s]
  have hx1 : (s 1 : ℝ) = 1 / 2 := by simp [s]
  have hy0 : (cTopL 0 : ℝ) = 0 := by simp [cTopL]
  have hy1 : (cTopL 1 : ℝ) = 1 := by simp [cTopL]
  have hq0 : ((AffineMap.lineMap s cTopL tt) 0 : ℝ) = tt - 1 := by
    rw [lineMap_coord, hx0, hy0]
    ring
  have hq1 : ((AffineMap.lineMap s cTopL tt) 1 : ℝ) = 1 / 2 + tt / 2 := by
    rw [lineMap_coord, hx1, hy1]
    ring
  have hle : ((AffineMap.lineMap s cTopL tt) 0 : ℝ) ≤ 0 := by linarith
  rcases lt_or_eq_of_le hle with hlt | heq
  · apply mem_G_of_not_mem
    simp only [O1, O2, mem_union, mem_ofPred_eq]
    rintro (⟨hge, _, _, _⟩ | ⟨hge, _, _, _⟩) <;> linarith
  · have htt : tt = 1 := by linarith
    have hy : ((AffineMap.lineMap s cTopL tt) 1 : ℝ) = 1 := by
      rw [hq1, htt]
      norm_num
    exact mem_G_of_y_eq_one _ hy

-- Horizontal top middle: the whole segment sits at height 1.
theorem top_middle_visible : segment ℝ cTopL cTopR ⊆ G := by
  intro q hq
  rw [segment_eq_image_lineMap] at hq
  obtain ⟨tt, ⟨ht0, ht1⟩, rfl⟩ := hq
  have hx1 : (cTopL 1 : ℝ) = 1 := by simp [cTopL]
  have hy1 : (cTopR 1 : ℝ) = 1 := by simp [cTopR]
  have hq1 : ((AffineMap.lineMap cTopL cTopR tt) 1 : ℝ) = 1 := by
    rw [lineMap_coord, hx1, hy1]
    ring
  exact mem_G_of_y_eq_one _ hq1

-- Top-right slanted side: x stays at or right of 3.
lemma seg_top_right : segment ℝ cTopR t ⊆ G := by
  intro q hq
  rw [segment_eq_image_lineMap] at hq
  obtain ⟨tt, ⟨ht0, ht1⟩, rfl⟩ := hq
  have hx0 : (cTopR 0 : ℝ) = 3 := by simp [cTopR]
  have hx1 : (cTopR 1 : ℝ) = 1 := by simp [cTopR]
  have hy0 : (t 0 : ℝ) = 4 := by simp [t]
  have hy1 : (t 1 : ℝ) = 1 / 2 := by simp [t]
  have hq0 : ((AffineMap.lineMap cTopR t tt) 0 : ℝ) = 3 + tt := by
    rw [lineMap_coord, hx0, hy0]
    ring
  have hq1 : ((AffineMap.lineMap cTopR t tt) 1 : ℝ) = 1 - tt / 2 := by
    rw [lineMap_coord, hx1, hy1]
    ring
  have hge : (3 : ℝ) ≤ ((AffineMap.lineMap cTopR t tt) 0 : ℝ) := by linarith
  rcases eq_or_lt_of_le hge with heq | hlt
  · have htt : tt = 0 := by linarith
    have hy : ((AffineMap.lineMap cTopR t tt) 1 : ℝ) = 1 := by
      rw [hq1, htt]
      norm_num
    exact mem_G_of_y_eq_one _ hy
  · apply mem_G_of_not_mem
    simp only [O1, O2, mem_union, mem_ofPred_eq]
    rintro (⟨_, hle, _, _⟩ | ⟨_, hle, _, _⟩) <;> linarith

-- Bottom-left slanted side: x stays at or left of 0.
lemma seg_bot_left : segment ℝ s cBotL ⊆ G := by
  intro q hq
  rw [segment_eq_image_lineMap] at hq
  obtain ⟨tt, ⟨ht0, ht1⟩, rfl⟩ := hq
  have hx0 : (s 0 : ℝ) = -1 := by simp [s]
  have hx1 : (s 1 : ℝ) = 1 / 2 := by simp [s]
  have hy0 : (cBotL 0 : ℝ) = 0 := by simp [cBotL]
  have hy1 : (cBotL 1 : ℝ) = 0 := by simp [cBotL]
  have hq0 : ((AffineMap.lineMap s cBotL tt) 0 : ℝ) = tt - 1 := by
    rw [lineMap_coord, hx0, hy0]
    ring
  have hq1 : ((AffineMap.lineMap s cBotL tt) 1 : ℝ) = 1 / 2 - tt / 2 := by
    rw [lineMap_coord, hx1, hy1]
    ring
  have hle : ((AffineMap.lineMap s cBotL tt) 0 : ℝ) ≤ 0 := by linarith
  rcases lt_or_eq_of_le hle with hlt | heq
  · apply mem_G_of_not_mem
    simp only [O1, O2, mem_union, mem_ofPred_eq]
    rintro (⟨hge, _, _, _⟩ | ⟨hge, _, _, _⟩) <;> linarith
  · have htt : tt = 1 := by linarith
    have hy : ((AffineMap.lineMap s cBotL tt) 1 : ℝ) = 0 := by
      rw [hq1, htt]
      norm_num
    exact mem_G_of_y_eq_zero _ hy

-- Horizontal bottom middle: the whole segment sits at height 0.
theorem bottom_middle_visible : segment ℝ cBotL cBotR ⊆ G := by
  intro q hq
  rw [segment_eq_image_lineMap] at hq
  obtain ⟨tt, ⟨ht0, ht1⟩, rfl⟩ := hq
  have hx1 : (cBotL 1 : ℝ) = 0 := by simp [cBotL]
  have hy1 : (cBotR 1 : ℝ) = 0 := by simp [cBotR]
  have hq1 : ((AffineMap.lineMap cBotL cBotR tt) 1 : ℝ) = 0 := by
    rw [lineMap_coord, hx1, hy1]
    ring
  exact mem_G_of_y_eq_zero _ hq1

-- Bottom-right slanted side: x stays at or right of 3.
lemma seg_bot_right : segment ℝ cBotR t ⊆ G := by
  intro q hq
  rw [segment_eq_image_lineMap] at hq
  obtain ⟨tt, ⟨ht0, ht1⟩, rfl⟩ := hq
  have hx0 : (cBotR 0 : ℝ) = 3 := by simp [cBotR]
  have hx1 : (cBotR 1 : ℝ) = 0 := by simp [cBotR]
  have hy0 : (t 0 : ℝ) = 4 := by simp [t]
  have hy1 : (t 1 : ℝ) = 1 / 2 := by simp [t]
  have hq0 : ((AffineMap.lineMap cBotR t tt) 0 : ℝ) = 3 + tt := by
    rw [lineMap_coord, hx0, hy0]
    ring
  have hq1 : ((AffineMap.lineMap cBotR t tt) 1 : ℝ) = tt / 2 := by
    rw [lineMap_coord, hx1, hy1]
    ring
  have hge : (3 : ℝ) ≤ ((AffineMap.lineMap cBotR t tt) 0 : ℝ) := by linarith
  rcases eq_or_lt_of_le hge with heq | hlt
  · have htt : tt = 0 := by linarith
    have hy : ((AffineMap.lineMap cBotR t tt) 1 : ℝ) = 0 := by
      rw [hq1, htt]
      norm_num
    exact mem_G_of_y_eq_zero _ hy
  · apply mem_G_of_not_mem
    simp only [O1, O2, mem_union, mem_ofPred_eq]
    rintro (⟨_, hle, _, _⟩ | ⟨_, hle, _, _⟩) <;> linarith

-- Edge lengths of the two witness routes.
lemma dist_s_topL : dist s cTopL = Real.sqrt 5 / 2 := by
  rw [EuclideanSpace.dist_eq]
  simp only [s, cTopL, WithLp.ofLp_toLp]
  rw [Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num [dist_eq_norm, Real.sq_sqrt]

lemma dist_top_mid : dist cTopL cTopR = 3 := by
  rw [EuclideanSpace.dist_eq]
  simp only [cTopL, cTopR, WithLp.ofLp_toLp]
  rw [Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num [dist_eq_norm, Real.sq_sqrt]

lemma dist_topR_t : dist cTopR t = Real.sqrt 5 / 2 := by
  rw [EuclideanSpace.dist_eq]
  simp only [cTopR, t, WithLp.ofLp_toLp]
  rw [Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num [dist_eq_norm, Real.sq_sqrt]

lemma dist_s_botL : dist s cBotL = Real.sqrt 5 / 2 := by
  rw [EuclideanSpace.dist_eq]
  simp only [s, cBotL, WithLp.ofLp_toLp]
  rw [Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num [dist_eq_norm, Real.sq_sqrt]

lemma dist_bot_mid : dist cBotL cBotR = 3 := by
  rw [EuclideanSpace.dist_eq]
  simp only [cBotL, cBotR, WithLp.ofLp_toLp]
  rw [Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num [dist_eq_norm, Real.sq_sqrt]

lemma dist_botR_t : dist cBotR t = Real.sqrt 5 / 2 := by
  rw [EuclideanSpace.dist_eq]
  simp only [cBotR, t, WithLp.ofLp_toLp]
  rw [Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num [dist_eq_norm, Real.sq_sqrt]

-- Witness routes.
theorem top_feasible : Feasible G [s, cTopL, cTopR, t] := by
  simp only [Feasible]
  exact ⟨seg_top_left, top_middle_visible, seg_top_right, t_mem_G⟩

theorem top_length : polyLen [s, cTopL, cTopR, t] = 3 + Real.sqrt 5 := by
  have h1 := dist_s_topL
  have h2 := dist_top_mid
  have h3 := dist_topR_t
  simp only [polyLen] at ⊢
  linarith

theorem bottom_feasible : Feasible G [s, cBotL, cBotR, t] := by
  simp only [Feasible]
  exact ⟨seg_bot_left, bottom_middle_visible, seg_bot_right, t_mem_G⟩

theorem bottom_length : polyLen [s, cBotL, cBotR, t] = 3 + Real.sqrt 5 := by
  have h1 := dist_s_botL
  have h2 := dist_bot_mid
  have h3 := dist_botR_t
  simp only [polyLen] at ⊢
  linarith

end Cslib.Planning.MotionPlanning.VisibilityInstance
