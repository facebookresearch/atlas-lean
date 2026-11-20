/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardAdaptivePatchedPlacement









namespace StatMech.FrontierA

open scoped NNReal ENNReal Convex
open Set

theorem KWFiniteSimplePolygon.singleton_vertex_disjoint_closedEdgeCore
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    {eps : ℝ} (heps : 0 < eps ∧ eps < 1 / 2)
    (v i : Fin n) :
    Disjoint ({polygon.vertex v} : Set ℂ)
      (polygon.closedEdgeCore eps i) := by
  rw [Set.disjoint_left]
  intro z hzv hzcore
  rw [Set.mem_singleton_iff] at hzv
  subst z
  have hs := polygon.closedEdgeCore_subset_edgeInterior heps i hzcore
  by_cases hvi : v = i
  · subst v
    exact hs.ne_left rfl
  by_cases hvis : v = i + 1
  · subst v
    exact hs.ne_right rfl
  exact polygon.vertex_not_strictly_between i v hvi hvis hs

private theorem exists_uniform_vertexCore_radius_finset
    {n : ℕ} [NeZero n]
    (polygon : KWFiniteSimplePolygon n) {eps : ℝ}
    (heps : 0 < eps ∧ eps < 1 / 2)
    (pairs : Finset (Fin n × Fin n)) :
    ∃ r : ℝ≥0, 0 < r ∧ ∀ p ∈ pairs,
      ∀ y ∈ polygon.closedEdgeCore eps p.2,
        (r : ℝ≥0∞) < edist (polygon.vertex p.1) y := by
  classical
  induction pairs using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert p s hp ih =>
      obtain ⟨rp, hrp, hsepP⟩ := Metric.exists_pos_forall_lt_edist
        (s := {polygon.vertex p.1})
        (t := polygon.closedEdgeCore eps p.2)
        isCompact_singleton (polygon.closedEdgeCore_isClosed eps p.2)
        (polygon.singleton_vertex_disjoint_closedEdgeCore heps p.1 p.2)
      obtain ⟨rs, hrs, hsepS⟩ := ih
      refine ⟨min rp rs, lt_min hrp hrs, ?_⟩
      intro q hq y hy
      rcases Finset.mem_insert.mp hq with rfl | hqs
      · exact (ENNReal.coe_le_coe.mpr (min_le_left _ _)).trans_lt
          (hsepP (polygon.vertex q.1) rfl y hy)
      · exact (ENNReal.coe_le_coe.mpr (min_le_right _ _)).trans_lt
          (hsepS q hqs y hy)

theorem KWFiniteSimplePolygon.exists_uniform_vertex_core_separation
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    {eps : ℝ} (heps : 0 < eps ∧ eps < 1 / 2) :
    ∃ r : ℝ≥0, 0 < r ∧
      ∀ v i : Fin n, ∀ y ∈ polygon.closedEdgeCore eps i,
        (r : ℝ) < dist (polygon.vertex v) y := by
  obtain ⟨r, hr, hsep⟩ := exists_uniform_vertexCore_radius_finset
    polygon heps Finset.univ
  refine ⟨r, hr, ?_⟩
  intro v i y hy
  have h := hsep (v, i) (Finset.mem_univ _) y hy
  rw [edist_dist] at h
  exact ENNReal.coe_lt_ofReal.mp h

theorem KWFiniteSimplePolygon.vertexBall_disjoint_closedEdgeCoreTube
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    {eps : ℝ} {r : ℝ≥0}
    (hsep : ∀ v i : Fin n, ∀ y ∈ polygon.closedEdgeCore eps i,
      (r : ℝ) < dist (polygon.vertex v) y)
    (v i : Fin n) :
    Disjoint (Metric.ball (polygon.vertex v) ((r : ℝ) / 2))
      (polygon.closedEdgeCoreTube eps (r / 2) i) := by
  rw [Set.disjoint_left]
  rintro z hz ⟨y, hy, hzy⟩
  have hvy := hsep v i y hy
  have hvz : dist (polygon.vertex v) z < (r : ℝ) / 2 :=
    Metric.mem_ball'.mp hz
  have hzy' : dist z y < (r : ℝ) / 2 := by
    simpa only [NNReal.coe_div, NNReal.coe_ofNat] using hzy
  have htriangle : dist (polygon.vertex v) y ≤
      dist (polygon.vertex v) z + dist z y := dist_triangle _ _ _
  linarith



theorem KWFiniteSimplePolygon.exists_pairwise_vertexBall_coreTube_separation
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    {eps : ℝ} (heps : 0 < eps ∧ eps < 1 / 2) :
    ∃ r : ℝ≥0, 0 < r ∧
      ∀ v i : Fin n,
        Disjoint (Metric.ball (polygon.vertex v) (r : ℝ))
          (polygon.closedEdgeCoreTube eps r i) := by
  obtain ⟨R, hR, hsep⟩ :=
    polygon.exists_uniform_vertex_core_separation heps
  refine ⟨R / 2, half_pos hR, ?_⟩
  intro v i
  simpa only [NNReal.coe_div, NNReal.coe_ofNat] using
    polygon.vertexBall_disjoint_closedEdgeCoreTube hsep v i

end StatMech.FrontierA
