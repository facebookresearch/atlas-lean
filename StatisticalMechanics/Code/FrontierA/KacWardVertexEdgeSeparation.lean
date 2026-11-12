/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardRectilinearSeparation








namespace StatMech.FrontierA

open scoped NNReal ENNReal Convex
open Set



def KWVertexEdgeNonincident {n : ℕ} [NeZero n] (v j : Fin n) : Prop :=
  v ≠ j ∧ v ≠ j + 1

theorem KWVertexEdgeNonincident.symm_endpoint
    {n : ℕ} [NeZero n] {v j : Fin n} (h : KWVertexEdgeNonincident v j) :
    v ≠ j ∧ v ≠ j + 1 := h

theorem KWFiniteSimplePolygon.vertex_not_mem_closedEdge
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    {v j : Fin n} (hvj : v ≠ j) (hvjs : v ≠ j + 1) :
    polygon.vertex v ∉ polygon.closedEdge j := by
  intro hv
  have hbetween : Wbtw ℝ (polygon.vertex j) (polygon.vertex v)
      (polygon.vertex (j + 1)) := mem_segment_iff_wbtw.mp hv
  have hs : Sbtw ℝ (polygon.vertex j) (polygon.vertex v)
      (polygon.vertex (j + 1)) :=
    ⟨hbetween, polygon.vertex_injective.ne hvj,
      polygon.vertex_injective.ne hvjs⟩
  exact polygon.vertex_not_strictly_between j v hvj hvjs hs

theorem KWFiniteSimplePolygon.singleton_vertex_disjoint_closedEdge
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    {v j : Fin n} (hvj : v ≠ j) (hvjs : v ≠ j + 1) :
    Disjoint ({polygon.vertex v} : Set ℂ) (polygon.closedEdge j) := by
  exact Set.disjoint_singleton_left.mpr
    (polygon.vertex_not_mem_closedEdge hvj hvjs)

theorem KWFiniteSimplePolygon.singleton_vertex_disjoint_closedEdge_of_nonincident
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    {v j : Fin n} (hvj : KWVertexEdgeNonincident v j) :
    Disjoint ({polygon.vertex v} : Set ℂ) (polygon.closedEdge j) :=
  polygon.singleton_vertex_disjoint_closedEdge hvj.1 hvj.2

private theorem exists_uniform_vertexEdge_radius_finset
    {n : ℕ} [NeZero n]
    (polygon : KWFiniteSimplePolygon n)
    (pairs : Finset (Fin n × Fin n))
    (hpairs : ∀ p ∈ pairs, p.1 ≠ p.2 ∧ p.1 ≠ p.2 + 1) :
    ∃ r : ℝ≥0, 0 < r ∧ ∀ p ∈ pairs,
      ∀ y ∈ polygon.closedEdge p.2,
        (r : ℝ≥0∞) < edist (polygon.vertex p.1) y := by
  classical
  induction pairs using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert p s hp ih =>
      have hpair := hpairs p (by simp)
      obtain ⟨rp, hrp, hsepP⟩ := Metric.exists_pos_forall_lt_edist
        (s := {polygon.vertex p.1}) (t := polygon.closedEdge p.2)
        isCompact_singleton (polygon.closedEdge_isClosed p.2)
        (polygon.singleton_vertex_disjoint_closedEdge hpair.1 hpair.2)
      obtain ⟨rs, hrs, hsepS⟩ := ih (fun q hq ↦ hpairs q (by simp [hq]))
      refine ⟨min rp rs, lt_min hrp hrs, ?_⟩
      intro q hq y hy
      rcases Finset.mem_insert.mp hq with rfl | hqs
      · exact (ENNReal.coe_le_coe.mpr (min_le_left _ _)).trans_lt
          (hsepP (polygon.vertex q.1) rfl y hy)
      · exact (ENNReal.coe_le_coe.mpr (min_le_right _ _)).trans_lt
          (hsepS q hqs y hy)

theorem KWFiniteSimplePolygon.exists_uniform_vertex_edge_separation
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n) :
    ∃ r : ℝ≥0, 0 < r ∧
      ∀ v j : Fin n, v ≠ j → v ≠ j + 1 →
        ∀ y ∈ polygon.closedEdge j,
          (r : ℝ) < dist (polygon.vertex v) y := by
  classical
  let pairs : Finset (Fin n × Fin n) :=
    Finset.univ.filter (fun p ↦ p.1 ≠ p.2 ∧ p.1 ≠ p.2 + 1)
  obtain ⟨r, hr, hsep⟩ := exists_uniform_vertexEdge_radius_finset
    polygon pairs (by
      intro p hp
      simpa only [pairs, Finset.mem_filter, Finset.mem_univ, true_and] using hp)
  refine ⟨r, hr, ?_⟩
  intro v j hvj hvjs y hy
  have h := hsep (v, j) (by simp [pairs, hvj, hvjs]) y hy
  rw [edist_dist] at h
  exact ENNReal.coe_lt_ofReal.mp h

theorem KWFiniteSimplePolygon.vertexBall_disjoint_closedEdgeTube
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    {r : ℝ≥0}
    (hsep : ∀ v j : Fin n, v ≠ j → v ≠ j + 1 →
      ∀ y ∈ polygon.closedEdge j,
        (r : ℝ) < dist (polygon.vertex v) y)
    {v j : Fin n} (hvj : v ≠ j) (hvjs : v ≠ j + 1) :
    Disjoint (Metric.ball (polygon.vertex v) ((r : ℝ) / 2))
      (polygon.closedEdgeTube (r / 2) j) := by
  rw [Set.disjoint_left]
  rintro z hz ⟨y, hy, hzy⟩
  have hvy := hsep v j hvj hvjs y hy
  have hvz : dist (polygon.vertex v) z < (r : ℝ) / 2 := by
    exact Metric.mem_ball'.mp hz
  have hzy' : dist z y < (r : ℝ) / 2 := by
    simpa only [NNReal.coe_div, NNReal.coe_ofNat] using hzy
  have htriangle : dist (polygon.vertex v) y ≤
      dist (polygon.vertex v) z + dist z y := dist_triangle _ _ _
  linarith

end StatMech.FrontierA
