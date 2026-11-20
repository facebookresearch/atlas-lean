/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardAdjacentCoreSeparation









namespace StatMech.FrontierA

open scoped NNReal ENNReal Convex Pointwise
open Set

def KWFiniteSimplePolygon.closedEdgeCoreTube
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (eps : ℝ) (r : ℝ≥0) (i : Fin n) : Set ℂ :=
  {z | ∃ x ∈ polygon.closedEdgeCore eps i, dist z x < r}

theorem KWFiniteSimplePolygon.closedEdgeCore_convex
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (eps : ℝ) (i : Fin n) :
    Convex ℝ (polygon.closedEdgeCore eps i) := by
  exact (convex_Icc eps (1 - eps)).affine_image
    (AffineMap.lineMap (polygon.vertex i) (polygon.vertex (i + 1)))

theorem KWFiniteSimplePolygon.closedEdgeCoreTube_eq_add_ball
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (eps : ℝ) (r : ℝ≥0) (i : Fin n) :
    polygon.closedEdgeCoreTube eps r i =
      polygon.closedEdgeCore eps i + Metric.ball (0 : ℂ) (r : ℝ) := by
  ext z
  constructor
  · rintro ⟨x, hx, hzx⟩
    apply Set.mem_add.mpr
    refine ⟨x, hx, z - x, ?_, by ring⟩
    rw [mem_ball_zero_iff, ← dist_eq_norm]
    exact hzx
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_add.mp hz
    refine ⟨x, hx, ?_⟩
    rw [dist_eq_norm, add_sub_cancel_left, ← mem_ball_zero_iff]
    exact hy

theorem KWFiniteSimplePolygon.closedEdgeCoreTube_convex
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (eps : ℝ) (r : ℝ≥0) (i : Fin n) :
    Convex ℝ (polygon.closedEdgeCoreTube eps r i) := by
  rw [polygon.closedEdgeCoreTube_eq_add_ball]
  exact (polygon.closedEdgeCore_convex eps i).add
    (convex_ball (0 : ℂ) (r : ℝ))

theorem nnreal_lt_edist_iff_lt_dist
    {r : ℝ≥0} {x y : ℂ} :
    (r : ℝ≥0∞) < edist x y ↔ (r : ℝ) < dist x y := by
  rw [edist_dist, ENNReal.ofReal_eq_coe_nnreal dist_nonneg,
    ENNReal.coe_lt_coe]
  rfl

theorem KWFiniteSimplePolygon.closedEdgeCoreTube_disjoint_of_separation
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    {eps : ℝ} {r : ℝ≥0}
    (hsep : ∀ i j : Fin n, i ≠ j →
      ∀ x ∈ polygon.closedEdgeCore eps i,
        ∀ y ∈ polygon.closedEdgeCore eps j,
          (r : ℝ≥0∞) < edist x y)
    {i j : Fin n} (hij : i ≠ j) :
    Disjoint (polygon.closedEdgeCoreTube eps (r / 2) i)
      (polygon.closedEdgeCoreTube eps (r / 2) j) := by
  rw [Set.disjoint_left]
  rintro z ⟨x, hx, hzx⟩ ⟨y, hy, hzy⟩
  have hxy : (r : ℝ) < dist x y :=
    nnreal_lt_edist_iff_lt_dist.mp (hsep i j hij x hx y hy)
  have hxz : dist x z < (r : ℝ) / 2 := by
    simpa only [dist_comm x z, NNReal.coe_div, NNReal.coe_ofNat] using hzx
  have hzy' : dist z y < (r : ℝ) / 2 := by
    simpa only [NNReal.coe_div, NNReal.coe_ofNat] using hzy
  have htriangle : dist x y ≤ dist x z + dist z y := dist_triangle x z y
  linarith



theorem KWFiniteSimplePolygon.exists_pairwise_disjoint_closedEdgeCoreTubes
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    {eps : ℝ} (heps : 0 < eps ∧ eps < 1 / 2) :
    ∃ r : ℝ≥0, 0 < r ∧
      ∀ i j : Fin n, i ≠ j →
        Disjoint (polygon.closedEdgeCoreTube eps r i)
          (polygon.closedEdgeCoreTube eps r j) := by
  obtain ⟨r, hr, hsep⟩ :=
    polygon.exists_uniform_closedEdgeCore_separation heps
  refine ⟨r / 2, half_pos hr, ?_⟩
  intro i j hij
  exact polygon.closedEdgeCoreTube_disjoint_of_separation hsep hij

end StatMech.FrontierA
