/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardAdaptiveIdealSimple





namespace StatMech.FrontierA

open scoped NNReal

theorem KWAdaptivePatchedData.dist_middleCorner_ideal_lt_two_mul
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (r : ℝ≥0) (hfine : patch.data.MeshWithin r)
    (i : Fin n) (q : Fin M) :
    dist (patch.middleCorner i q) (patch.idealMiddleCorner i q) < 2 * r := by
  let base := patch.data.base i q.succ.castSucc.castSucc
  have hdelta : 0 < patch.data.parameter i q.succ.castSucc.succ -
      patch.data.parameter i q.succ.castSucc.castSucc :=
    patch.middleDelta_pos i q
  have hactual : ‖patch.middleCorner i q - base‖ < r := by
    rw [patch.middleCorner_sub_base, norm_mul, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdelta]
    by_cases hv : patch.sliceUsesVerticalFirst i q
    · rw [if_pos hv]
      exact (mul_le_mul_of_nonneg_left
        (norm_kwVerticalPart_le (polygon.edgeVector i)) hdelta.le).trans_lt
        (hfine i q.succ.castSucc)
    · rw [if_neg hv]
      exact (mul_le_mul_of_nonneg_left
        (norm_kwHorizontalPart_le (polygon.edgeVector i)) hdelta.le).trans_lt
        (hfine i q.succ.castSucc)
  have hideal : ‖patch.idealMiddleCorner i q - base‖ < r := by
    have hdeltaNorm :
        ‖(patch.data.parameter i q.succ.castSucc.succ : ℝ) -
          patch.data.parameter i q.succ.castSucc.castSucc‖ =
        (patch.data.parameter i q.succ.castSucc.succ : ℝ) -
          patch.data.parameter i q.succ.castSucc.castSucc := by
      exact Real.norm_of_nonneg hdelta.le
    rw [patch.idealMiddleCorner_sub_base, norm_mul, norm_mul,
      ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real,
      hdeltaNorm]
    norm_num
    have hmesh :
          (patch.data.parameter i q.castSucc.succ.succ -
            patch.data.parameter i q.castSucc.castSucc.succ) *
          ‖polygon.edgeVector i‖ < r := by
      exact hfine i q.succ.castSucc
    have hdelta' : 0 <
        patch.data.parameter i q.castSucc.succ.succ -
          patch.data.parameter i q.castSucc.castSucc.succ := by
      exact hdelta
    have hprod : 0 ≤
        (patch.data.parameter i q.castSucc.succ.succ -
            patch.data.parameter i q.castSucc.castSucc.succ) *
          ‖polygon.edgeVector i‖ :=
      mul_nonneg hdelta'.le (norm_nonneg _)
    unfold KWFiniteSimplePolygon.edgeVector at hmesh hprod
    unfold kwCyclicEdgeVector
    nlinarith
  rw [dist_eq_norm]
  have heq : patch.middleCorner i q - patch.idealMiddleCorner i q =
      (patch.middleCorner i q - base) -
        (patch.idealMiddleCorner i q - base) := by ring
  rw [heq]
  exact (norm_sub_le _ _).trans_lt (by
    have hr : (r : ℝ) + r = 2 * r := by ring
    rw [← hr]
    exact add_lt_add hactual hideal)

theorem KWAdaptivePatchedData.dist_vertex_idealVertex_lt_two_mul
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (r : ℝ≥0) (hr : 0 < r) (hfine : patch.data.MeshWithin r) :
    ∀ j : Fin (n * (2 * (M + 1))),
      dist (patch.vertex j) (patch.idealVertex j) < 2 * r := by
  intro j
  obtain ⟨i, k, rfl | rfl⟩ := kwStairIndex_even_or_odd j
  · rw [patch.vertex_even, patch.idealVertex_even, dist_self]
    positivity
  · refine Fin.lastCases ?_ (fun q ↦ ?_) k
    · rw [patch.vertex_odd, patch.idealVertex_odd,
        patch.pathCorner_last, patch.idealPathCorner_last, dist_self]
      positivity
    · rw [patch.vertex_odd, patch.idealVertex_odd,
        patch.pathCorner_castSucc, patch.idealPathCorner_castSucc]
      exact patch.dist_middleCorner_ideal_lt_two_mul r hfine i q

theorem KWAdaptivePatchedData.actual_nonincident_disjoint_of_close_to_ideal
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (ideal : KWFiniteSimplePolygon (n * (2 * (M + 1))))
    (hideal : ideal.vertex = patch.idealVertex)
    (r sep : ℝ≥0) (hr : 0 < r)
    (hfine : patch.data.MeshWithin r)
    (hsep : ∀ i j, KWEdgesNonincident i j →
      ∀ x ∈ ideal.closedEdge i, ∀ y ∈ ideal.closedEdge j,
        (sep : ℝ) < dist x y)
    (hsmall : 8 * (r : ℝ) < sep) :
    ∀ i j, KWEdgesNonincident i j →
      Disjoint (kwRawClosedEdge patch.vertex i)
        (kwRawClosedEdge patch.vertex j) := by
  intro i j hij
  rw [kwRawClosedEdge, kwRawClosedEdge]
  have hsepij := hsep i j hij
  simp only [KWFiniteSimplePolygon.closedEdge, hideal] at hsepij
  apply segment_disjoint_of_perturbation
    (le_of_lt (patch.dist_vertex_idealVertex_lt_two_mul r hr hfine i))
    (le_of_lt (patch.dist_vertex_idealVertex_lt_two_mul r hr hfine (i + 1)))
    (le_of_lt (patch.dist_vertex_idealVertex_lt_two_mul r hr hfine j))
    (le_of_lt (patch.dist_vertex_idealVertex_lt_two_mul r hr hfine (j + 1)))
    hsepij
  linarith

end StatMech.FrontierA
