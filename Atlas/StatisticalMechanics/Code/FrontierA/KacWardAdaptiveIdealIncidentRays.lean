/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardAdaptiveIdealSameEdge





namespace StatMech.FrontierA

open Set

def kwTranslatedOpenRayTail (v a : ℂ) : Set ℂ :=
  {z | ∃ t : ℝ, 1 < t ∧ z = v + t * a}

private theorem lineMap_segment_parameter
    {a b : ℂ} {s t : ℝ} (hst : s ≤ t) {z : ℂ}
    (hz : z ∈ segment ℝ (AffineMap.lineMap a b s)
      (AffineMap.lineMap a b t)) :
    ∃ u ∈ Icc s t, z = AffineMap.lineMap a b u := by
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  let u := (1 - r) * s + r * t
  refine ⟨u, ?_, ?_⟩
  · constructor <;> dsimp only [u] <;> nlinarith [hr.1, hr.2]
  · simp only [AffineMap.lineMap_apply_module, Complex.real_smul]
    dsimp only [u]
    push_cast
    ring

theorem KWAdaptivePatchedData.beta_le_retainedParameter
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) :
    patch.beta ≤ patch.data.parameter i q.succ.castSucc.castSucc := by
  rw [← patch.parameter_one i]
  apply (patch.data.parameter_strictMono i).monotone
  apply Fin.mk_le_mk.mpr
  change 1 ≤ q.val + 1
  omega

theorem KWAdaptivePatchedData.beta_lt_retainedParameter
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) (hq : q ≠ 0) :
    patch.beta < patch.data.parameter i q.succ.castSucc.castSucc := by
  rw [← patch.parameter_one i]
  apply patch.data.parameter_strictMono i
  apply Fin.mk_lt_mk.mpr
  have hqpos : 0 < q.val := Fin.pos_iff_ne_zero.mpr hq
  change 1 < q.val + 1
  omega

theorem KWAdaptivePatchedData.retainedNextParameter_le_incoming
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) :
    patch.data.parameter i q.succ.castSucc.succ ≤
      1 - patch.alpha (i + 1) := by
  rw [← patch.parameter_penultimate i]
  apply (patch.data.parameter_strictMono i).monotone
  apply Fin.mk_le_mk.mpr
  change q.val + 1 + 1 ≤ M + 1
  omega

theorem KWAdaptivePatchedData.retainedNextParameter_lt_incoming
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) (hq : q ≠ patch.lastMiddleIndex) :
    patch.data.parameter i q.succ.castSucc.succ <
      1 - patch.alpha (i + 1) := by
  rw [← patch.parameter_penultimate i]
  apply patch.data.parameter_strictMono i
  apply Fin.mk_lt_mk.mpr
  change q.val + 2 < M + 1
  have hqLt := q.isLt
  have hlast := patch.lastMiddleIndex_val
  by_contra h
  apply hq
  apply Fin.ext
  omega

private theorem lineMap_mem_outgoingTail
    {n : ℕ} [NeZero n] {polygon : KWFiniteSimplePolygon n}
    {beta x : ℝ} (hbeta : 0 < beta) (hxbeta : beta < x)
    (i : Fin n) :
    AffineMap.lineMap (polygon.vertex i) (polygon.vertex (i + 1)) x ∈
      kwTranslatedOpenRayTail (polygon.vertex i)
        (beta * polygon.edgeVector i) := by
  refine ⟨x / beta, (lt_div_iff₀ hbeta).mpr (by simpa using hxbeta), ?_⟩
  unfold KWFiniteSimplePolygon.edgeVector
  rw [AffineMap.lineMap_apply_module]
  simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul]
  push_cast
  field_simp [ne_of_gt hbeta]
  ring

private theorem lineMap_mem_incomingTail
    {n : ℕ} [NeZero n] {polygon : KWFiniteSimplePolygon n}
    {alpha x : ℝ} (halpha : 0 < alpha) (hxalpha : x < 1 - alpha)
    (i : Fin n) :
    AffineMap.lineMap (polygon.vertex i) (polygon.vertex (i + 1)) x ∈
      kwTranslatedOpenRayTail (polygon.vertex (i + 1))
        (alpha * (-polygon.edgeVector i)) := by
  refine ⟨(1 - x) / alpha, (lt_div_iff₀ halpha).mpr (by linarith), ?_⟩
  unfold KWFiniteSimplePolygon.edgeVector
  rw [AffineMap.lineMap_apply_module]
  simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul]
  push_cast
  field_simp [ne_of_gt halpha]
  ring

private theorem lineMap_mem_outgoingPortTail
    {n : ℕ} [NeZero n] {polygon : KWFiniteSimplePolygon n}
    {beta x : ℝ} (hbeta : 0 < beta) (hxbeta : beta ≤ x)
    (i : Fin n) :
    AffineMap.lineMap (polygon.vertex i) (polygon.vertex (i + 1)) x ∈
      {polygon.vertex i + beta * polygon.edgeVector i} ∪
        kwTranslatedOpenRayTail (polygon.vertex i)
          (beta * polygon.edgeVector i) := by
  rcases hxbeta.eq_or_lt with rfl | hlt
  · left
    rw [mem_singleton_iff]
    unfold KWFiniteSimplePolygon.edgeVector
    rw [AffineMap.lineMap_apply_module]
    simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul]
    push_cast
    ring
  · right
    exact lineMap_mem_outgoingTail hbeta hlt i

private theorem lineMap_mem_incomingPortTail
    {n : ℕ} [NeZero n] {polygon : KWFiniteSimplePolygon n}
    {alpha x : ℝ} (halpha : 0 < alpha) (hxalpha : x ≤ 1 - alpha)
    (i : Fin n) :
    AffineMap.lineMap (polygon.vertex i) (polygon.vertex (i + 1)) x ∈
      {polygon.vertex (i + 1) + alpha * (-polygon.edgeVector i)} ∪
        kwTranslatedOpenRayTail (polygon.vertex (i + 1))
          (alpha * (-polygon.edgeVector i)) := by
  rcases hxalpha.eq_or_lt with rfl | hlt
  · left
    rw [mem_singleton_iff]
    unfold KWFiniteSimplePolygon.edgeVector
    rw [AffineMap.lineMap_apply_module]
    simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul]
    push_cast
    ring
  · right
    exact lineMap_mem_incomingTail halpha hlt i

theorem KWAdaptivePatchedData.idealRawClosedEdge_even_subset_outgoingTail
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) (hq : q ≠ 0) :
    kwRawClosedEdge patch.idealVertex (kwStairEvenIndex i q.castSucc) ⊆
      kwTranslatedOpenRayTail (polygon.vertex i)
        (patch.beta * polygon.edgeVector i) := by
  rw [patch.idealRawClosedEdge_even_eq_parameterSegment]
  intro z hz
  obtain ⟨x, hx, rfl⟩ := lineMap_segment_parameter
    (patch.parameter_lt_idealMid i q).le hz
  exact lineMap_mem_outgoingTail patch.hbeta
    ((patch.beta_lt_retainedParameter i q hq).trans_le hx.1) i

theorem KWAdaptivePatchedData.idealRawClosedEdge_even_subset_outgoingPortTail
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) :
    kwRawClosedEdge patch.idealVertex (kwStairEvenIndex i q.castSucc) ⊆
      {polygon.vertex i + patch.beta * polygon.edgeVector i} ∪
        kwTranslatedOpenRayTail (polygon.vertex i)
          (patch.beta * polygon.edgeVector i) := by
  rw [patch.idealRawClosedEdge_even_eq_parameterSegment]
  intro z hz
  obtain ⟨x, hx, rfl⟩ := lineMap_segment_parameter
    (patch.parameter_lt_idealMid i q).le hz
  exact lineMap_mem_outgoingPortTail patch.hbeta
    ((patch.beta_le_retainedParameter i q).trans hx.1) i

theorem KWAdaptivePatchedData.idealRawClosedEdge_odd_subset_outgoingTail
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) :
    kwRawClosedEdge patch.idealVertex (kwStairOddIndex i q.castSucc) ⊆
      kwTranslatedOpenRayTail (polygon.vertex i)
        (patch.beta * polygon.edgeVector i) := by
  rw [patch.idealRawClosedEdge_odd_eq_parameterSegment]
  intro z hz
  obtain ⟨x, hx, rfl⟩ := lineMap_segment_parameter
    (patch.idealMid_lt_parameter i q).le hz
  exact lineMap_mem_outgoingTail patch.hbeta
    ((patch.beta_le_retainedParameter i q).trans_lt
      (patch.parameter_lt_idealMid i q) |>.trans_le hx.1) i

theorem KWAdaptivePatchedData.idealRawClosedEdge_even_subset_incomingTail
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) :
    kwRawClosedEdge patch.idealVertex (kwStairEvenIndex i q.castSucc) ⊆
      kwTranslatedOpenRayTail (polygon.vertex (i + 1))
        (patch.alpha (i + 1) * (-polygon.edgeVector i)) := by
  rw [patch.idealRawClosedEdge_even_eq_parameterSegment]
  intro z hz
  obtain ⟨x, hx, rfl⟩ := lineMap_segment_parameter
    (patch.parameter_lt_idealMid i q).le hz
  exact lineMap_mem_incomingTail (patch.halpha (i + 1))
    (hx.2.trans_lt ((patch.idealMid_lt_parameter i q).trans_le
      (patch.retainedNextParameter_le_incoming i q))) i

theorem KWAdaptivePatchedData.idealRawClosedEdge_odd_subset_incomingTail
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) (hq : q ≠ patch.lastMiddleIndex) :
    kwRawClosedEdge patch.idealVertex (kwStairOddIndex i q.castSucc) ⊆
      kwTranslatedOpenRayTail (polygon.vertex (i + 1))
        (patch.alpha (i + 1) * (-polygon.edgeVector i)) := by
  rw [patch.idealRawClosedEdge_odd_eq_parameterSegment]
  intro z hz
  obtain ⟨x, hx, rfl⟩ := lineMap_segment_parameter
    (patch.idealMid_lt_parameter i q).le hz
  exact lineMap_mem_incomingTail (patch.halpha (i + 1))
    (hx.2.trans_lt (patch.retainedNextParameter_lt_incoming i q hq)) i

theorem KWAdaptivePatchedData.idealRawClosedEdge_odd_subset_incomingPortTail
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) :
    kwRawClosedEdge patch.idealVertex (kwStairOddIndex i q.castSucc) ⊆
      {polygon.vertex (i + 1) +
          patch.alpha (i + 1) * (-polygon.edgeVector i)} ∪
        kwTranslatedOpenRayTail (polygon.vertex (i + 1))
          (patch.alpha (i + 1) * (-polygon.edgeVector i)) := by
  rw [patch.idealRawClosedEdge_odd_eq_parameterSegment]
  intro z hz
  obtain ⟨x, hx, rfl⟩ := lineMap_segment_parameter
    (patch.idealMid_lt_parameter i q).le hz
  exact lineMap_mem_incomingPortTail (patch.halpha (i + 1))
    (hx.2.trans (patch.retainedNextParameter_le_incoming i q)) i

end StatMech.FrontierA
