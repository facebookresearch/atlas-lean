/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardAdaptiveConnectorClosedSeparation





namespace StatMech.FrontierA

open Set

private theorem lineMap_segment_point
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

private theorem lineMap_parameterSegments_disjoint
    {a b : ℂ} (hab : a ≠ b)
    {s t u v : ℝ} (hst : s ≤ t) (huv : u ≤ v) (htu : t < u) :
    Disjoint
      (segment ℝ (AffineMap.lineMap a b s) (AffineMap.lineMap a b t))
      (segment ℝ (AffineMap.lineMap a b u) (AffineMap.lineMap a b v)) := by
  rw [Set.disjoint_left]
  intro z hz₁ hz₂
  obtain ⟨x, hx, hxz⟩ := lineMap_segment_point hst hz₁
  obtain ⟨y, hy, hyz⟩ := lineMap_segment_point huv hz₂
  have hxy : x = y := AffineMap.lineMap_injective ℝ hab (hxz.symm.trans hyz)
  rw [hxy] at hx
  linarith [hx.2, hy.1]

private theorem lineMap_parameterSegments_disjoint_rev
    {a b : ℂ} (hab : a ≠ b)
    {s t u v : ℝ} (hst : s ≤ t) (huv : u ≤ v) (hvs : v < s) :
    Disjoint
      (segment ℝ (AffineMap.lineMap a b s) (AffineMap.lineMap a b t))
      (segment ℝ (AffineMap.lineMap a b u) (AffineMap.lineMap a b v)) := by
  exact (lineMap_parameterSegments_disjoint hab huv hst hvs).symm

noncomputable def KWAdaptivePatchedData.idealMidParameter
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) : ℝ :=
  (patch.data.parameter i q.succ.castSucc.castSucc +
    patch.data.parameter i q.succ.castSucc.succ) / 2

theorem KWAdaptivePatchedData.parameter_lt_idealMid
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) :
    patch.data.parameter i q.succ.castSucc.castSucc <
      patch.idealMidParameter i q := by
  have h := patch.data.parameter_strict i q.succ.castSucc
  unfold KWAdaptivePatchedData.idealMidParameter
  linarith

theorem KWAdaptivePatchedData.idealMid_lt_parameter
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) :
    patch.idealMidParameter i q <
      patch.data.parameter i q.succ.castSucc.succ := by
  have h := patch.data.parameter_strict i q.succ.castSucc
  unfold KWAdaptivePatchedData.idealMidParameter
  linarith

theorem KWAdaptivePatchedData.idealMiddleCorner_eq_lineMap_midParameter
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) :
    patch.idealMiddleCorner i q =
      AffineMap.lineMap (polygon.vertex i) (polygon.vertex (i + 1))
        (patch.idealMidParameter i q) := by
  rw [KWAdaptivePatchedData.idealMiddleCorner,
    KWStairParameterData.base, KWStairParameterData.base,
    AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module,
    AffineMap.lineMap_apply_module]
  simp only [Complex.real_smul]
  unfold KWAdaptivePatchedData.idealMidParameter
  push_cast
  ring

theorem KWAdaptivePatchedData.idealRawClosedEdge_even_eq_parameterSegment
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) :
    kwRawClosedEdge patch.idealVertex (kwStairEvenIndex i q.castSucc) =
      segment ℝ
        (AffineMap.lineMap (polygon.vertex i) (polygon.vertex (i + 1))
          (patch.data.parameter i q.succ.castSucc.castSucc))
        (AffineMap.lineMap (polygon.vertex i) (polygon.vertex (i + 1))
          (patch.idealMidParameter i q)) := by
  rw [kwRawClosedEdge, kwStairEvenIndex_add_one,
    patch.idealVertex_even, patch.idealVertex_odd,
    patch.pathBase_castSucc, patch.idealPathCorner_castSucc,
    patch.idealMiddleCorner_eq_lineMap_midParameter]
  rfl

theorem KWAdaptivePatchedData.idealRawClosedEdge_odd_eq_parameterSegment
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) :
    kwRawClosedEdge patch.idealVertex (kwStairOddIndex i q.castSucc) =
      segment ℝ
        (AffineMap.lineMap (polygon.vertex i) (polygon.vertex (i + 1))
          (patch.idealMidParameter i q))
        (AffineMap.lineMap (polygon.vertex i) (polygon.vertex (i + 1))
          (patch.data.parameter i q.succ.castSucc.succ)) := by
  rw [kwRawClosedEdge, kwStairOddIndex_castSucc_add_one,
    patch.idealVertex_odd, patch.idealVertex_even,
    patch.idealPathCorner_castSucc,
    patch.idealMiddleCorner_eq_lineMap_midParameter]
  have hbase : patch.pathBase i q.succ =
      patch.data.base i q.succ.castSucc.succ := by
    by_cases hq : q = patch.lastMiddleIndex
    · subst q
      have hlast : patch.lastMiddleIndex.succ = Fin.last M := by
        apply Fin.ext
        simp [KWAdaptivePatchedData.lastMiddleIndex]
        have := patch.hM
        omega
      rw [hlast, patch.pathBase_last]
      unfold KWAdaptivePatchedData.incomingPort
      congr 2
    · have hsucc_ne : q.succ ≠ Fin.last M := by
        intro h
        apply hq
        apply Fin.ext
        have hval := congrArg Fin.val h
        simp only [Fin.val_succ, Fin.val_last] at hval
        simp [KWAdaptivePatchedData.lastMiddleIndex]
        omega
      obtain ⟨r, hr⟩ := Fin.eq_castSucc_of_ne_last hsucc_ne
      rw [← hr, patch.pathBase_castSucc]
      congr 2
  rw [hbase]
  rfl

private theorem KWAdaptivePatchedData.parameter_next_le_parameter_current
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) {q k : Fin M} (hqk : q.val < k.val) :
    patch.data.parameter i q.succ.castSucc.succ ≤
      patch.data.parameter i k.succ.castSucc.castSucc := by
  apply (patch.data.parameter_strictMono i).monotone
  apply Fin.mk_le_mk.mpr
  simp only [Fin.val_succ, Fin.val_castSucc]
  omega

private theorem KWAdaptivePatchedData.parameter_next_lt_parameter_current
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) {q k : Fin M} (hqk : q.val + 1 < k.val) :
    patch.data.parameter i q.succ.castSucc.succ <
      patch.data.parameter i k.succ.castSucc.castSucc := by
  apply patch.data.parameter_strictMono i
  apply Fin.mk_lt_mk.mpr
  simp only [Fin.val_succ, Fin.val_castSucc]
  omega

theorem KWAdaptivePatchedData.idealRawClosedEdge_even_disjoint_even
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q k : Fin M) (hqk : q ≠ k) :
    Disjoint
      (kwRawClosedEdge patch.idealVertex (kwStairEvenIndex i q.castSucc))
      (kwRawClosedEdge patch.idealVertex (kwStairEvenIndex i k.castSucc)) := by
  rw [patch.idealRawClosedEdge_even_eq_parameterSegment,
    patch.idealRawClosedEdge_even_eq_parameterSegment]
  have hab := polygon.vertex_injective.ne (polygon.add_one_ne_self i).symm
  rcases lt_or_gt_of_ne hqk with hlt | hgt
  · apply lineMap_parameterSegments_disjoint hab
      (patch.parameter_lt_idealMid i q).le
      (patch.parameter_lt_idealMid i k).le
    exact (patch.idealMid_lt_parameter i q).trans_le
      (patch.parameter_next_le_parameter_current i (by simpa using hlt))
  · apply lineMap_parameterSegments_disjoint_rev hab
      (patch.parameter_lt_idealMid i q).le
      (patch.parameter_lt_idealMid i k).le
    exact (patch.idealMid_lt_parameter i k).trans_le
      (patch.parameter_next_le_parameter_current i (by simpa using hgt))

theorem KWAdaptivePatchedData.idealRawClosedEdge_odd_disjoint_odd
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q k : Fin M) (hqk : q ≠ k) :
    Disjoint
      (kwRawClosedEdge patch.idealVertex (kwStairOddIndex i q.castSucc))
      (kwRawClosedEdge patch.idealVertex (kwStairOddIndex i k.castSucc)) := by
  rw [patch.idealRawClosedEdge_odd_eq_parameterSegment,
    patch.idealRawClosedEdge_odd_eq_parameterSegment]
  have hab := polygon.vertex_injective.ne (polygon.add_one_ne_self i).symm
  rcases lt_or_gt_of_ne hqk with hlt | hgt
  · apply lineMap_parameterSegments_disjoint hab
      (patch.idealMid_lt_parameter i q).le
      (patch.idealMid_lt_parameter i k).le
    exact (patch.parameter_next_le_parameter_current i (by simpa using hlt)).trans_lt
      (patch.parameter_lt_idealMid i k)
  · apply lineMap_parameterSegments_disjoint_rev hab
      (patch.idealMid_lt_parameter i q).le
      (patch.idealMid_lt_parameter i k).le
    exact (patch.parameter_next_le_parameter_current i (by simpa using hgt)).trans_lt
      (patch.parameter_lt_idealMid i q)

theorem KWAdaptivePatchedData.idealRawClosedEdge_even_disjoint_odd
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q k : Fin M)
    (hnon : KWEdgesNonincident
      (kwStairEvenIndex i q.castSucc) (kwStairOddIndex i k.castSucc)) :
    Disjoint
      (kwRawClosedEdge patch.idealVertex (kwStairEvenIndex i q.castSucc))
      (kwRawClosedEdge patch.idealVertex (kwStairOddIndex i k.castSucc)) := by
  rw [patch.idealRawClosedEdge_even_eq_parameterSegment,
    patch.idealRawClosedEdge_odd_eq_parameterSegment]
  have hab := polygon.vertex_injective.ne (polygon.add_one_ne_self i).symm
  rcases lt_trichotomy q.val k.val with hlt | heq | hgt
  · apply lineMap_parameterSegments_disjoint hab
      (patch.parameter_lt_idealMid i q).le
      (patch.idealMid_lt_parameter i k).le
    exact (patch.idealMid_lt_parameter i q).trans_le
      ((patch.parameter_next_le_parameter_current i hlt).trans_lt
        (patch.parameter_lt_idealMid i k)).le
  · have hqk : q = k := Fin.ext heq
    subst k
    exact (hnon.2.2 (kwStairEvenIndex_add_one i q.castSucc)).elim
  · by_cases hgap : k.val + 1 < q.val
    · apply lineMap_parameterSegments_disjoint_rev hab
        (patch.parameter_lt_idealMid i q).le
        (patch.idealMid_lt_parameter i k).le
      exact patch.parameter_next_lt_parameter_current i hgap
    · have hsucc : k.succ = q.castSucc := by
        apply Fin.ext
        simp only [Fin.val_succ, Fin.val_castSucc]
        omega
      apply (hnon.2.1 ?_).elim
      rw [← hsucc, ← kwStairOddIndex_castSucc_add_one]

theorem KWAdaptivePatchedData.idealRawClosedEdge_odd_disjoint_even
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q k : Fin M)
    (hnon : KWEdgesNonincident
      (kwStairOddIndex i q.castSucc) (kwStairEvenIndex i k.castSucc)) :
    Disjoint
      (kwRawClosedEdge patch.idealVertex (kwStairOddIndex i q.castSucc))
      (kwRawClosedEdge patch.idealVertex (kwStairEvenIndex i k.castSucc)) := by
  exact (patch.idealRawClosedEdge_even_disjoint_odd i k q hnon.symm).symm

end StatMech.FrontierA
