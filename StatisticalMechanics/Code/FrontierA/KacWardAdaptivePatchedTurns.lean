/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardForwardSubdivision





namespace StatMech.FrontierA

private theorem scaled_horizontal_ne_zero
    {z : ℂ} {d : ℝ} (hd : d ≠ 0) (hz : z.re ≠ 0) :
    d * kwHorizontalPart z ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  unfold kwHorizontalPart at hre
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hre
  exact mul_ne_zero hd hz hre

private theorem scaled_vertical_ne_zero
    {z : ℂ} {d : ℝ} (hd : d ≠ 0) (hz : z.im ≠ 0) :
    d * kwVerticalPart z ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  unfold kwVerticalPart at him
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, add_zero, mul_one] at him
  exact mul_ne_zero hd hz him

private theorem cross_scaled_horizontal_vertical_ne_zero
    {z w : ℂ} {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hx : z.re ≠ 0) (hy : w.im ≠ 0) :
    kwComplexCross (a * kwHorizontalPart z)
      (b * kwVerticalPart w) ≠ 0 := by
  unfold kwComplexCross kwHorizontalPart kwVerticalPart
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  norm_num
  exact ⟨⟨ha, hx⟩, hb, hy⟩

private theorem cross_scaled_vertical_horizontal_ne_zero
    {z w : ℂ} {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hy : z.im ≠ 0) (hx : w.re ≠ 0) :
    kwComplexCross (a * kwVerticalPart z)
      (b * kwHorizontalPart w) ≠ 0 := by
  unfold kwComplexCross kwHorizontalPart kwVerticalPart
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  norm_num
  exact ⟨⟨ha, hy⟩, hb, hx⟩

private theorem scaled_forward
    {z : ℂ} {d₁ d₂ : ℝ} (hd₁ : d₁ ≠ 0) :
    (d₂ : ℂ) * z = ((d₂ / d₁ : ℝ) : ℂ) * ((d₁ : ℂ) * z) := by
  calc
    (d₂ : ℂ) * z = (((d₂ / d₁) * d₁ : ℝ) : ℂ) * z := by
      rw [div_mul_cancel₀ d₂ hd₁]
    _ = ((d₂ / d₁ : ℝ) : ℂ) * ((d₁ : ℂ) * z) := by
      push_cast
      ring

theorem KWAdaptivePatchedData.middleDelta_pos
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) :
    0 < patch.data.parameter i q.succ.castSucc.succ -
      patch.data.parameter i q.succ.castSucc.castSucc :=
  kwStairParameterDelta_pos patch.data i q.succ.castSucc

theorem KWAdaptivePatchedData.rawEdge_ne_zero
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0) :
    ∀ j : Fin (n * (2 * (M + 1))), kwRawEdge patch.vertex j ≠ 0 := by
  intro j
  obtain ⟨i, k, rfl | rfl⟩ := kwStairIndex_even_or_odd j
  · refine Fin.lastCases ?_ (fun q ↦ ?_) k
    · rw [patch.rawEdge_even_last]
      have hcorner := (patch.connector (i + 1)).corner_ne_left
      have hi : i + 1 - 1 = i := by abel
      exact sub_ne_zero.mpr (by simpa only [hi] using hcorner)
    · rw [patch.rawEdge_even_castSucc]
      by_cases hv : patch.sliceUsesVerticalFirst i q
      · rw [if_pos hv]
        simpa only [Complex.ofReal_sub] using
          scaled_vertical_ne_zero (patch.middleDelta_pos i q).ne'
            (hcoords i).2
      · rw [if_neg hv]
        simpa only [Complex.ofReal_sub] using
          scaled_horizontal_ne_zero (patch.middleDelta_pos i q).ne'
            (hcoords i).1
  · refine Fin.lastCases ?_ (fun q ↦ ?_) k
    · rw [patch.rawEdge_odd_last]
      have hcorner := (patch.connector (i + 1)).corner_ne_right
      exact sub_ne_zero.mpr hcorner.symm
    · rw [patch.rawEdge_odd_castSucc]
      by_cases hv : patch.sliceUsesVerticalFirst i q
      · rw [if_pos hv]
        simpa only [Complex.ofReal_sub] using
          scaled_horizontal_ne_zero (patch.middleDelta_pos i q).ne'
            (hcoords i).1
      · rw [if_neg hv]
        simpa only [Complex.ofReal_sub] using
          scaled_vertical_ne_zero (patch.middleDelta_pos i q).ne'
            (hcoords i).2

theorem KWAdaptivePatchedData.turnAdmissible_even_middle
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    (i : Fin n) (q : Fin M) :
    KWRawTurnAdmissible patch.vertex (kwStairEvenIndex i q.castSucc) := by
  left
  rw [kwStairEvenIndex_add_one, patch.rawEdge_even_castSucc,
    patch.rawEdge_odd_castSucc]
  by_cases hv : patch.sliceUsesVerticalFirst i q
  · rw [if_pos hv, if_pos hv]
    simpa only [Complex.ofReal_sub] using
      cross_scaled_vertical_horizontal_ne_zero
        (patch.middleDelta_pos i q).ne' (patch.middleDelta_pos i q).ne'
        (hcoords i).2 (hcoords i).1
  · rw [if_neg hv, if_neg hv]
    simpa only [Complex.ofReal_sub] using
      cross_scaled_horizontal_vertical_ne_zero
        (patch.middleDelta_pos i q).ne' (patch.middleDelta_pos i q).ne'
        (hcoords i).1 (hcoords i).2

theorem KWAdaptivePatchedData.turnAdmissible_even_connector
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) (i : Fin n) :
    KWRawTurnAdmissible patch.vertex (kwStairEvenIndex i (Fin.last M)) := by
  left
  rw [kwStairEvenIndex_add_one, patch.rawEdge_even_last,
    patch.rawEdge_odd_last]
  have hi : i + 1 - 1 = i := by abel
  simpa only [hi] using (patch.connector (i + 1)).turn_ne_zero

theorem KWAdaptivePatchedData.sliceUsesVerticalFirst_zero_iff
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) (i : Fin n) :
    patch.sliceUsesVerticalFirst i 0 ↔
      patch.connectorUsesVerticalFirst i := by
  have hne : (0 : Fin M) ≠ patch.lastMiddleIndex := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_zero, patch.lastMiddleIndex_val] at hval
    have := patch.hM
    omega
  simp [KWAdaptivePatchedData.sliceUsesVerticalFirst, hne]

theorem KWAdaptivePatchedData.sliceUsesVerticalFirst_last_iff
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) (i : Fin n) :
    patch.sliceUsesVerticalFirst i patch.lastMiddleIndex ↔
      patch.connectorUsesVerticalFirst (i + 1) := by
  have hne : patch.lastMiddleIndex ≠ 0 := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_zero, patch.lastMiddleIndex_val] at hval
    have := patch.hM
    omega
  simp [KWAdaptivePatchedData.sliceUsesVerticalFirst, hne]

theorem KWAdaptivePatchedData.connector_corner_eq_vh
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) {i : Fin n}
    (h : patch.connectorUsesVerticalFirst i) :
    (patch.connector i).corner = kwVHConnectorCorner
      (patch.alpha i * (-polygon.edgeVector (i - 1)))
      (patch.beta * polygon.edgeVector i) := h

theorem KWAdaptivePatchedData.connector_corner_eq_hv
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) {i : Fin n}
    (h : ¬patch.connectorUsesVerticalFirst i) :
    (patch.connector i).corner = kwHVConnectorCorner
      (patch.alpha i * (-polygon.edgeVector (i - 1)))
      (patch.beta * polygon.edgeVector i) := by
  rcases (patch.connector i).axis_corner with hHV | hVH
  · exact hHV
  · exact (h hVH).elim

theorem KWAdaptivePatchedData.connector_first_eq
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) (i : Fin n) :
    (patch.connector i).corner -
        patch.alpha i * (-polygon.edgeVector (i - 1)) =
      if patch.connectorUsesVerticalFirst i then
        kwVerticalPart (patch.beta * polygon.edgeVector i -
          patch.alpha i * (-polygon.edgeVector (i - 1)))
      else
        kwHorizontalPart (patch.beta * polygon.edgeVector i -
          patch.alpha i * (-polygon.edgeVector (i - 1))) := by
  by_cases hv : patch.connectorUsesVerticalFirst i
  · rw [if_pos hv, patch.connector_corner_eq_vh hv]
    unfold kwVHConnectorCorner kwVerticalPart
    apply Complex.ext <;>
      simp only [Complex.add_re, Complex.add_im, Complex.sub_re,
        Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im] <;> ring
  · rw [if_neg hv, patch.connector_corner_eq_hv hv]
    unfold kwHVConnectorCorner kwHorizontalPart
    apply Complex.ext <;>
      simp only [Complex.add_re, Complex.add_im, Complex.sub_re,
        Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im] <;> ring

theorem KWAdaptivePatchedData.connector_second_eq
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) (i : Fin n) :
    patch.beta * polygon.edgeVector i - (patch.connector i).corner =
      if patch.connectorUsesVerticalFirst i then
        kwHorizontalPart (patch.beta * polygon.edgeVector i -
          patch.alpha i * (-polygon.edgeVector (i - 1)))
      else
        kwVerticalPart (patch.beta * polygon.edgeVector i -
          patch.alpha i * (-polygon.edgeVector (i - 1))) := by
  by_cases hv : patch.connectorUsesVerticalFirst i
  · rw [if_pos hv, patch.connector_corner_eq_vh hv]
    unfold kwVHConnectorCorner kwHorizontalPart
    apply Complex.ext <;>
      simp only [Complex.add_re, Complex.add_im, Complex.sub_re,
        Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im] <;> ring
  · rw [if_neg hv, patch.connector_corner_eq_hv hv]
    unfold kwHVConnectorCorner kwVerticalPart
    apply Complex.ext <;>
      simp only [Complex.add_re, Complex.add_im, Complex.sub_re,
        Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im] <;> ring

theorem KWAdaptivePatchedData.connector_total_im_ne_of_vh
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) {i : Fin n}
    (hv : patch.connectorUsesVerticalFirst i) :
    (patch.beta * polygon.edgeVector i -
      patch.alpha i * (-polygon.edgeVector (i - 1))).im ≠ 0 := by
  intro hzero
  have hfirst := (patch.connector i).corner_ne_left
  apply hfirst
  apply sub_eq_zero.mp
  calc
    (patch.connector i).corner -
        patch.alpha i * (-polygon.edgeVector (i - 1)) =
      kwVerticalPart (patch.beta * polygon.edgeVector i -
        patch.alpha i * (-polygon.edgeVector (i - 1))) := by
          simpa only [if_pos hv] using patch.connector_first_eq i
    _ = 0 := by
      apply Complex.ext
      · simp [kwVerticalPart]
      · simpa [kwVerticalPart] using hzero

theorem KWAdaptivePatchedData.connector_total_re_ne_of_hv
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) {i : Fin n}
    (hv : ¬patch.connectorUsesVerticalFirst i) :
    (patch.beta * polygon.edgeVector i -
      patch.alpha i * (-polygon.edgeVector (i - 1))).re ≠ 0 := by
  intro hzero
  have hfirst := (patch.connector i).corner_ne_left
  apply hfirst
  apply sub_eq_zero.mp
  calc
    (patch.connector i).corner -
        patch.alpha i * (-polygon.edgeVector (i - 1)) =
      kwHorizontalPart (patch.beta * polygon.edgeVector i -
        patch.alpha i * (-polygon.edgeVector (i - 1))) := by
          simpa only [if_neg hv] using patch.connector_first_eq i
    _ = 0 := by
      apply Complex.ext
      · simpa [kwHorizontalPart] using hzero
      · simp [kwHorizontalPart]

theorem KWAdaptivePatchedData.connector_total_re_ne_of_vh
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) {i : Fin n}
    (hv : patch.connectorUsesVerticalFirst i) :
    (patch.beta * polygon.edgeVector i -
      patch.alpha i * (-polygon.edgeVector (i - 1))).re ≠ 0 := by
  intro hzero
  have hsecond := (patch.connector i).corner_ne_right
  apply hsecond
  apply Eq.symm
  apply sub_eq_zero.mp
  calc
    patch.beta * polygon.edgeVector i - (patch.connector i).corner =
      kwHorizontalPart (patch.beta * polygon.edgeVector i -
        patch.alpha i * (-polygon.edgeVector (i - 1))) := by
          simpa only [if_pos hv] using patch.connector_second_eq i
    _ = 0 := by
      apply Complex.ext
      · simpa [kwHorizontalPart] using hzero
      · simp [kwHorizontalPart]

theorem KWAdaptivePatchedData.connector_total_im_ne_of_hv
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) {i : Fin n}
    (hv : ¬patch.connectorUsesVerticalFirst i) :
    (patch.beta * polygon.edgeVector i -
      patch.alpha i * (-polygon.edgeVector (i - 1))).im ≠ 0 := by
  intro hzero
  have hsecond := (patch.connector i).corner_ne_right
  apply hsecond
  apply Eq.symm
  apply sub_eq_zero.mp
  calc
    patch.beta * polygon.edgeVector i - (patch.connector i).corner =
      kwVerticalPart (patch.beta * polygon.edgeVector i -
        patch.alpha i * (-polygon.edgeVector (i - 1))) := by
          simpa only [if_neg hv] using patch.connector_second_eq i
    _ = 0 := by
      apply Complex.ext
      · simp [kwVerticalPart]
      · simpa [kwVerticalPart] using hzero

theorem KWAdaptivePatchedData.turnAdmissible_lastMiddle_connector
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    (i : Fin n) :
    KWRawTurnAdmissible patch.vertex
      (kwStairOddIndex i patch.lastMiddleIndex.castSucc) := by
  left
  have hlast : patch.lastMiddleIndex.succ = Fin.last M := by
    apply Fin.ext
    simp [KWAdaptivePatchedData.lastMiddleIndex]
    have := patch.hM
    omega
  have hi : i + 1 - 1 = i := by abel
  have hnext : kwRawEdge patch.vertex
      (kwStairEvenIndex i patch.lastMiddleIndex.succ) =
      (patch.connector (i + 1)).corner -
        patch.alpha (i + 1) * (-polygon.edgeVector i) := by
    rw [hlast, patch.rawEdge_even_last]
  have hconnector :
      (patch.connector (i + 1)).corner -
          patch.alpha (i + 1) * (-polygon.edgeVector i) =
        if patch.connectorUsesVerticalFirst (i + 1) then
          kwVerticalPart (patch.beta * polygon.edgeVector (i + 1) -
            patch.alpha (i + 1) * (-polygon.edgeVector i))
        else
          kwHorizontalPart (patch.beta * polygon.edgeVector (i + 1) -
            patch.alpha (i + 1) * (-polygon.edgeVector i)) := by
    simpa only [hi] using patch.connector_first_eq (i + 1)
  rw [kwStairOddIndex_castSucc_add_one,
    patch.rawEdge_odd_castSucc, hnext,
    hconnector]
  by_cases hv : patch.connectorUsesVerticalFirst (i + 1)
  · have hs : patch.sliceUsesVerticalFirst i patch.lastMiddleIndex :=
      (patch.sliceUsesVerticalFirst_last_iff i).mpr hv
    rw [if_pos hs, if_pos hv]
    simpa only [hi, Complex.ofReal_sub, Complex.ofReal_one, one_mul] using
      (cross_scaled_horizontal_vertical_ne_zero
        (a := patch.data.parameter i
          patch.lastMiddleIndex.succ.castSucc.succ -
            patch.data.parameter i
              patch.lastMiddleIndex.succ.castSucc.castSucc)
        (b := 1) (patch.middleDelta_pos i patch.lastMiddleIndex).ne'
        (by norm_num) (hcoords i).1
        (patch.connector_total_im_ne_of_vh hv))
  · have hs : ¬patch.sliceUsesVerticalFirst i patch.lastMiddleIndex :=
      fun hs ↦ hv ((patch.sliceUsesVerticalFirst_last_iff i).mp hs)
    rw [if_neg hs, if_neg hv]
    simpa only [hi, Complex.ofReal_sub, Complex.ofReal_one, one_mul] using
      (cross_scaled_vertical_horizontal_ne_zero
        (a := patch.data.parameter i
          patch.lastMiddleIndex.succ.castSucc.succ -
            patch.data.parameter i
              patch.lastMiddleIndex.succ.castSucc.castSucc)
        (b := 1) (patch.middleDelta_pos i patch.lastMiddleIndex).ne'
        (by norm_num) (hcoords i).2
        (patch.connector_total_re_ne_of_hv hv))

theorem KWAdaptivePatchedData.turnAdmissible_connector_firstMiddle
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    (i : Fin n) :
    KWRawTurnAdmissible patch.vertex
      (kwStairOddIndex i (Fin.last M)) := by
  left
  rw [kwStairOddIndex_last_add_one, patch.rawEdge_odd_last]
  have hzero : (0 : Fin (M + 1)) = (0 : Fin M).castSucc := by
    apply Fin.ext
    rfl
  rw [hzero, patch.rawEdge_even_castSucc, patch.connector_second_eq]
  by_cases hv : patch.connectorUsesVerticalFirst (i + 1)
  · have hs : patch.sliceUsesVerticalFirst (i + 1) 0 :=
      (patch.sliceUsesVerticalFirst_zero_iff (i + 1)).mpr hv
    rw [if_pos hv, if_pos hs]
    simpa only [Complex.ofReal_sub, Complex.ofReal_one, one_mul] using
      (cross_scaled_horizontal_vertical_ne_zero
      (a := 1) (b := patch.data.parameter (i + 1)
        (0 : Fin M).succ.castSucc.succ -
          patch.data.parameter (i + 1) (0 : Fin M).succ.castSucc.castSucc)
      (by norm_num)
      (patch.middleDelta_pos (i + 1) 0).ne'
      (patch.connector_total_re_ne_of_vh hv) (hcoords (i + 1)).2)
  · have hs : ¬patch.sliceUsesVerticalFirst (i + 1) 0 :=
      fun hs ↦ hv ((patch.sliceUsesVerticalFirst_zero_iff (i + 1)).mp hs)
    rw [if_neg hv, if_neg hs]
    simpa only [Complex.ofReal_sub, Complex.ofReal_one, one_mul] using
      (cross_scaled_vertical_horizontal_ne_zero
      (a := 1) (b := patch.data.parameter (i + 1)
        (0 : Fin M).succ.castSucc.succ -
          patch.data.parameter (i + 1) (0 : Fin M).succ.castSucc.castSucc)
      (by norm_num)
      (patch.middleDelta_pos (i + 1) 0).ne'
      (patch.connector_total_im_ne_of_hv hv) (hcoords (i + 1)).1)

theorem KWAdaptivePatchedData.turnAdmissible_betweenMiddle
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    (i : Fin n) (q : Fin M) (hq : q ≠ patch.lastMiddleIndex) :
    KWRawTurnAdmissible patch.vertex
      (kwStairOddIndex i q.castSucc) := by
  have hqNext : q.val + 1 < M := by
    have hqLt := q.isLt
    have hlastVal := patch.lastMiddleIndex_val
    by_contra h
    have heq : q = patch.lastMiddleIndex := by
      apply Fin.ext
      omega
    exact hq heq
  let qnext : Fin M := ⟨q.val + 1, hqNext⟩
  rw [KWRawTurnAdmissible]
  rw [kwStairOddIndex_castSucc_add_one,
    patch.rawEdge_odd_castSucc]
  have hidx : q.succ = qnext.castSucc := by
    apply Fin.ext
    rfl
  have hnextEdge : kwRawEdge patch.vertex
      (kwStairEvenIndex i q.succ) =
      (patch.data.parameter i qnext.succ.castSucc.succ -
        patch.data.parameter i qnext.succ.castSucc.castSucc) *
        (if patch.sliceUsesVerticalFirst i qnext then
          kwVerticalPart (polygon.edgeVector i)
        else kwHorizontalPart (polygon.edgeVector i)) := by
    rw [hidx, patch.rawEdge_even_castSucc]
  rw [hnextEdge]
  let d₁ := patch.data.parameter i q.succ.castSucc.succ -
    patch.data.parameter i q.succ.castSucc.castSucc
  let d₂ := patch.data.parameter i qnext.succ.castSucc.succ -
    patch.data.parameter i qnext.succ.castSucc.castSucc
  have hd₁ : 0 < d₁ := patch.middleDelta_pos i q
  have hd₂ : 0 < d₂ := patch.middleDelta_pos i qnext
  by_cases hv₁ : patch.sliceUsesVerticalFirst i q
  · by_cases hv₂ : patch.sliceUsesVerticalFirst i qnext
    · left
      rw [if_pos hv₁, if_pos hv₂]
      simpa only [d₁, d₂, Complex.ofReal_sub] using
        cross_scaled_horizontal_vertical_ne_zero hd₁.ne' hd₂.ne'
          (hcoords i).1 (hcoords i).2
    · right
      refine ⟨d₂ / d₁, div_pos hd₂ hd₁, ?_⟩
      rw [if_pos hv₁, if_neg hv₂]
      simpa only [d₁, d₂, Complex.ofReal_sub] using
        (scaled_forward (z := kwHorizontalPart (polygon.edgeVector i))
          (d₁ := d₁) (d₂ := d₂) hd₁.ne')
  · by_cases hv₂ : patch.sliceUsesVerticalFirst i qnext
    · right
      refine ⟨d₂ / d₁, div_pos hd₂ hd₁, ?_⟩
      rw [if_neg hv₁, if_pos hv₂]
      simpa only [d₁, d₂, Complex.ofReal_sub] using
        (scaled_forward (z := kwVerticalPart (polygon.edgeVector i))
          (d₁ := d₁) (d₂ := d₂) hd₁.ne')
    · left
      rw [if_neg hv₁, if_neg hv₂]
      simpa only [d₁, d₂, Complex.ofReal_sub] using
        cross_scaled_vertical_horizontal_ne_zero hd₁.ne' hd₂.ne'
          (hcoords i).2 (hcoords i).1



theorem KWAdaptivePatchedData.turnAdmissible
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0) :
    ∀ j : Fin (n * (2 * (M + 1))), KWRawTurnAdmissible patch.vertex j := by
  intro j
  obtain ⟨i, k, rfl | rfl⟩ := kwStairIndex_even_or_odd j
  · refine Fin.lastCases ?_ (fun q ↦ ?_) k
    · exact patch.turnAdmissible_even_connector i
    · exact patch.turnAdmissible_even_middle hcoords i q
  · refine Fin.lastCases ?_ (fun q ↦ ?_) k
    · exact patch.turnAdmissible_connector_firstMiddle hcoords i
    · by_cases hq : q = patch.lastMiddleIndex
      · subst q
        exact patch.turnAdmissible_lastMiddle_connector hcoords i
      · exact patch.turnAdmissible_betweenMiddle hcoords i q hq

end StatMech.FrontierA
