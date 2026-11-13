/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardAdaptiveIdealGlobalSeparation
import Code.FrontierA.KacWardForwardSubdivision





namespace StatMech.FrontierA

private theorem cross_full_axis_ne_zero
    {z w : ℂ} (hzRe : z.re ≠ 0) (hzIm : z.im ≠ 0)
    (hw : w ≠ 0) (haxis : w.re = 0 ∨ w.im = 0) :
    kwComplexCross z w ≠ 0 := by
  rcases haxis with hre | him
  · have hwIm : w.im ≠ 0 := by
      intro hwim
      apply hw
      apply Complex.ext <;> assumption
    unfold kwComplexCross
    rw [hre]
    simp only [mul_zero, sub_zero]
    exact mul_ne_zero hzRe hwIm
  · have hwRe : w.re ≠ 0 := by
      intro hwre
      apply hw
      apply Complex.ext <;> assumption
    unfold kwComplexCross
    rw [him]
    simp only [mul_zero, zero_sub]
    exact neg_ne_zero.mpr (mul_ne_zero hzIm hwRe)

private theorem cross_axis_full_ne_zero
    {z w : ℂ} (hz : z ≠ 0) (haxis : z.re = 0 ∨ z.im = 0)
    (hwRe : w.re ≠ 0) (hwIm : w.im ≠ 0) :
    kwComplexCross z w ≠ 0 := by
  intro hzero
  apply cross_full_axis_ne_zero hwRe hwIm hz haxis
  rw [kwComplexCross_swap, hzero, neg_zero]

private theorem KWAdaptiveConnectorData.firstVector_axis
    {a b : ℂ} (connector : KWAdaptiveConnectorData a b) :
    (connector.corner - a).re = 0 ∨
      (connector.corner - a).im = 0 := by
  rcases connector.axis_corner with h | h
  · right
    rw [h]
    simp
  · left
    rw [h]
    simp

private theorem KWAdaptiveConnectorData.secondVector_axis
    {a b : ℂ} (connector : KWAdaptiveConnectorData a b) :
    (b - connector.corner).re = 0 ∨
      (b - connector.corner).im = 0 := by
  rcases connector.axis_corner with h | h
  · left
    rw [h]
    simp
  · right
    rw [h]
    simp

private theorem scaled_forward
    {z : ℂ} {d₁ d₂ : ℝ} (hd₁ : d₁ ≠ 0) :
    (d₂ : ℂ) * z = ((d₂ / d₁ : ℝ) : ℂ) * ((d₁ : ℂ) * z) := by
  calc
    (d₂ : ℂ) * z = (((d₂ / d₁) * d₁ : ℝ) : ℂ) * z := by
      rw [div_mul_cancel₀ d₂ hd₁]
    _ = ((d₂ / d₁ : ℝ) : ℂ) * ((d₁ : ℂ) * z) := by
      push_cast
      ring

theorem KWAdaptivePatchedData.idealRawEdge_ne_zero
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) :
    ∀ j : Fin (n * (2 * (M + 1))),
      kwRawEdge patch.idealVertex j ≠ 0 := by
  intro j
  obtain ⟨i, k, rfl | rfl⟩ := kwStairIndex_even_or_odd j
  · refine Fin.lastCases ?_ (fun q ↦ ?_) k
    · rw [patch.idealRawEdge_even_last]
      have hi : i + 1 - 1 = i := by abel
      exact sub_ne_zero.mpr (by
        simpa only [hi] using (patch.connector (i + 1)).corner_ne_left)
    · rw [patch.idealRawEdge_even_castSucc]
      have hdelta :
          ((patch.data.parameter i q.succ.castSucc.succ : ℂ) -
            patch.data.parameter i q.succ.castSucc.castSucc) ≠ 0 := by
        rw [← Complex.ofReal_sub, Complex.ofReal_ne_zero]
        exact (patch.middleDelta_pos i q).ne'
      exact mul_ne_zero
        (mul_ne_zero (by norm_num) hdelta)
        (polygon.edgeVector_ne_zero i)
  · refine Fin.lastCases ?_ (fun q ↦ ?_) k
    · rw [patch.idealRawEdge_odd_last]
      exact sub_ne_zero.mpr (patch.connector (i + 1)).corner_ne_right.symm
    · rw [patch.idealRawEdge_odd_castSucc]
      have hdelta :
          ((patch.data.parameter i q.succ.castSucc.succ : ℂ) -
            patch.data.parameter i q.succ.castSucc.castSucc) ≠ 0 := by
        rw [← Complex.ofReal_sub, Complex.ofReal_ne_zero]
        exact (patch.middleDelta_pos i q).ne'
      exact mul_ne_zero
        (mul_ne_zero (by norm_num) hdelta)
        (polygon.edgeVector_ne_zero i)

private theorem KWAdaptivePatchedData.idealTurn_evenMiddle
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) :
    KWRawTurnAdmissible patch.idealVertex
      (kwStairEvenIndex i q.castSucc) := by
  right
  refine ⟨1, by norm_num, ?_⟩
  rw [kwStairEvenIndex_add_one, patch.idealRawEdge_even_castSucc,
    patch.idealRawEdge_odd_castSucc]
  simp

private theorem KWAdaptivePatchedData.idealTurn_betweenMiddle
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) (hq : q ≠ patch.lastMiddleIndex) :
    KWRawTurnAdmissible patch.idealVertex
      (kwStairOddIndex i q.castSucc) := by
  have hqNext : q.val + 1 < M := by
    have hqLt := q.isLt
    by_contra h
    apply hq
    apply Fin.ext
    simp [KWAdaptivePatchedData.lastMiddleIndex]
    omega
  let qnext : Fin M := ⟨q.val + 1, hqNext⟩
  have hidx : q.succ = qnext.castSucc := by
    apply Fin.ext
    rfl
  have hnextEdge : kwRawEdge patch.idealVertex
      (kwStairEvenIndex i q.succ) =
      (1 / 2 : ℝ) *
        (patch.data.parameter i qnext.succ.castSucc.succ -
          patch.data.parameter i qnext.succ.castSucc.castSucc) *
            polygon.edgeVector i := by
    rw [hidx, patch.idealRawEdge_even_castSucc]
  rw [KWRawTurnAdmissible, kwStairOddIndex_castSucc_add_one,
    patch.idealRawEdge_odd_castSucc, hnextEdge]
  let d₁ : ℝ := (1 / 2) *
    (patch.data.parameter i q.succ.castSucc.succ -
      patch.data.parameter i q.succ.castSucc.castSucc)
  let d₂ : ℝ := (1 / 2) *
    (patch.data.parameter i qnext.succ.castSucc.succ -
      patch.data.parameter i qnext.succ.castSucc.castSucc)
  have hd₁ : 0 < d₁ := mul_pos (by norm_num) (patch.middleDelta_pos i q)
  have hd₂ : 0 < d₂ := mul_pos (by norm_num) (patch.middleDelta_pos i qnext)
  right
  refine ⟨d₂ / d₁, div_pos hd₂ hd₁, ?_⟩
  rw [← Complex.ofReal_sub, ← Complex.ofReal_mul,
    ← Complex.ofReal_sub, ← Complex.ofReal_mul]
  change (d₂ : ℂ) * polygon.edgeVector i =
    ((d₂ / d₁ : ℝ) : ℂ) * ((d₁ : ℂ) * polygon.edgeVector i)
  exact scaled_forward hd₁.ne'

private theorem KWAdaptivePatchedData.idealTurn_lastMiddle_connector
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    (i : Fin n) :
    KWRawTurnAdmissible patch.idealVertex
      (kwStairOddIndex i patch.lastMiddleIndex.castSucc) := by
  have hlast : patch.lastMiddleIndex.succ = Fin.last M := by
    apply Fin.ext
    simp [KWAdaptivePatchedData.lastMiddleIndex]
    have := patch.hM
    omega
  left
  rw [kwStairOddIndex_castSucc_add_one, hlast,
    patch.idealRawEdge_odd_castSucc, patch.idealRawEdge_even_last,
    ← Complex.ofReal_sub, mul_assoc,
    kwComplexCross_mul_real_left, kwComplexCross_mul_real_left]
  apply mul_ne_zero (by norm_num)
  apply mul_ne_zero
  · exact (patch.middleDelta_pos i patch.lastMiddleIndex).ne'
  · apply cross_full_axis_ne_zero (hcoords i).1 (hcoords i).2
    · have hi : i + 1 - 1 = i := by abel
      exact sub_ne_zero.mpr (by
        simpa only [hi] using (patch.connector (i + 1)).corner_ne_left)
    · have hi : i + 1 - 1 = i := by abel
      simpa only [hi] using (patch.connector (i + 1)).firstVector_axis

private theorem KWAdaptivePatchedData.idealTurn_connector
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) (i : Fin n) :
    KWRawTurnAdmissible patch.idealVertex
      (kwStairEvenIndex i (Fin.last M)) := by
  left
  rw [kwStairEvenIndex_add_one, patch.idealRawEdge_even_last,
    patch.idealRawEdge_odd_last]
  have hi : i + 1 - 1 = i := by abel
  simpa only [hi] using (patch.connector (i + 1)).turn_ne_zero

private theorem KWAdaptivePatchedData.idealTurn_connector_firstMiddle
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    (i : Fin n) :
    KWRawTurnAdmissible patch.idealVertex
      (kwStairOddIndex i (Fin.last M)) := by
  left
  rw [kwStairOddIndex_last_add_one, patch.idealRawEdge_odd_last]
  have hzero : (0 : Fin (M + 1)) = (0 : Fin M).castSucc := by
    apply Fin.ext
    rfl
  rw [hzero, patch.idealRawEdge_even_castSucc,
    ← Complex.ofReal_sub, mul_assoc,
    kwComplexCross_mul_real_right, kwComplexCross_mul_real_right]
  apply mul_ne_zero (by norm_num)
  apply mul_ne_zero
  · exact (patch.middleDelta_pos (i + 1) 0).ne'
  · apply cross_axis_full_ne_zero
    · exact sub_ne_zero.mpr (patch.connector (i + 1)).corner_ne_right.symm
    · have hi : i + 1 - 1 = i := by abel
      simpa only [hi] using (patch.connector (i + 1)).secondVector_axis
    · exact (hcoords (i + 1)).1
    · exact (hcoords (i + 1)).2

theorem KWAdaptivePatchedData.idealTurnAdmissible
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0) :
    ∀ j : Fin (n * (2 * (M + 1))),
      KWRawTurnAdmissible patch.idealVertex j := by
  intro j
  obtain ⟨i, k, rfl | rfl⟩ := kwStairIndex_even_or_odd j
  · refine Fin.lastCases ?_ (fun q ↦ ?_) k
    · exact patch.idealTurn_connector i
    · exact patch.idealTurn_evenMiddle i q
  · refine Fin.lastCases ?_ (fun q ↦ ?_) k
    · exact patch.idealTurn_connector_firstMiddle hcoords i
    · by_cases hq : q = patch.lastMiddleIndex
      · subst q
        exact patch.idealTurn_lastMiddle_connector hcoords i
      · exact patch.idealTurn_betweenMiddle i q hq

end StatMech.FrontierA
