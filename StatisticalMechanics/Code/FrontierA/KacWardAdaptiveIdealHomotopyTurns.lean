/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardAdaptiveIdealHomotopy





namespace StatMech.FrontierA

open Set

private theorem lineMap_scaled_forward
    {z : ℂ} {a b t : ℝ} (ha : a ≠ 0) (part : ℂ → ℂ) :
    AffineMap.lineMap ((b / 2 : ℝ) * z) (b * part z) t =
      (b / a : ℝ) *
        AffineMap.lineMap ((a / 2 : ℝ) * z) (a * part z) t := by
  rw [AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module]
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.real_smul,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im] <;>
    field_simp <;> ring

private theorem cross_horizontal_vertical_lineMap_ne_zero
    {z : ℂ} {a b t : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (ht : t ≠ 0) (hx : z.re ≠ 0) (hy : z.im ≠ 0) :
    kwComplexCross
        (AffineMap.lineMap ((a / 2 : ℝ) * z)
          (a * kwHorizontalPart z) t)
        (AffineMap.lineMap ((b / 2 : ℝ) * z)
          (b * kwVerticalPart z) t) ≠ 0 := by
  unfold kwComplexCross kwHorizontalPart kwVerticalPart
  simp only [AffineMap.lineMap_apply_module, Complex.add_re, Complex.add_im,
    Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  norm_num
  ring_nf
  have hta : t * a ≠ 0 := mul_ne_zero ht ha
  have htax : t * a * z.re ≠ 0 := mul_ne_zero hta hx
  have htaxb : t * a * z.re * b ≠ 0 := mul_ne_zero htax hb
  exact mul_ne_zero htaxb hy

private theorem cross_vertical_horizontal_lineMap_ne_zero
    {z : ℂ} {a b t : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (ht : t ≠ 0) (hx : z.re ≠ 0) (hy : z.im ≠ 0) :
    kwComplexCross
        (AffineMap.lineMap ((a / 2 : ℝ) * z)
          (a * kwVerticalPart z) t)
        (AffineMap.lineMap ((b / 2 : ℝ) * z)
          (b * kwHorizontalPart z) t) ≠ 0 := by
  rw [kwComplexCross_swap]
  exact neg_ne_zero.mpr
    (cross_horizontal_vertical_lineMap_ne_zero hb ha ht hx hy)

private theorem cross_horizontal_lineMap_vertical_axis_ne_zero
    {z w : ℂ} {a t : ℝ} (ha : 0 < a) (ht : t ∈ Icc (0 : ℝ) 1)
    (hx : z.re ≠ 0) (hwRe : w.re = 0) (hw : w ≠ 0) :
    kwComplexCross
        (AffineMap.lineMap ((a / 2 : ℝ) * z)
          (a * kwHorizontalPart z) t) w ≠ 0 := by
  have hwIm : w.im ≠ 0 := by
    intro him
    apply hw
    apply Complex.ext <;> assumption
  unfold kwComplexCross kwHorizontalPart
  simp only [AffineMap.lineMap_apply_module, Complex.add_re, Complex.add_im,
    Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, hwRe]
  norm_num
  have hcoef : 0 < (1 - t) * (a / 2) + t * a := by
    nlinarith [ht.1, ht.2]
  constructor
  · convert mul_ne_zero hcoef.ne' hx using 1 <;> ring
  · exact hwIm

private theorem cross_vertical_lineMap_horizontal_axis_ne_zero
    {z w : ℂ} {a t : ℝ} (ha : 0 < a) (ht : t ∈ Icc (0 : ℝ) 1)
    (hy : z.im ≠ 0) (hwIm : w.im = 0) (hw : w ≠ 0) :
    kwComplexCross
        (AffineMap.lineMap ((a / 2 : ℝ) * z)
          (a * kwVerticalPart z) t) w ≠ 0 := by
  have hwRe : w.re ≠ 0 := by
    intro hre
    apply hw
    apply Complex.ext <;> assumption
  unfold kwComplexCross kwVerticalPart
  simp only [AffineMap.lineMap_apply_module, Complex.add_re, Complex.add_im,
    Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, add_zero,
    hwIm, zero_sub]
  norm_num
  have hcoef : 0 < (1 - t) * (a / 2) + t * a := by
    nlinarith [ht.1, ht.2]
  constructor
  · convert mul_ne_zero hcoef.ne' hy using 1 <;> ring
  · exact hwRe

private theorem cross_horizontal_axis_vertical_lineMap_ne_zero
    {z w : ℂ} {a t : ℝ} (ha : 0 < a) (ht : t ∈ Icc (0 : ℝ) 1)
    (hwIm : w.im = 0) (hw : w ≠ 0) (hy : z.im ≠ 0) :
    kwComplexCross w
        (AffineMap.lineMap ((a / 2 : ℝ) * z)
          (a * kwVerticalPart z) t) ≠ 0 := by
  rw [kwComplexCross_swap]
  exact neg_ne_zero.mpr
    (cross_vertical_lineMap_horizontal_axis_ne_zero ha ht hy hwIm hw)

private theorem cross_vertical_axis_horizontal_lineMap_ne_zero
    {z w : ℂ} {a t : ℝ} (ha : 0 < a) (ht : t ∈ Icc (0 : ℝ) 1)
    (hwRe : w.re = 0) (hw : w ≠ 0) (hx : z.re ≠ 0) :
    kwComplexCross w
        (AffineMap.lineMap ((a / 2 : ℝ) * z)
          (a * kwHorizontalPart z) t) ≠ 0 := by
  rw [kwComplexCross_swap]
  exact neg_ne_zero.mpr
    (cross_horizontal_lineMap_vertical_axis_ne_zero ha ht hx hwRe hw)

private theorem KWAdaptivePatchedData.idealAxisHomotopy_evenMiddle_turn
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (i : Fin n) (q : Fin M) :
    KWRawTurnAdmissible (patch.idealAxisHomotopyVertex t)
      (kwStairEvenIndex i q.castSucc) := by
  rw [KWRawTurnAdmissible, kwStairEvenIndex_add_one,
    patch.idealAxisHomotopy_rawEdge_even_castSucc,
    patch.idealAxisHomotopy_rawEdge_odd_castSucc]
  let d : ℝ := patch.data.parameter i q.succ.castSucc.succ -
    patch.data.parameter i q.succ.castSucc.castSucc
  have hd : 0 < d := patch.middleDelta_pos i q
  by_cases hzero : t = 0
  · right
    refine ⟨1, by norm_num, ?_⟩
    subst t
    simp
  · left
    by_cases hv : patch.sliceUsesVerticalFirst i q
    · rw [if_pos hv, if_pos hv]
      convert cross_vertical_horizontal_lineMap_ne_zero
        (z := polygon.edgeVector i) (a := d) (b := d)
        hd.ne' hd.ne' hzero (hcoords i).1 (hcoords i).2 using 1 <;>
          dsimp only [d] <;>
          simp only [AffineMap.lineMap_apply_module, Complex.real_smul] <;>
          try unfold kwComplexCross <;>
          simp only [Complex.add_re, Complex.add_im, Complex.sub_re,
            Complex.sub_im, Complex.mul_re, Complex.mul_im,
            Complex.ofReal_re, Complex.ofReal_im] <;> ring
    · rw [if_neg hv, if_neg hv]
      convert cross_horizontal_vertical_lineMap_ne_zero
        (z := polygon.edgeVector i) (a := d) (b := d)
        hd.ne' hd.ne' hzero (hcoords i).1 (hcoords i).2 using 1 <;>
          dsimp only [d] <;>
          simp only [AffineMap.lineMap_apply_module, Complex.real_smul] <;>
          try unfold kwComplexCross <;>
          simp only [Complex.add_re, Complex.add_im, Complex.sub_re,
            Complex.sub_im, Complex.mul_re, Complex.mul_im,
            Complex.ofReal_re, Complex.ofReal_im] <;> ring

private theorem KWAdaptivePatchedData.idealAxisHomotopy_betweenMiddle_turn
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (i : Fin n) (q : Fin M) (hq : q ≠ patch.lastMiddleIndex) :
    KWRawTurnAdmissible (patch.idealAxisHomotopyVertex t)
      (kwStairOddIndex i q.castSucc) := by
  have hqNext : q.val + 1 < M := by
    by_contra h
    apply hq
    apply Fin.ext
    simp [KWAdaptivePatchedData.lastMiddleIndex]
    omega
  let qnext : Fin M := ⟨q.val + 1, hqNext⟩
  have hidx : q.succ = qnext.castSucc := by
    apply Fin.ext
    rfl
  have hnextIndex : kwStairEvenIndex i q.succ =
      kwStairEvenIndex i qnext.castSucc := congrArg (kwStairEvenIndex i) hidx
  rw [KWRawTurnAdmissible, kwStairOddIndex_castSucc_add_one,
    patch.idealAxisHomotopy_rawEdge_odd_castSucc,
    hnextIndex, patch.idealAxisHomotopy_rawEdge_even_castSucc]
  let d₁ : ℝ := patch.data.parameter i q.succ.castSucc.succ -
    patch.data.parameter i q.succ.castSucc.castSucc
  let d₂ : ℝ := patch.data.parameter i qnext.succ.castSucc.succ -
    patch.data.parameter i qnext.succ.castSucc.castSucc
  have hd₁ : 0 < d₁ := patch.middleDelta_pos i q
  have hd₂ : 0 < d₂ := patch.middleDelta_pos i qnext
  have hd₁ne : patch.data.parameter i q.succ.castSucc.succ -
      patch.data.parameter i q.succ.castSucc.castSucc ≠ 0 :=
    (patch.middleDelta_pos i q).ne'
  by_cases hzero : t = 0
  · right
    refine ⟨d₂ / d₁, div_pos hd₂ hd₁, ?_⟩
    subst t
    simp only [AffineMap.lineMap_apply_module, zero_smul, add_zero,
      one_smul]
    apply Complex.ext <;>
      dsimp only [d₁, d₂] <;>
      simp only [Complex.add_re, Complex.add_im, Complex.real_smul,
        Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im] <;>
      field_simp [hd₁ne] <;> ring
  · by_cases hv₁ : patch.sliceUsesVerticalFirst i q
    · by_cases hv₂ : patch.sliceUsesVerticalFirst i qnext
      · left
        rw [if_pos hv₁, if_pos hv₂]
        convert cross_horizontal_vertical_lineMap_ne_zero
          (z := polygon.edgeVector i) (a := d₁) (b := d₂)
          hd₁.ne' hd₂.ne' hzero (hcoords i).1 (hcoords i).2 using 1 <;>
            dsimp only [d₁, d₂] <;>
            simp only [AffineMap.lineMap_apply_module, Complex.real_smul] <;>
            try unfold kwComplexCross <;>
            simp only [Complex.add_re, Complex.add_im, Complex.sub_re,
              Complex.sub_im, Complex.mul_re, Complex.mul_im,
              Complex.ofReal_re, Complex.ofReal_im] <;> ring
      · right
        refine ⟨d₂ / d₁, div_pos hd₂ hd₁, ?_⟩
        rw [if_pos hv₁, if_neg hv₂]
        convert lineMap_scaled_forward
          (z := polygon.edgeVector i) (a := d₁) (b := d₂) (t := t)
          hd₁.ne' kwHorizontalPart using 1 <;>
            dsimp only [d₁, d₂] <;>
            simp only [AffineMap.lineMap_apply_module, Complex.real_smul] <;>
            push_cast <;> ring
    · by_cases hv₂ : patch.sliceUsesVerticalFirst i qnext
      · right
        refine ⟨d₂ / d₁, div_pos hd₂ hd₁, ?_⟩
        rw [if_neg hv₁, if_pos hv₂]
        convert lineMap_scaled_forward
          (z := polygon.edgeVector i) (a := d₁) (b := d₂) (t := t)
          hd₁.ne' kwVerticalPart using 1 <;>
            dsimp only [d₁, d₂] <;>
            simp only [AffineMap.lineMap_apply_module, Complex.real_smul] <;>
            push_cast <;> ring
      · left
        rw [if_neg hv₁, if_neg hv₂]
        convert cross_vertical_horizontal_lineMap_ne_zero
          (z := polygon.edgeVector i) (a := d₁) (b := d₂)
          hd₁.ne' hd₂.ne' hzero (hcoords i).1 (hcoords i).2 using 1 <;>
            dsimp only [d₁, d₂] <;>
            simp only [AffineMap.lineMap_apply_module, Complex.real_smul] <;>
            try unfold kwComplexCross <;>
            simp only [Complex.add_re, Complex.add_im, Complex.sub_re,
              Complex.sub_im, Complex.mul_re, Complex.mul_im,
              Complex.ofReal_re, Complex.ofReal_im] <;> ring

private theorem KWAdaptivePatchedData.idealAxisHomotopy_lastMiddle_turn
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (i : Fin n) :
    KWRawTurnAdmissible (patch.idealAxisHomotopyVertex t)
      (kwStairOddIndex i patch.lastMiddleIndex.castSucc) := by
  have hlast : patch.lastMiddleIndex.succ = Fin.last M := by
    apply Fin.ext
    simp [KWAdaptivePatchedData.lastMiddleIndex]
    have := patch.hM
    omega
  rw [KWRawTurnAdmissible, kwStairOddIndex_castSucc_add_one, hlast,
    patch.idealAxisHomotopy_rawEdge_odd_castSucc,
    patch.idealAxisHomotopy_rawEdge_even_last]
  left
  let d : ℝ := patch.data.parameter i
      patch.lastMiddleIndex.succ.castSucc.succ -
    patch.data.parameter i patch.lastMiddleIndex.succ.castSucc.castSucc
  have hd : 0 < d := patch.middleDelta_pos i patch.lastMiddleIndex
  let w : ℂ := (patch.connector (i + 1)).corner -
    patch.alpha (i + 1) * (-polygon.edgeVector i)
  have hw : w ≠ 0 := by
    apply sub_ne_zero.mpr
    have hi : i + 1 - 1 = i := by abel
    simpa only [w, hi] using (patch.connector (i + 1)).corner_ne_left
  have hi : i + 1 - 1 = i := by abel
  have hwEq : w =
      if patch.connectorUsesVerticalFirst (i + 1) then
        kwVerticalPart (patch.beta * polygon.edgeVector (i + 1) -
          patch.alpha (i + 1) * (-polygon.edgeVector i))
      else
        kwHorizontalPart (patch.beta * polygon.edgeVector (i + 1) -
          patch.alpha (i + 1) * (-polygon.edgeVector i)) := by
    simpa only [w, hi] using patch.connector_first_eq (i + 1)
  by_cases hv : patch.connectorUsesVerticalFirst (i + 1)
  · have hs : patch.sliceUsesVerticalFirst i patch.lastMiddleIndex :=
      (patch.sliceUsesVerticalFirst_last_iff i).mpr hv
    rw [if_pos hs]
    have hwRe : w.re = 0 := by
      rw [hwEq, if_pos hv]
      simp [kwVerticalPart]
    convert cross_horizontal_lineMap_vertical_axis_ne_zero
      (z := polygon.edgeVector i) (w := w) (a := d)
      hd ht (hcoords i).1 hwRe hw using 1 <;>
        dsimp only [d, w] <;>
        simp only [AffineMap.lineMap_apply_module, Complex.real_smul] <;>
        push_cast <;> ring
  · have hs : ¬patch.sliceUsesVerticalFirst i patch.lastMiddleIndex :=
      fun hs ↦ hv ((patch.sliceUsesVerticalFirst_last_iff i).mp hs)
    rw [if_neg hs]
    have hwIm : w.im = 0 := by
      rw [hwEq, if_neg hv]
      simp [kwHorizontalPart]
    convert cross_vertical_lineMap_horizontal_axis_ne_zero
      (z := polygon.edgeVector i) (w := w) (a := d)
      hd ht (hcoords i).2 hwIm hw using 1 <;>
        dsimp only [d, w] <;>
        simp only [AffineMap.lineMap_apply_module, Complex.real_smul] <;>
        push_cast <;> ring

private theorem KWAdaptivePatchedData.idealAxisHomotopy_connector_turn
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (t : ℝ) (i : Fin n) :
    KWRawTurnAdmissible (patch.idealAxisHomotopyVertex t)
      (kwStairEvenIndex i (Fin.last M)) := by
  left
  rw [kwStairEvenIndex_add_one,
    patch.idealAxisHomotopy_rawEdge_even_last,
    patch.idealAxisHomotopy_rawEdge_odd_last]
  have hi : i + 1 - 1 = i := by abel
  simpa only [hi] using (patch.connector (i + 1)).turn_ne_zero

private theorem KWAdaptivePatchedData.idealAxisHomotopy_firstMiddle_turn
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (i : Fin n) :
    KWRawTurnAdmissible (patch.idealAxisHomotopyVertex t)
      (kwStairOddIndex i (Fin.last M)) := by
  rw [KWRawTurnAdmissible, kwStairOddIndex_last_add_one,
    patch.idealAxisHomotopy_rawEdge_odd_last]
  have hzero : (0 : Fin (M + 1)) = (0 : Fin M).castSucc := by
    apply Fin.ext
    rfl
  rw [hzero, patch.idealAxisHomotopy_rawEdge_even_castSucc]
  left
  let d : ℝ := patch.data.parameter (i + 1) (0 : Fin M).succ.castSucc.succ -
    patch.data.parameter (i + 1) (0 : Fin M).succ.castSucc.castSucc
  have hd : 0 < d := patch.middleDelta_pos (i + 1) 0
  let w : ℂ := patch.beta * polygon.edgeVector (i + 1) -
    (patch.connector (i + 1)).corner
  have hw : w ≠ 0 :=
    sub_ne_zero.mpr (patch.connector (i + 1)).corner_ne_right.symm
  have hi : i + 1 - 1 = i := by abel
  have hwEq : w =
      if patch.connectorUsesVerticalFirst (i + 1) then
        kwHorizontalPart (patch.beta * polygon.edgeVector (i + 1) -
          patch.alpha (i + 1) * (-polygon.edgeVector i))
      else
        kwVerticalPart (patch.beta * polygon.edgeVector (i + 1) -
          patch.alpha (i + 1) * (-polygon.edgeVector i)) := by
    simpa only [w, hi] using patch.connector_second_eq (i + 1)
  by_cases hv : patch.connectorUsesVerticalFirst (i + 1)
  · have hs : patch.sliceUsesVerticalFirst (i + 1) 0 :=
      (patch.sliceUsesVerticalFirst_zero_iff (i + 1)).mpr hv
    rw [if_pos hs]
    have hwIm : w.im = 0 := by
      rw [hwEq, if_pos hv]
      simp [kwHorizontalPart]
    convert cross_horizontal_axis_vertical_lineMap_ne_zero
      (z := polygon.edgeVector (i + 1)) (w := w) (a := d)
      hd ht hwIm hw (hcoords (i + 1)).2 using 1 <;>
        dsimp only [d, w] <;>
        simp only [AffineMap.lineMap_apply_module, Complex.real_smul] <;>
        push_cast <;> ring
  · have hs : ¬patch.sliceUsesVerticalFirst (i + 1) 0 :=
      fun hs ↦ hv ((patch.sliceUsesVerticalFirst_zero_iff (i + 1)).mp hs)
    rw [if_neg hs]
    have hwRe : w.re = 0 := by
      rw [hwEq, if_neg hv]
      simp [kwVerticalPart]
    convert cross_vertical_axis_horizontal_lineMap_ne_zero
      (z := polygon.edgeVector (i + 1)) (w := w) (a := d)
      hd ht hwRe hw (hcoords (i + 1)).1 using 1 <;>
        dsimp only [d, w] <;>
        simp only [AffineMap.lineMap_apply_module, Complex.real_smul] <;>
        push_cast <;> ring



theorem KWAdaptivePatchedData.idealAxisHomotopy_turnAdmissible
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∀ j : Fin (n * (2 * (M + 1))),
      KWRawTurnAdmissible (patch.idealAxisHomotopyVertex t) j := by
  intro j
  obtain ⟨i, k, rfl | rfl⟩ := kwStairIndex_even_or_odd j
  · refine Fin.lastCases ?_ (fun q ↦ ?_) k
    · exact patch.idealAxisHomotopy_connector_turn t i
    · exact patch.idealAxisHomotopy_evenMiddle_turn hcoords ht i q
  · refine Fin.lastCases ?_ (fun q ↦ ?_) k
    · exact patch.idealAxisHomotopy_firstMiddle_turn hcoords ht i
    · by_cases hq : q = patch.lastMiddleIndex
      · subst q
        exact patch.idealAxisHomotopy_lastMiddle_turn hcoords ht i
      · exact patch.idealAxisHomotopy_betweenMiddle_turn hcoords ht i q hq

end StatMech.FrontierA
