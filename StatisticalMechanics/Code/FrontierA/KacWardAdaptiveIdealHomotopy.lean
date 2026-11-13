/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardAdaptiveIdealSimple





namespace StatMech.FrontierA

open Set

noncomputable def KWAdaptivePatchedData.idealAxisHomotopyVertex
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (t : ℝ) (j : Fin (n * (2 * (M + 1)))) : ℂ :=
  AffineMap.lineMap (patch.idealVertex j) (patch.vertex j) t

@[simp] theorem KWAdaptivePatchedData.idealAxisHomotopyVertex_zero
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) :
    patch.idealAxisHomotopyVertex 0 = patch.idealVertex := by
  funext j
  simp [KWAdaptivePatchedData.idealAxisHomotopyVertex]

@[simp] theorem KWAdaptivePatchedData.idealAxisHomotopyVertex_one
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) :
    patch.idealAxisHomotopyVertex 1 = patch.vertex := by
  funext j
  simp [KWAdaptivePatchedData.idealAxisHomotopyVertex]

theorem KWAdaptivePatchedData.idealAxisHomotopyVertex_continuous
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (j : Fin (n * (2 * (M + 1)))) :
    Continuous fun t ↦ patch.idealAxisHomotopyVertex t j := by
  unfold KWAdaptivePatchedData.idealAxisHomotopyVertex
  fun_prop

theorem KWAdaptivePatchedData.idealAxisHomotopy_rawEdge
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (t : ℝ) (j : Fin (n * (2 * (M + 1)))) :
    kwRawEdge (patch.idealAxisHomotopyVertex t) j =
      AffineMap.lineMap (kwRawEdge patch.idealVertex j)
        (kwRawEdge patch.vertex j) t := by
  unfold kwRawEdge KWAdaptivePatchedData.idealAxisHomotopyVertex
  simp only [AffineMap.lineMap_apply_module, Complex.real_smul]
  push_cast
  ring

theorem KWAdaptivePatchedData.idealAxisHomotopy_rawEdge_even_castSucc
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (t : ℝ) (i : Fin n) (q : Fin M) :
    kwRawEdge (patch.idealAxisHomotopyVertex t)
        (kwStairEvenIndex i q.castSucc) =
      AffineMap.lineMap
        (((patch.data.parameter i q.succ.castSucc.succ -
          patch.data.parameter i q.succ.castSucc.castSucc) / 2 : ℝ) *
            polygon.edgeVector i)
        ((patch.data.parameter i q.succ.castSucc.succ -
          patch.data.parameter i q.succ.castSucc.castSucc) *
            (if patch.sliceUsesVerticalFirst i q then
              kwVerticalPart (polygon.edgeVector i)
            else kwHorizontalPart (polygon.edgeVector i))) t := by
  rw [patch.idealAxisHomotopy_rawEdge,
    patch.idealRawEdge_even_castSucc, patch.rawEdge_even_castSucc]
  simp only [AffineMap.lineMap_apply_module, Complex.real_smul]
  push_cast
  ring

theorem KWAdaptivePatchedData.idealAxisHomotopy_rawEdge_odd_castSucc
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (t : ℝ) (i : Fin n) (q : Fin M) :
    kwRawEdge (patch.idealAxisHomotopyVertex t)
        (kwStairOddIndex i q.castSucc) =
      AffineMap.lineMap
        (((patch.data.parameter i q.succ.castSucc.succ -
          patch.data.parameter i q.succ.castSucc.castSucc) / 2 : ℝ) *
            polygon.edgeVector i)
        ((patch.data.parameter i q.succ.castSucc.succ -
          patch.data.parameter i q.succ.castSucc.castSucc) *
            (if patch.sliceUsesVerticalFirst i q then
              kwHorizontalPart (polygon.edgeVector i)
            else kwVerticalPart (polygon.edgeVector i))) t := by
  rw [patch.idealAxisHomotopy_rawEdge,
    patch.idealRawEdge_odd_castSucc, patch.rawEdge_odd_castSucc]
  simp only [AffineMap.lineMap_apply_module, Complex.real_smul]
  push_cast
  ring

@[simp] theorem KWAdaptivePatchedData.idealAxisHomotopy_rawEdge_even_last
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (t : ℝ) (i : Fin n) :
    kwRawEdge (patch.idealAxisHomotopyVertex t)
        (kwStairEvenIndex i (Fin.last M)) =
      (patch.connector (i + 1)).corner -
        patch.alpha (i + 1) * (-polygon.edgeVector i) := by
  rw [patch.idealAxisHomotopy_rawEdge,
    patch.idealRawEdge_even_last, patch.rawEdge_even_last]
  simp [AffineMap.lineMap_apply_module]

@[simp] theorem KWAdaptivePatchedData.idealAxisHomotopy_rawEdge_odd_last
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (t : ℝ) (i : Fin n) :
    kwRawEdge (patch.idealAxisHomotopyVertex t)
        (kwStairOddIndex i (Fin.last M)) =
      patch.beta * polygon.edgeVector (i + 1) -
        (patch.connector (i + 1)).corner := by
  rw [patch.idealAxisHomotopy_rawEdge,
    patch.idealRawEdge_odd_last, patch.rawEdge_odd_last]
  simp [AffineMap.lineMap_apply_module]

private theorem lineMap_full_horizontal_ne_zero
    {z : ℂ} {d t : ℝ} (hd : 0 < d) (ht : t ∈ Icc (0 : ℝ) 1)
    (hzRe : z.re ≠ 0) :
    AffineMap.lineMap ((d / 2 : ℝ) * z)
      (d * kwHorizontalPart z) t ≠ 0 := by
  intro hzero
  have hre := congrArg Complex.re hzero
  rw [AffineMap.lineMap_apply_module] at hre
  unfold kwHorizontalPart at hre
  simp only [Complex.add_re, Complex.sub_re, Complex.real_smul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hre
  norm_num at hre
  have hcoef : 0 < (1 - t) * (d / 2) + t * d := by
    nlinarith [ht.1, ht.2]
  apply (mul_ne_zero hcoef.ne' hzRe)
  calc
    ((1 - t) * (d / 2) + t * d) * z.re =
        (1 - t) * (d / 2 * z.re) + t * (d * z.re) := by ring
    _ = 0 := hre

private theorem lineMap_full_vertical_ne_zero
    {z : ℂ} {d t : ℝ} (hd : 0 < d) (ht : t ∈ Icc (0 : ℝ) 1)
    (hzIm : z.im ≠ 0) :
    AffineMap.lineMap ((d / 2 : ℝ) * z)
      (d * kwVerticalPart z) t ≠ 0 := by
  intro hzero
  have him := congrArg Complex.im hzero
  rw [AffineMap.lineMap_apply_module] at him
  unfold kwVerticalPart at him
  simp only [Complex.add_im, Complex.sub_im, Complex.real_smul,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, zero_mul, mul_zero, add_zero,
    mul_one] at him
  norm_num at him
  have hcoef : 0 < (1 - t) * (d / 2) + t * d := by
    nlinarith [ht.1, ht.2]
  apply (mul_ne_zero hcoef.ne' hzIm)
  calc
    ((1 - t) * (d / 2) + t * d) * z.im =
        (1 - t) * (d / 2 * z.im) + t * (d * z.im) := by ring
    _ = 0 := him

private theorem KWAdaptivePatchedData.idealAxisHomotopy_evenMiddle_ne_zero
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (i : Fin n) (q : Fin M) :
    kwRawEdge (patch.idealAxisHomotopyVertex t)
      (kwStairEvenIndex i q.castSucc) ≠ 0 := by
  rw [patch.idealAxisHomotopy_rawEdge,
    patch.idealRawEdge_even_castSucc,
    patch.rawEdge_even_castSucc, ← Complex.ofReal_sub,
    ← Complex.ofReal_mul]
  by_cases hv : patch.sliceUsesVerticalFirst i q
  · rw [if_pos hv]
    convert lineMap_full_vertical_ne_zero
      (patch.middleDelta_pos i q) ht (hcoords i).2 using 1 <;> ring
  · rw [if_neg hv]
    convert lineMap_full_horizontal_ne_zero
      (patch.middleDelta_pos i q) ht (hcoords i).1 using 1 <;> ring

private theorem KWAdaptivePatchedData.idealAxisHomotopy_oddMiddle_ne_zero
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (i : Fin n) (q : Fin M) :
    kwRawEdge (patch.idealAxisHomotopyVertex t)
      (kwStairOddIndex i q.castSucc) ≠ 0 := by
  rw [patch.idealAxisHomotopy_rawEdge,
    patch.idealRawEdge_odd_castSucc,
    patch.rawEdge_odd_castSucc, ← Complex.ofReal_sub,
    ← Complex.ofReal_mul]
  by_cases hv : patch.sliceUsesVerticalFirst i q
  · rw [if_pos hv]
    convert lineMap_full_horizontal_ne_zero
      (patch.middleDelta_pos i q) ht (hcoords i).1 using 1 <;> ring
  · rw [if_neg hv]
    convert lineMap_full_vertical_ne_zero
      (patch.middleDelta_pos i q) ht (hcoords i).2 using 1 <;> ring

private theorem KWAdaptivePatchedData.idealAxisHomotopy_evenConnector_ne_zero
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (t : ℝ) (i : Fin n) :
    kwRawEdge (patch.idealAxisHomotopyVertex t)
      (kwStairEvenIndex i (Fin.last M)) ≠ 0 := by
  rw [patch.idealAxisHomotopy_rawEdge,
    patch.idealRawEdge_even_last, patch.rawEdge_even_last]
  have hw : (patch.connector (i + 1)).corner -
      patch.alpha (i + 1) * (-polygon.edgeVector i) ≠ 0 := by
    apply sub_ne_zero.mpr
    have hi : i + 1 - 1 = i := by abel
    simpa only [hi] using (patch.connector (i + 1)).corner_ne_left
  simpa [AffineMap.lineMap_apply_module] using hw

private theorem KWAdaptivePatchedData.idealAxisHomotopy_oddConnector_ne_zero
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (t : ℝ) (i : Fin n) :
    kwRawEdge (patch.idealAxisHomotopyVertex t)
      (kwStairOddIndex i (Fin.last M)) ≠ 0 := by
  rw [patch.idealAxisHomotopy_rawEdge,
    patch.idealRawEdge_odd_last, patch.rawEdge_odd_last]
  have hw : patch.beta * polygon.edgeVector (i + 1) -
      (patch.connector (i + 1)).corner ≠ 0 :=
    sub_ne_zero.mpr (patch.connector (i + 1)).corner_ne_right.symm
  simpa [AffineMap.lineMap_apply_module] using hw

theorem KWAdaptivePatchedData.idealAxisHomotopy_rawEdge_ne_zero
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∀ j : Fin (n * (2 * (M + 1))),
      kwRawEdge (patch.idealAxisHomotopyVertex t) j ≠ 0 := by
  intro j
  obtain ⟨i, k, rfl | rfl⟩ := kwStairIndex_even_or_odd j
  · refine Fin.lastCases ?_ (fun q ↦ ?_) k
    · exact patch.idealAxisHomotopy_evenConnector_ne_zero t i
    · exact patch.idealAxisHomotopy_evenMiddle_ne_zero hcoords ht i q
  · refine Fin.lastCases ?_ (fun q ↦ ?_) k
    · exact patch.idealAxisHomotopy_oddConnector_ne_zero t i
    · exact patch.idealAxisHomotopy_oddMiddle_ne_zero hcoords ht i q

end StatMech.FrontierA
