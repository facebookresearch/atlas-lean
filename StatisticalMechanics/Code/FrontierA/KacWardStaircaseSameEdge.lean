/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardStaircaseEndpointPatch









namespace StatMech.FrontierA

open scoped Convex
open Set

private theorem horizontal_point_im
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (i : Fin n) (k : Fin S) {z : ℂ}
    (hz : z ∈ segment ℝ (data.base i k.castSucc) (data.corner i k)) :
    z.im = (polygon.vertex i).im +
      data.parameter i k.castSucc * (polygon.edgeVector i).im := by
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  rw [AffineMap.lineMap_apply_module]
  simp only [Complex.add_im, Complex.real_smul, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, data.base_im, data.corner_im]
  ring

private theorem horizontal_point_re_parameter
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (i : Fin n) (k : Fin S) {z : ℂ}
    (hz : z ∈ segment ℝ (data.base i k.castSucc) (data.corner i k)) :
    ∃ u ∈ Icc (data.parameter i k.castSucc) (data.parameter i k.succ),
      z.re = (polygon.vertex i).re + u * (polygon.edgeVector i).re := by
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  let u := (1 - t) * data.parameter i k.castSucc +
    t * data.parameter i k.succ
  refine ⟨u, ?_, ?_⟩
  · constructor <;> dsimp only [u]
    · nlinarith [ht.1, ht.2, data.parameter_strict i k]
    · nlinarith [ht.1, ht.2, data.parameter_strict i k]
  · rw [AffineMap.lineMap_apply_module]
    simp only [Complex.add_re, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, data.base_re, data.corner_re]
    dsimp only [u]
    ring

private theorem vertical_point_re
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (i : Fin n) (k : Fin S) {z : ℂ}
    (hz : z ∈ segment ℝ (data.corner i k) (data.base i k.succ)) :
    z.re = (polygon.vertex i).re +
      data.parameter i k.succ * (polygon.edgeVector i).re := by
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  rw [AffineMap.lineMap_apply_module]
  simp only [Complex.add_re, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, data.corner_re, data.base_re]
  ring

private theorem vertical_point_im_parameter
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (i : Fin n) (k : Fin S) {z : ℂ}
    (hz : z ∈ segment ℝ (data.corner i k) (data.base i k.succ)) :
    ∃ u ∈ Icc (data.parameter i k.castSucc) (data.parameter i k.succ),
      z.im = (polygon.vertex i).im + u * (polygon.edgeVector i).im := by
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  let u := (1 - t) * data.parameter i k.castSucc +
    t * data.parameter i k.succ
  refine ⟨u, ?_, ?_⟩
  · constructor <;> dsimp only [u]
    · nlinarith [ht.1, ht.2, data.parameter_strict i k]
    · nlinarith [ht.1, ht.2, data.parameter_strict i k]
  · rw [AffineMap.lineMap_apply_module]
    simp only [Complex.add_im, Complex.real_smul, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, data.corner_im, data.base_im]
    dsimp only [u]
    ring

private theorem parameter_eq_of_scaled_coordinate
    {a x s t : ℝ} (hx : x ≠ 0) (h : a + s * x = a + t * x) :
    s = t := by
  apply mul_right_cancel₀ hx
  linarith


theorem KWStairParameterData.horizontalLeg_disjoint
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    (i : Fin n) {k q : Fin S} (hkq : k ≠ q) :
    Disjoint
      (segment ℝ (data.base i k.castSucc) (data.corner i k))
      (segment ℝ (data.base i q.castSucc) (data.corner i q)) := by
  rw [Set.disjoint_left]
  intro z hzk hzq
  have hk := horizontal_point_im data i k hzk
  have hq := horizontal_point_im data i q hzq
  have hp : data.parameter i k.castSucc = data.parameter i q.castSucc :=
    parameter_eq_of_scaled_coordinate (hcoords i).2 (hk.symm.trans hq)
  have hindex : k.castSucc = q.castSucc :=
    (data.parameter_strictMono i).injective hp
  exact hkq (Fin.castSucc_injective S hindex)


theorem KWStairParameterData.verticalLeg_disjoint
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    (i : Fin n) {k q : Fin S} (hkq : k ≠ q) :
    Disjoint
      (segment ℝ (data.corner i k) (data.base i k.succ))
      (segment ℝ (data.corner i q) (data.base i q.succ)) := by
  rw [Set.disjoint_left]
  intro z hzk hzq
  have hk := vertical_point_re data i k hzk
  have hq := vertical_point_re data i q hzq
  have hp : data.parameter i k.succ = data.parameter i q.succ :=
    parameter_eq_of_scaled_coordinate (hcoords i).1 (hk.symm.trans hq)
  have hindex : k.succ = q.succ :=
    (data.parameter_strictMono i).injective hp
  exact hkq (Fin.succ_injective _ hindex)


theorem KWStairParameterData.horizontalLeg_disjoint_verticalLeg
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    (i : Fin n) {k q : Fin S} (hkq : k ≠ q)
    (hprev : q.val + 1 ≠ k.val) :
    Disjoint
      (segment ℝ (data.base i k.castSucc) (data.corner i k))
      (segment ℝ (data.corner i q) (data.base i q.succ)) := by
  rw [Set.disjoint_left]
  intro z hzh hzv
  obtain ⟨u, hu, hre⟩ := horizontal_point_re_parameter data i k hzh
  obtain ⟨v, hv, him⟩ := vertical_point_im_parameter data i q hzv
  have hHorizontalIm := horizontal_point_im data i k hzh
  have hVerticalRe := vertical_point_re data i q hzv
  have hpu : u = data.parameter i q.succ :=
    parameter_eq_of_scaled_coordinate (hcoords i).1
      (hre.symm.trans hVerticalRe)
  have hpv : data.parameter i k.castSucc = v :=
    parameter_eq_of_scaled_coordinate (hcoords i).2
      (hHorizontalIm.symm.trans him)
  rcases lt_or_gt_of_ne hkq with hkqLt | hqkLt
  · have hparam : data.parameter i k.succ < data.parameter i q.succ :=
      data.parameter_strictMono i (by simpa using hkqLt)
    linarith [hu.2]
  · have hparam : data.parameter i q.succ < data.parameter i k.castSucc := by
      apply data.parameter_strictMono i
      have : q.val + 1 < k.val := by omega
      simpa using this
    linarith [hv.2]



theorem KWStairParameterData.verticalLeg_disjoint_horizontalLeg
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    (i : Fin n) {k q : Fin S} (hkq : k ≠ q)
    (hsucc : k.val + 1 ≠ q.val) :
    Disjoint
      (segment ℝ (data.corner i k) (data.base i k.succ))
      (segment ℝ (data.base i q.castSucc) (data.corner i q)) := by
  rw [Set.disjoint_left]
  intro z hzv hzh
  obtain ⟨u, hu, him⟩ := vertical_point_im_parameter data i k hzv
  obtain ⟨v, hv, hre⟩ := horizontal_point_re_parameter data i q hzh
  have hVerticalRe := vertical_point_re data i k hzv
  have hHorizontalIm := horizontal_point_im data i q hzh
  have hpv : data.parameter i k.succ = v :=
    parameter_eq_of_scaled_coordinate (hcoords i).1
      (hVerticalRe.symm.trans hre)
  have hpu : u = data.parameter i q.castSucc :=
    parameter_eq_of_scaled_coordinate (hcoords i).2
      (him.symm.trans hHorizontalIm)
  rcases lt_or_gt_of_ne hkq with hkqLt | hqkLt
  · have hkSuccLe : k.val + 1 < q.val := by omega
    have hparam : data.parameter i k.succ <
        data.parameter i q.castSucc := by
      apply data.parameter_strictMono i
      simpa using hkSuccLe
    linarith [hv.1]
  · have hparam : data.parameter i q.castSucc <
        data.parameter i k.castSucc := by
      apply data.parameter_strictMono i
      simpa using hqkLt
    linarith [hu.1]

@[simp] theorem KWStairParameterData.rawClosedEdge_even
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (i : Fin n) (k : Fin S) :
    kwRawClosedEdge data.vertex (kwStairEvenIndex i k) =
      segment ℝ (data.base i k.castSucc) (data.corner i k) := by
  unfold kwRawClosedEdge
  rw [kwStairEvenIndex_add_one, data.vertex_even, data.vertex_odd]

@[simp] theorem KWStairParameterData.rawClosedEdge_odd
    {n M : ℕ} [NeZero n]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := M + 1) polygon)
    (i : Fin n) (k : Fin (M + 1)) :
    kwRawClosedEdge data.vertex (kwStairOddIndex i k) =
      segment ℝ (data.corner i k) (data.base i k.succ) := by
  refine Fin.lastCases ?_ (fun q ↦ ?_) k
  · unfold kwRawClosedEdge
    rw [data.vertex_odd, data.vertex_odd_last_succ]
    have hindex : (Fin.last M).succ = Fin.last (M + 1) := by
      apply Fin.ext
      rfl
    rw [hindex, data.base_last]
  · unfold kwRawClosedEdge
    rw [data.vertex_odd, kwStairOddIndex_castSucc_add_one,
      data.vertex_even]
    congr 2



theorem KWStairParameterData.rawClosedEdge_even_disjoint_even
    {n M : ℕ} [NeZero n]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := M + 1) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    (i : Fin n) (k q : Fin (M + 1))
    (hnon : KWEdgesNonincident (kwStairEvenIndex i k)
      (kwStairEvenIndex i q)) :
    Disjoint (kwRawClosedEdge data.vertex (kwStairEvenIndex i k))
      (kwRawClosedEdge data.vertex (kwStairEvenIndex i q)) := by
  rw [data.rawClosedEdge_even, data.rawClosedEdge_even]
  apply data.horizontalLeg_disjoint hcoords i
  intro hkq
  subst q
  exact hnon.1 rfl



theorem KWStairParameterData.rawClosedEdge_odd_disjoint_odd
    {n M : ℕ} [NeZero n]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := M + 1) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    (i : Fin n) (k q : Fin (M + 1))
    (hnon : KWEdgesNonincident (kwStairOddIndex i k)
      (kwStairOddIndex i q)) :
    Disjoint (kwRawClosedEdge data.vertex (kwStairOddIndex i k))
      (kwRawClosedEdge data.vertex (kwStairOddIndex i q)) := by
  rw [data.rawClosedEdge_odd, data.rawClosedEdge_odd]
  apply data.verticalLeg_disjoint hcoords i
  intro hkq
  subst q
  exact hnon.1 rfl



theorem KWStairParameterData.rawClosedEdge_even_disjoint_odd
    {n M : ℕ} [NeZero n]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := M + 1) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    (i : Fin n) (k q : Fin (M + 1))
    (hnon : KWEdgesNonincident (kwStairEvenIndex i k)
      (kwStairOddIndex i q)) :
    Disjoint (kwRawClosedEdge data.vertex (kwStairEvenIndex i k))
      (kwRawClosedEdge data.vertex (kwStairOddIndex i q)) := by
  rw [data.rawClosedEdge_even, data.rawClosedEdge_odd]
  apply data.horizontalLeg_disjoint_verticalLeg hcoords i
  · intro hkq
    subst q
    exact hnon.2.2 (kwStairEvenIndex_add_one i k)
  · intro hqk
    have hqNotLast : q ≠ Fin.last M := by
      intro hlast
      subst q
      have hklt := k.isLt
      simp only [Fin.val_last] at hqk
      omega
    obtain ⟨p, rfl⟩ := Fin.eq_castSucc_of_ne_last hqNotLast
    have hk : k = p.succ := by
      apply Fin.ext
      simpa only [Fin.val_castSucc, Fin.val_succ] using hqk.symm
    subst k
    exact hnon.2.1 (kwStairOddIndex_castSucc_add_one i p).symm



theorem KWStairParameterData.rawClosedEdge_odd_disjoint_even
    {n M : ℕ} [NeZero n]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := M + 1) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    (i : Fin n) (k q : Fin (M + 1))
    (hnon : KWEdgesNonincident (kwStairOddIndex i k)
      (kwStairEvenIndex i q)) :
    Disjoint (kwRawClosedEdge data.vertex (kwStairOddIndex i k))
      (kwRawClosedEdge data.vertex (kwStairEvenIndex i q)) := by
  rw [data.rawClosedEdge_odd, data.rawClosedEdge_even]
  apply data.verticalLeg_disjoint_horizontalLeg hcoords i
  · intro hkq
    subst q
    exact hnon.2.1 (kwStairEvenIndex_add_one i k).symm
  · intro hkq
    have hkNotLast : k ≠ Fin.last M := by
      intro hlast
      subst k
      have hqlt := q.isLt
      simp only [Fin.val_last] at hkq
      omega
    obtain ⟨p, rfl⟩ := Fin.eq_castSucc_of_ne_last hkNotLast
    have hq : q = p.succ := by
      apply Fin.ext
      simpa only [Fin.val_castSucc, Fin.val_succ] using hkq.symm
    subst q
    exact hnon.2.2 (kwStairOddIndex_castSucc_add_one i p)



theorem KWStairParameterData.rawClosedEdges_disjoint_sameOwner
    {n M : ℕ} [NeZero n]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := M + 1) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    (i : Fin n) (j l : Fin (n * (2 * (M + 1))))
    (hj : (finProdFinEquiv.symm j).1 = i)
    (hl : (finProdFinEquiv.symm l).1 = i)
    (hnon : KWEdgesNonincident j l) :
    Disjoint (kwRawClosedEdge data.vertex j)
      (kwRawClosedEdge data.vertex l) := by
  obtain ⟨ij, k, rfl | rfl⟩ := kwStairIndex_even_or_odd j
  · obtain ⟨il, q, rfl | rfl⟩ := kwStairIndex_even_or_odd l
    · simp only [kwStairEvenIndex, Equiv.symm_apply_apply] at hj hl
      subst ij
      subst il
      exact data.rawClosedEdge_even_disjoint_even hcoords i k q hnon
    · simp only [kwStairEvenIndex, kwStairOddIndex,
        Equiv.symm_apply_apply] at hj hl
      subst ij
      subst il
      exact data.rawClosedEdge_even_disjoint_odd hcoords i k q hnon
  · obtain ⟨il, q, rfl | rfl⟩ := kwStairIndex_even_or_odd l
    · simp only [kwStairOddIndex, kwStairEvenIndex,
        Equiv.symm_apply_apply] at hj hl
      subst ij
      subst il
      exact data.rawClosedEdge_odd_disjoint_even hcoords i k q hnon
    · simp only [kwStairOddIndex, Equiv.symm_apply_apply] at hj hl
      subst ij
      subst il
      exact data.rawClosedEdge_odd_disjoint_odd hcoords i k q hnon

end StatMech.FrontierA
