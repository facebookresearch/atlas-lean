/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardAdaptiveSameEdgeMiddle
import Code.FrontierA.KacWardAdaptiveIdealLocalSeparation





namespace StatMech.FrontierA

open scoped NNReal
open Set

private theorem mem_segment_re_eq
    {a b z : ℂ} (h : b.re = a.re) (hz : z ∈ segment ℝ a b) :
    z.re = a.re := by
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨t, _ht, rfl⟩ := hz
  rw [AffineMap.lineMap_apply_module]
  simp only [Complex.add_re, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, h]
  ring

private theorem mem_segment_im_eq
    {a b z : ℂ} (h : b.im = a.im) (hz : z ∈ segment ℝ a b) :
    z.im = a.im := by
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨t, _ht, rfl⟩ := hz
  rw [AffineMap.lineMap_apply_module]
  simp only [Complex.add_im, Complex.real_smul, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, h]
  ring

private theorem parameter_eq_of_scaled_coordinate
    {a x s t : ℝ} (hx : x ≠ 0) (h : a + s * x = a + t * x) :
    s = t := by
  apply mul_right_cancel₀ hx
  linarith

private theorem isCompact_complexSegment (a b : ℂ) :
    IsCompact (segment ℝ a b) := by
  rw [segment_eq_image_lineMap]
  exact isCompact_Icc.image AffineMap.lineMap_continuous

@[simp] theorem KWAdaptivePatchedData.connectorFirstClosedEdge_eq
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) (i : Fin n) :
    kwRawClosedEdge patch.vertex (kwStairEvenIndex i (Fin.last M)) =
      segment ℝ (patch.incomingPort i) (patch.connectorCorner (i + 1)) := by
  unfold kwRawClosedEdge
  rw [kwStairEvenIndex_add_one, patch.vertex_even, patch.vertex_odd,
    patch.pathBase_last, patch.pathCorner_last]

@[simp] theorem KWAdaptivePatchedData.connectorSecondClosedEdge_eq
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) (i : Fin n) :
    kwRawClosedEdge patch.vertex (kwStairOddIndex i (Fin.last M)) =
      segment ℝ (patch.connectorCorner (i + 1))
        (patch.outgoingPort (i + 1)) := by
  unfold kwRawClosedEdge
  rw [kwStairOddIndex_last_add_one, patch.vertex_odd, patch.vertex_even,
    patch.pathCorner_last]
  have hzero : (0 : Fin (M + 1)) = (0 : Fin M).castSucc := by
    ext
    rfl
  rw [hzero, patch.pathBase_castSucc]
  unfold KWAdaptivePatchedData.outgoingPort
  congr 2

theorem KWAdaptivePatchedData.firstConnector_point_re_of_vertical
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    {i : Fin n} (hv : patch.connectorUsesVerticalFirst (i + 1))
    {z : ℂ}
    (hz : z ∈ kwRawClosedEdge patch.vertex
      (kwStairEvenIndex i (Fin.last M))) :
    z.re = (patch.incomingPort i).re := by
  rw [patch.connectorFirstClosedEdge_eq] at hz
  apply mem_segment_re_eq _ hz
  rw [KWAdaptivePatchedData.connectorCorner, patch.incomingPort_eq,
    patch.connector_corner_eq_vh hv]
  have hi : i + 1 - 1 = i := by abel
  simp only [hi, Complex.add_re, kwVHConnectorCorner_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem KWAdaptivePatchedData.firstConnector_point_im_of_horizontal
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    {i : Fin n} (hv : ¬patch.connectorUsesVerticalFirst (i + 1))
    {z : ℂ}
    (hz : z ∈ kwRawClosedEdge patch.vertex
      (kwStairEvenIndex i (Fin.last M))) :
    z.im = (patch.incomingPort i).im := by
  rw [patch.connectorFirstClosedEdge_eq] at hz
  apply mem_segment_im_eq _ hz
  rw [KWAdaptivePatchedData.connectorCorner, patch.incomingPort_eq,
    patch.connector_corner_eq_hv hv]
  have hi : i + 1 - 1 = i := by abel
  simp only [hi, Complex.add_im, kwHVConnectorCorner_im,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]

theorem KWAdaptivePatchedData.secondConnector_point_im_of_vertical
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    {i : Fin n} (hv : patch.connectorUsesVerticalFirst (i + 1))
    {z : ℂ}
    (hz : z ∈ kwRawClosedEdge patch.vertex
      (kwStairOddIndex i (Fin.last M))) :
    z.im = (patch.outgoingPort (i + 1)).im := by
  rw [patch.connectorSecondClosedEdge_eq] at hz
  have hcorner : (patch.connectorCorner (i + 1)).im =
      (patch.outgoingPort (i + 1)).im := by
    rw [KWAdaptivePatchedData.connectorCorner, patch.outgoingPort_eq,
      patch.connector_corner_eq_vh hv]
    have hi : i + 1 - 1 = i := by abel
    simp only [hi, Complex.add_im, kwVHConnectorCorner_im,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  exact (mem_segment_im_eq hcorner.symm hz).trans hcorner

theorem KWAdaptivePatchedData.secondConnector_point_re_of_horizontal
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    {i : Fin n} (hv : ¬patch.connectorUsesVerticalFirst (i + 1))
    {z : ℂ}
    (hz : z ∈ kwRawClosedEdge patch.vertex
      (kwStairOddIndex i (Fin.last M))) :
    z.re = (patch.outgoingPort (i + 1)).re := by
  rw [patch.connectorSecondClosedEdge_eq] at hz
  have hcorner : (patch.connectorCorner (i + 1)).re =
      (patch.outgoingPort (i + 1)).re := by
    rw [KWAdaptivePatchedData.connectorCorner, patch.outgoingPort_eq,
      patch.connector_corner_eq_hv hv]
    have hi : i + 1 - 1 = i := by abel
    simp only [hi, Complex.add_re, kwHVConnectorCorner_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact (mem_segment_re_eq hcorner.symm hz).trans hcorner

private theorem KWAdaptivePatchedData.incomingPort_re_parameter
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) (i : Fin n) :
    (patch.incomingPort i).re = (polygon.vertex i).re +
      patch.data.parameter i (Fin.last (M + 1)).castSucc *
        (polygon.edgeVector i).re := by
  unfold KWAdaptivePatchedData.incomingPort
  exact patch.data.base_re i (Fin.last (M + 1)).castSucc

private theorem KWAdaptivePatchedData.incomingPort_im_parameter
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) (i : Fin n) :
    (patch.incomingPort i).im = (polygon.vertex i).im +
      patch.data.parameter i (Fin.last (M + 1)).castSucc *
        (polygon.edgeVector i).im := by
  unfold KWAdaptivePatchedData.incomingPort
  exact patch.data.base_im i (Fin.last (M + 1)).castSucc

private theorem KWAdaptivePatchedData.outgoingPort_re_parameter
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) (i : Fin n) :
    (patch.outgoingPort i).re = (polygon.vertex i).re +
      patch.data.parameter i (0 : Fin (M + 2)).succ *
        (polygon.edgeVector i).re := by
  unfold KWAdaptivePatchedData.outgoingPort
  exact patch.data.base_re i (0 : Fin (M + 2)).succ

private theorem KWAdaptivePatchedData.outgoingPort_im_parameter
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) (i : Fin n) :
    (patch.outgoingPort i).im = (polygon.vertex i).im +
      patch.data.parameter i (0 : Fin (M + 2)).succ *
        (polygon.edgeVector i).im := by
  unfold KWAdaptivePatchedData.outgoingPort
  exact patch.data.base_im i (0 : Fin (M + 2)).succ



theorem KWAdaptivePatchedData.firstConnector_disjoint_incomingMiddle
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcoords : ∀ j : Fin n,
      (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0)
    (i : Fin n) (q : Fin M) (even : Bool)
    (hnotLast : q ≠ patch.lastMiddleIndex ∨ even = true) :
    Disjoint
      (kwRawClosedEdge patch.vertex (kwStairEvenIndex i (Fin.last M)))
      (patch.middleClosedEdge i q even) := by
  rw [Set.disjoint_left]
  intro z hzConnector hzMiddle
  have hlastIndex : patch.lastMiddleIndex.succ.castSucc.castSucc <
      (Fin.last (M + 1)).castSucc := by
    apply Fin.mk_lt_mk.mpr
    simp [KWAdaptivePatchedData.lastMiddleIndex]
    have := patch.hM
    omega
  by_cases hv : patch.connectorUsesVerticalFirst (i + 1)
  · have hzPort := patch.firstConnector_point_re_of_vertical hv hzConnector
    by_cases hq : q = patch.lastMiddleIndex
    · subst q
      have heven : even = true := by
        rcases hnotLast with h | h
        · exact (h rfl).elim
        · exact h
      subst even
      have hs : patch.sliceUsesVerticalFirst i patch.lastMiddleIndex :=
        (patch.sliceUsesVerticalFirst_last_iff i).mpr hv
      have hzBase : z.re =
          (patch.pathBase i patch.lastMiddleIndex.castSucc).re := by
        change z ∈ kwRawClosedEdge patch.vertex
          (kwStairEvenIndex i patch.lastMiddleIndex.castSucc) at hzMiddle
        rw [patch.rawClosedEdge_even_castSucc] at hzMiddle
        apply mem_segment_re_eq _ hzMiddle
        rw [patch.middleCorner_re, patch.pathBase_castSucc_re, if_pos hs]
      have heq := hzBase.symm.trans hzPort
      rw [patch.pathBase_castSucc_re,
        patch.incomingPort_re_parameter] at heq
      have hparam := parameter_eq_of_scaled_coordinate
        (hcoords i).1 heq
      exact (patch.data.parameter_strictMono i hlastIndex).ne hparam
    · obtain ⟨⟨u, hu, hzu⟩, _⟩ :=
        patch.middleClosedEdge_point_parameters i q even hzMiddle
      have hupperIndex : q.succ.castSucc.succ <
          (Fin.last (M + 1)).castSucc := by
        apply Fin.mk_lt_mk.mpr
        simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last]
        have hqLt := q.isLt
        have hlastVal := patch.lastMiddleIndex_val
        by_contra h
        apply hq
        apply Fin.ext
        omega
      have hupper := patch.data.parameter_strictMono i hupperIndex
      have heq : (polygon.vertex i).re + u * (polygon.edgeVector i).re =
          (polygon.vertex i).re +
            patch.data.parameter i (Fin.last (M + 1)).castSucc *
              (polygon.edgeVector i).re := by
        rw [← patch.incomingPort_re_parameter]
        exact hzu.symm.trans hzPort
      have hparam := parameter_eq_of_scaled_coordinate (hcoords i).1 heq
      linarith [hu.2]
  · have hzPort := patch.firstConnector_point_im_of_horizontal hv hzConnector
    by_cases hq : q = patch.lastMiddleIndex
    · subst q
      have heven : even = true := by
        rcases hnotLast with h | h
        · exact (h rfl).elim
        · exact h
      subst even
      have hs : ¬patch.sliceUsesVerticalFirst i patch.lastMiddleIndex :=
        fun h ↦ hv ((patch.sliceUsesVerticalFirst_last_iff i).mp h)
      have hzBase : z.im =
          (patch.pathBase i patch.lastMiddleIndex.castSucc).im := by
        change z ∈ kwRawClosedEdge patch.vertex
          (kwStairEvenIndex i patch.lastMiddleIndex.castSucc) at hzMiddle
        rw [patch.rawClosedEdge_even_castSucc] at hzMiddle
        apply mem_segment_im_eq _ hzMiddle
        rw [patch.middleCorner_im, patch.pathBase_castSucc_im, if_neg hs]
      have heq := hzBase.symm.trans hzPort
      rw [patch.pathBase_castSucc_im,
        patch.incomingPort_im_parameter] at heq
      have hparam := parameter_eq_of_scaled_coordinate
        (hcoords i).2 heq
      exact (patch.data.parameter_strictMono i hlastIndex).ne hparam
    · obtain ⟨_, ⟨u, hu, hzu⟩⟩ :=
        patch.middleClosedEdge_point_parameters i q even hzMiddle
      have hupperIndex : q.succ.castSucc.succ <
          (Fin.last (M + 1)).castSucc := by
        apply Fin.mk_lt_mk.mpr
        simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last]
        have hqLt := q.isLt
        have hlastVal := patch.lastMiddleIndex_val
        by_contra h
        apply hq
        apply Fin.ext
        omega
      have hupper := patch.data.parameter_strictMono i hupperIndex
      have heq : (polygon.vertex i).im + u * (polygon.edgeVector i).im =
          (polygon.vertex i).im +
            patch.data.parameter i (Fin.last (M + 1)).castSucc *
              (polygon.edgeVector i).im := by
        rw [← patch.incomingPort_im_parameter]
        exact hzu.symm.trans hzPort
      have hparam := parameter_eq_of_scaled_coordinate (hcoords i).2 heq
      linarith [hu.2]



theorem KWAdaptivePatchedData.secondConnector_disjoint_outgoingMiddle
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcoords : ∀ j : Fin n,
      (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0)
    (i : Fin n) (q : Fin M) (even : Bool)
    (hnotFirst : q ≠ 0 ∨ even = false) :
    Disjoint
      (kwRawClosedEdge patch.vertex (kwStairOddIndex i (Fin.last M)))
      (patch.middleClosedEdge (i + 1) q even) := by
  rw [Set.disjoint_left]
  intro z hzConnector hzMiddle
  have hfirstIndex : (0 : Fin (M + 2)).succ <
      (0 : Fin M).succ.castSucc.succ := by
    apply Fin.mk_lt_mk.mpr
    change 1 < 2
    omega
  by_cases hv : patch.connectorUsesVerticalFirst (i + 1)
  · have hzPort := patch.secondConnector_point_im_of_vertical hv hzConnector
    by_cases hq : q = 0
    · subst q
      have hodd : even = false := by
        rcases hnotFirst with h | h
        · exact (h rfl).elim
        · exact h
      subst even
      have hs : patch.sliceUsesVerticalFirst (i + 1) 0 :=
        (patch.sliceUsesVerticalFirst_zero_iff (i + 1)).mpr hv
      have hzBase : z.im = (patch.pathBase (i + 1) (0 : Fin M).succ).im := by
        change z ∈ kwRawClosedEdge patch.vertex
          (kwStairOddIndex (i + 1) (0 : Fin M).castSucc) at hzMiddle
        rw [patch.rawClosedEdge_odd_castSucc] at hzMiddle
        have hcorner : (patch.middleCorner (i + 1) 0).im =
            (patch.pathBase (i + 1) (0 : Fin M).succ).im := by
          rw [patch.middleCorner_im, patch.pathBase_succ_im, if_pos hs]
        exact (mem_segment_im_eq hcorner.symm hzMiddle).trans hcorner
      have heq := hzPort.symm.trans hzBase
      rw [patch.outgoingPort_im_parameter,
        patch.pathBase_succ_im] at heq
      have hparam := parameter_eq_of_scaled_coordinate
        (hcoords (i + 1)).2 heq
      exact (patch.data.parameter_strictMono (i + 1) hfirstIndex).ne hparam
    · obtain ⟨_, ⟨u, hu, hzu⟩⟩ :=
        patch.middleClosedEdge_point_parameters (i + 1) q even hzMiddle
      have hlowerIndex : (0 : Fin (M + 2)).succ <
          q.succ.castSucc.castSucc := by
        apply Fin.mk_lt_mk.mpr
        change 1 < q.val + 1
        have hqval : q.val ≠ 0 := by
          intro h
          apply hq
          ext
          exact h
        omega
      have hlower := patch.data.parameter_strictMono (i + 1) hlowerIndex
      have heq : (polygon.vertex (i + 1)).im +
            patch.data.parameter (i + 1) (0 : Fin (M + 2)).succ *
              (polygon.edgeVector (i + 1)).im =
          (polygon.vertex (i + 1)).im +
            u * (polygon.edgeVector (i + 1)).im := by
        rw [← patch.outgoingPort_im_parameter]
        exact hzPort.symm.trans hzu
      have hparam := parameter_eq_of_scaled_coordinate
        (hcoords (i + 1)).2 heq
      linarith [hu.1]
  · have hzPort := patch.secondConnector_point_re_of_horizontal hv hzConnector
    by_cases hq : q = 0
    · subst q
      have hodd : even = false := by
        rcases hnotFirst with h | h
        · exact (h rfl).elim
        · exact h
      subst even
      have hs : ¬patch.sliceUsesVerticalFirst (i + 1) 0 :=
        fun h ↦ hv ((patch.sliceUsesVerticalFirst_zero_iff (i + 1)).mp h)
      have hzBase : z.re = (patch.pathBase (i + 1) (0 : Fin M).succ).re := by
        change z ∈ kwRawClosedEdge patch.vertex
          (kwStairOddIndex (i + 1) (0 : Fin M).castSucc) at hzMiddle
        rw [patch.rawClosedEdge_odd_castSucc] at hzMiddle
        have hcorner : (patch.middleCorner (i + 1) 0).re =
            (patch.pathBase (i + 1) (0 : Fin M).succ).re := by
          rw [patch.middleCorner_re, patch.pathBase_succ_re, if_neg hs]
        exact (mem_segment_re_eq hcorner.symm hzMiddle).trans hcorner
      have heq := hzPort.symm.trans hzBase
      rw [patch.outgoingPort_re_parameter,
        patch.pathBase_succ_re] at heq
      have hparam := parameter_eq_of_scaled_coordinate
        (hcoords (i + 1)).1 heq
      exact (patch.data.parameter_strictMono (i + 1) hfirstIndex).ne hparam
    · obtain ⟨⟨u, hu, hzu⟩, _⟩ :=
        patch.middleClosedEdge_point_parameters (i + 1) q even hzMiddle
      have hlowerIndex : (0 : Fin (M + 2)).succ <
          q.succ.castSucc.castSucc := by
        apply Fin.mk_lt_mk.mpr
        change 1 < q.val + 1
        have hqval : q.val ≠ 0 := by
          intro h
          apply hq
          ext
          exact h
        omega
      have hlower := patch.data.parameter_strictMono (i + 1) hlowerIndex
      have heq : (polygon.vertex (i + 1)).re +
            patch.data.parameter (i + 1) (0 : Fin (M + 2)).succ *
              (polygon.edgeVector (i + 1)).re =
          (polygon.vertex (i + 1)).re +
            u * (polygon.edgeVector (i + 1)).re := by
        rw [← patch.outgoingPort_re_parameter]
        exact hzPort.symm.trans hzu
      have hparam := parameter_eq_of_scaled_coordinate
        (hcoords (i + 1)).1 heq
      linarith [hu.1]


def KWAdaptivePatchedData.outgoingRetainedCarrier
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) (i : Fin n) : Set ℂ :=
  segment ℝ (patch.outgoingPort i) (polygon.vertex (i + 1))


def KWAdaptivePatchedData.incomingRetainedCarrier
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) (i : Fin n) : Set ℂ :=
  segment ℝ (polygon.vertex i) (patch.incomingPort i)

theorem KWAdaptivePatchedData.outgoingRetainedCarrier_subset_portTail
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) (i : Fin n) :
    patch.outgoingRetainedCarrier i ⊆
      ({patch.outgoingPort i} ∪
        kwTranslatedOpenRayTail (polygon.vertex i)
          (patch.beta * polygon.edgeVector i)) := by
  intro z hz
  rw [KWAdaptivePatchedData.outgoingRetainedCarrier,
    segment_eq_image_lineMap] at hz
  obtain ⟨s, hs, rfl⟩ := hz
  by_cases hs0 : s = 0
  · subst s
    simp
  · right
    let t : ℝ := (1 - s) + s / patch.beta
    have hbetaOne : patch.beta < 1 := by
      have := patch.hsum i
      have := patch.halpha i
      linarith
    have ht : 1 < t := by
      dsimp only [t]
      have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
      have hratio : 1 < 1 / patch.beta := by
        rw [one_div]
        exact (one_lt_inv₀ patch.hbeta).mpr hbetaOne
      have hprod : 0 < s * (1 / patch.beta - 1) :=
        mul_pos hspos (sub_pos.mpr hratio)
      calc
        1 < 1 + s * (1 / patch.beta - 1) := by linarith
        _ = t := by dsimp only [t]; ring
    refine ⟨t, ht, ?_⟩
    rw [patch.outgoingPort_eq, KWFiniteSimplePolygon.edgeVector,
      AffineMap.lineMap_apply_module]
    dsimp only [t]
    simp only [Complex.real_smul]
    push_cast
    field_simp [patch.hbeta.ne']
    ring

theorem KWAdaptivePatchedData.incomingRetainedCarrier_subset_portTail
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) (i : Fin n) :
    patch.incomingRetainedCarrier i ⊆
      ({patch.incomingPort i} ∪
        kwTranslatedOpenRayTail (polygon.vertex (i + 1))
          (patch.alpha (i + 1) * (-polygon.edgeVector i))) := by
  intro z hz
  rw [KWAdaptivePatchedData.incomingRetainedCarrier,
    segment_eq_image_lineMap] at hz
  obtain ⟨s, hs, rfl⟩ := hz
  by_cases hs1 : s = 1
  · subst s
    simp
  · right
    let t : ℝ := (1 - s) / patch.alpha (i + 1) + s
    have halphaOne : patch.alpha (i + 1) < 1 := by
      have := patch.hsum (i + 1)
      have := patch.hbeta
      linarith
    have ht : 1 < t := by
      dsimp only [t]
      have hslt : s < 1 := lt_of_le_of_ne hs.2 hs1
      have hratio : 1 < 1 / patch.alpha (i + 1) := by
        rw [one_div]
        exact (one_lt_inv₀ (patch.halpha (i + 1))).mpr halphaOne
      have hprod : 0 < (1 - s) * (1 / patch.alpha (i + 1) - 1) :=
        mul_pos (sub_pos.mpr hslt) (sub_pos.mpr hratio)
      calc
        1 < 1 + (1 - s) * (1 / patch.alpha (i + 1) - 1) := by linarith
        _ = t := by dsimp only [t]; ring
    refine ⟨t, ht, ?_⟩
    rw [patch.incomingPort_eq, KWFiniteSimplePolygon.edgeVector,
      AffineMap.lineMap_apply_module]
    dsimp only [t]
    simp only [Complex.real_smul]
    push_cast
    field_simp [(patch.halpha (i + 1)).ne']
    ring

theorem KWAdaptivePatchedData.firstConnector_disjoint_outgoingCarrier
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j)
      (polygon.edgeVector (j + 1)) ≠ 0)
    (hcoords : ∀ j : Fin n,
      (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0)
    (i : Fin n) :
    Disjoint
      (kwRawClosedEdge patch.vertex (kwStairEvenIndex i (Fin.last M)))
      (patch.outgoingRetainedCarrier (i + 1)) := by
  have hsub := patch.outgoingRetainedCarrier_subset_portTail (i + 1)
  rw [patch.outgoingPort_eq] at hsub
  have h := (patch.idealConnectorFirstClosedEdge_disjoint_outgoingPortTail
    hcross hcoords i).mono_right hsub
  rw [patch.idealConnectorFirstClosedEdge_eq,
    ← patch.connectorFirstClosedEdge_eq] at h
  exact h

theorem KWAdaptivePatchedData.secondConnector_disjoint_incomingCarrier
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j)
      (polygon.edgeVector (j + 1)) ≠ 0)
    (hcoords : ∀ j : Fin n,
      (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0)
    (i : Fin n) :
    Disjoint
      (kwRawClosedEdge patch.vertex (kwStairOddIndex i (Fin.last M)))
      (patch.incomingRetainedCarrier i) := by
  have hsub := patch.incomingRetainedCarrier_subset_portTail i
  rw [patch.incomingPort_eq] at hsub
  have h := (patch.idealConnectorSecondClosedEdge_disjoint_incomingPortTail
    hcross hcoords i).mono_right hsub
  rw [patch.idealConnectorSecondClosedEdge_eq,
    ← patch.connectorSecondClosedEdge_eq] at h
  exact h

theorem KWAdaptivePatchedData.exists_remoteIncident_dist_separation
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j)
      (polygon.edgeVector (j + 1)) ≠ 0)
    (hcoords : ∀ j : Fin n,
      (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0)
    (i : Fin n) (first : Bool) :
    ∃ r : ℝ≥0, 0 < r ∧
      ∀ x ∈ (if first then
          kwRawClosedEdge patch.vertex (kwStairEvenIndex i (Fin.last M))
        else kwRawClosedEdge patch.vertex (kwStairOddIndex i (Fin.last M))),
      ∀ y ∈ (if first then patch.outgoingRetainedCarrier (i + 1)
        else patch.incomingRetainedCarrier i),
        (r : ℝ) < dist x y := by
  cases first with
  | false =>
      have hdis := patch.secondConnector_disjoint_incomingCarrier
        hcross hcoords i
      rw [patch.connectorSecondClosedEdge_eq,
        KWAdaptivePatchedData.incomingRetainedCarrier] at hdis
      obtain ⟨r, hr, hsep⟩ := Metric.exists_pos_forall_lt_edist
        (isCompact_complexSegment _ _)
        (isCompact_complexSegment _ _).isClosed hdis
      refine ⟨r, hr, ?_⟩
      intro x hx y hy
      have h := hsep x (by
        simpa [patch.connectorSecondClosedEdge_eq] using hx) y (by
          simpa [KWAdaptivePatchedData.incomingRetainedCarrier] using hy)
      rw [edist_dist] at h
      exact ENNReal.coe_lt_ofReal.mp h
  | true =>
      have hdis := patch.firstConnector_disjoint_outgoingCarrier
        hcross hcoords i
      rw [patch.connectorFirstClosedEdge_eq,
        KWAdaptivePatchedData.outgoingRetainedCarrier] at hdis
      obtain ⟨r, hr, hsep⟩ := Metric.exists_pos_forall_lt_edist
        (isCompact_complexSegment _ _)
        (isCompact_complexSegment _ _).isClosed hdis
      refine ⟨r, hr, ?_⟩
      intro x hx y hy
      have h := hsep x (by
        simpa [patch.connectorFirstClosedEdge_eq] using hx) y (by
          simpa [KWAdaptivePatchedData.outgoingRetainedCarrier] using hy)
      rw [edist_dist] at h
      exact ENNReal.coe_lt_ofReal.mp h

end StatMech.FrontierA
