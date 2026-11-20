/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardStaircaseLocalGeometry








namespace StatMech.FrontierA

theorem kwEndpointParameter_one
    (M : ℕ) (beta alpha : ℝ) (hM : 0 < M) :
    kwEndpointParameter M beta alpha (1 : Fin (M + 3)) = beta := by
  unfold kwEndpointParameter
  simp only [Fin.val_one, if_neg (by omega : (1 : ℕ) ≠ 0),
    if_neg (by omega : (1 : ℕ) ≠ M + 2)]
  norm_num

theorem kwEndpointParameter_penultimate
    (M : ℕ) (beta alpha : ℝ) (hM : 0 < M) :
    kwEndpointParameter M beta alpha (Fin.last (M + 1)).castSucc =
      1 - alpha := by
  unfold kwEndpointParameter
  simp only [Fin.val_castSucc, Fin.val_last,
    if_neg (by omega : M + 1 ≠ 0),
    if_neg (by omega : M + 1 ≠ M + 2)]
  have hsub : M + 1 - 1 = M := by omega
  rw [hsub]
  have hMreal : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  rw [div_self hMreal, one_mul]
  ring

theorem kwEndpointParameter_step_le_max
    (M : ℕ) (beta alpha : ℝ)
    (hM : 0 < M) (hbeta : 0 ≤ beta) (halpha : 0 ≤ alpha)
    (hsum : alpha + beta < 1) (k : Fin (M + 2)) :
    kwEndpointParameter M beta alpha k.succ -
        kwEndpointParameter M beta alpha k.castSucc ≤
      max beta (max alpha (M : ℝ)⁻¹) := by
  have hklt := k.isLt
  have hMreal : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  by_cases hk0 : k.val = 0
  · have hsucc0 : k.val + 1 ≠ 0 := by omega
    have hsuccLast : k.val + 1 ≠ M + 2 := by omega
    simp only [kwEndpointParameter, Fin.val_castSucc, Fin.val_succ,
      if_pos hk0, if_neg hsucc0, if_neg hsuccLast]
    norm_num [hk0]
  · by_cases hklast : k.val + 1 = M + 2
    · have hkLast : k.val ≠ M + 2 := by omega
      have hsub : k.val - 1 = M := by omega
      simp only [kwEndpointParameter, Fin.val_castSucc, Fin.val_succ,
        if_neg hk0, if_neg hkLast, if_neg (by omega : k.val + 1 ≠ 0),
        if_pos hklast]
      rw [hsub, div_self hMreal, one_mul]
      have : alpha ≤ max alpha (M : ℝ)⁻¹ := le_max_left _ _
      linarith [this.trans (le_max_right beta _)]
    · have hkNotLast : k.val ≠ M + 2 := by omega
      have hsucc0 : k.val + 1 ≠ 0 := by omega
      simp only [kwEndpointParameter, Fin.val_castSucc, Fin.val_succ,
        if_neg hk0, if_neg hkNotLast, if_neg hsucc0, if_neg hklast]
      have hsubSucc : k.val + 1 - 1 = k.val := by omega
      rw [hsubSucc]
      have hstep : (((k.val : ℝ) / M) -
          (((k.val - 1 : ℕ) : ℝ) / M)) = (M : ℝ)⁻¹ := by
        have hkpos : 1 ≤ k.val := by omega
        have hcast : ((k.val - 1 : ℕ) : ℝ) = (k.val : ℝ) - 1 := by
          rw [Nat.cast_sub hkpos]
          norm_num
        rw [hcast]
        field_simp
        ring
      have hcentral : 1 - alpha - beta ≤ 1 := by linarith
      have hinv : 0 ≤ (M : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
      calc
        beta + (k.val : ℝ) / M * (1 - alpha - beta) -
            (beta + ((k.val - 1 : ℕ) : ℝ) / M *
              (1 - alpha - beta)) =
            ((k.val : ℝ) / M - ((k.val - 1 : ℕ) : ℝ) / M) *
              (1 - alpha - beta) := by ring
        _ = (M : ℝ)⁻¹ * (1 - alpha - beta) := by rw [hstep]
        _ ≤ (M : ℝ)⁻¹ := by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hcentral hinv
        _ ≤ max beta (max alpha (M : ℝ)⁻¹) :=
          (le_max_right alpha _).trans (le_max_right beta _)

theorem kwEndpointParameter_middle_step_le_inv
    (M : ℕ) (beta alpha : ℝ) (hM : 0 < M)
    (hbeta : 0 ≤ beta) (halpha : 0 ≤ alpha)
    (k : Fin (M + 2)) (hk0 : k ≠ 0) (hklast : k ≠ Fin.last (M + 1)) :
    kwEndpointParameter M beta alpha k.succ -
        kwEndpointParameter M beta alpha k.castSucc ≤ (M : ℝ)⁻¹ := by
  have hklt := k.isLt
  have hk0val : k.val ≠ 0 := by
    intro h
    exact hk0 (Fin.ext h)
  have hklastval : k.val + 1 ≠ M + 2 := by
    intro h
    apply hklast
    apply Fin.ext
    simpa only [Fin.val_last] using congrArg (fun q ↦ q - 1) h
  have hkNotLast : k.val ≠ M + 2 := by omega
  have hsucc0 : k.val + 1 ≠ 0 := by omega
  simp only [kwEndpointParameter, Fin.val_castSucc, Fin.val_succ,
    if_neg hk0val, if_neg hkNotLast, if_neg hsucc0, if_neg hklastval]
  have hsubSucc : k.val + 1 - 1 = k.val := by omega
  rw [hsubSucc]
  have hMreal : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hstep : (((k.val : ℝ) / M) -
      (((k.val - 1 : ℕ) : ℝ) / M)) = (M : ℝ)⁻¹ := by
    have hkpos : 1 ≤ k.val := by omega
    have hcast : ((k.val - 1 : ℕ) : ℝ) = (k.val : ℝ) - 1 := by
      rw [Nat.cast_sub hkpos]
      norm_num
    rw [hcast]
    field_simp
    ring
  have hcentral : 1 - alpha - beta ≤ 1 := by linarith
  have hinv : 0 ≤ (M : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
  calc
    beta + (k.val : ℝ) / M * (1 - alpha - beta) -
        (beta + ((k.val - 1 : ℕ) : ℝ) / M *
          (1 - alpha - beta)) =
        ((k.val : ℝ) / M - ((k.val - 1 : ℕ) : ℝ) / M) *
          (1 - alpha - beta) := by ring
    _ = (M : ℝ)⁻¹ * (1 - alpha - beta) := by rw [hstep]
    _ ≤ (M : ℝ)⁻¹ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hcentral hinv

theorem KWStairParameterData.corner_zero_eq_outgoingPatchCorner
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (i : Fin n) (beta : ℝ)
    (hbeta : data.parameter i (0 : Fin S).succ = beta) :
    data.corner i 0 =
      kwOutgoingPatchCorner (polygon.vertex i) (polygon.edgeVector i) beta := by
  have hzero : (0 : Fin S).castSucc = (0 : Fin (S + 1)) := by
    apply Fin.ext
    rfl
  unfold KWStairParameterData.corner kwOutgoingPatchCorner
  rw [hzero, data.base_zero, hbeta, data.parameter_zero]
  simp

theorem KWStairParameterData.base_one_eq_outgoingPatchEnd
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (i : Fin n) (beta : ℝ)
    (hbeta : data.parameter i (0 : Fin S).succ = beta) :
    data.base i (0 : Fin S).succ =
      kwOutgoingPatchEnd (polygon.vertex i) (polygon.edgeVector i) beta := by
  unfold KWStairParameterData.base kwOutgoingPatchEnd
  rw [AffineMap.lineMap_apply, hbeta]
  simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul]
  unfold KWFiniteSimplePolygon.edgeVector
  push_cast
  ring

theorem KWStairParameterData.base_penultimate_eq_incomingPatchBase
    {n M : ℕ} [NeZero n]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := M + 1) polygon)
    (i : Fin n) (alpha : ℝ)
    (halpha : data.parameter i (Fin.last M).castSucc = 1 - alpha) :
    data.base i (Fin.last M).castSucc =
      kwIncomingPatchBase (polygon.vertex (i + 1))
        (-polygon.edgeVector i) alpha := by
  unfold KWStairParameterData.base kwIncomingPatchBase
  rw [AffineMap.lineMap_apply, halpha]
  simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul]
  unfold KWFiniteSimplePolygon.edgeVector
  push_cast
  ring

theorem KWStairParameterData.corner_last_eq_incomingPatchCorner
    {n M : ℕ} [NeZero n]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := M + 1) polygon)
    (i : Fin n) (alpha : ℝ)
    (halpha : data.parameter i (Fin.last M).castSucc = 1 - alpha) :
    data.corner i (Fin.last M) =
      kwIncomingPatchCorner (polygon.vertex (i + 1))
        (-polygon.edgeVector i) alpha := by
  have hlastIndex : (Fin.last M).succ = Fin.last (M + 1) := by
    apply Fin.ext
    rfl
  have hlast : data.parameter i (Fin.last M).succ = 1 := by
    rw [hlastIndex, data.parameter_last]
  unfold KWStairParameterData.corner kwIncomingPatchCorner
  rw [data.base_penultimate_eq_incomingPatchBase i alpha halpha,
    hlast, halpha]
  unfold kwIncomingPatchBase
  have hvertical : kwVerticalPart (-polygon.edgeVector i) =
      -kwVerticalPart (polygon.edgeVector i) := by
    unfold kwVerticalPart
    simp
  rw [hvertical]
  push_cast
  have hdecomp := kwHorizontalPart_add_verticalPart (polygon.edgeVector i)
  have hdiff : -polygon.edgeVector i +
      kwHorizontalPart (polygon.edgeVector i) =
      -kwVerticalPart (polygon.edgeVector i) := by
    nth_rewrite 1 [← hdecomp]
    ring
  calc
    polygon.vertex (i + 1) + alpha * (-polygon.edgeVector i) +
        (1 - (1 - alpha)) * kwHorizontalPart (polygon.edgeVector i) =
      polygon.vertex (i + 1) + alpha *
        (-polygon.edgeVector i + kwHorizontalPart (polygon.edgeVector i)) := by ring
    _ = polygon.vertex (i + 1) + alpha *
        (-kwVerticalPart (polygon.edgeVector i)) := by rw [hdiff]

theorem KWStairParameterData.incident_endpoint_legs_disjoint
    {n M : ℕ} [NeZero n]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := M + 1) polygon)
    (i : Fin n) (alpha beta : ℝ)
    (halphaParameter :
      data.parameter i (Fin.last M).castSucc = 1 - alpha)
    (hbetaParameter :
      data.parameter (i + 1) (0 : Fin (M + 1)).succ = beta)
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hcoords : ∀ j : Fin n,
      (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0)
    (hextent : |alpha * (-polygon.edgeVector i).re| <
      |beta * (polygon.edgeVector (i + 1)).re|) :
    Disjoint
      ({z : ℂ | Sbtw ℝ (data.base i (Fin.last M).castSucc) z
          (data.corner i (Fin.last M))} ∪
        {z : ℂ | Sbtw ℝ (data.corner i (Fin.last M)) z
          (polygon.vertex (i + 1))})
      ({z : ℂ | Sbtw ℝ (polygon.vertex (i + 1)) z
          (data.corner (i + 1) 0)} ∪
        {z : ℂ | Sbtw ℝ (data.corner (i + 1) 0) z
          (data.base (i + 1) (0 : Fin (M + 1)).succ)}) := by
  have hinBase := data.base_penultimate_eq_incomingPatchBase
    i alpha halphaParameter
  have hinCorner := data.corner_last_eq_incomingPatchCorner
    i alpha halphaParameter
  have houtCorner := data.corner_zero_eq_outgoingPatchCorner
    (i + 1) beta hbetaParameter
  have houtEnd := data.base_one_eq_outgoingPatchEnd
    (i + 1) beta hbetaParameter
  rw [hinBase, hinCorner, houtCorner, houtEnd]
  apply kw_incidentPatch_pairwise_disjoint
  · exact halpha
  · exact hbeta
  · simpa only [Complex.neg_re] using neg_ne_zero.mpr (hcoords i).1
  · simpa only [Complex.neg_im] using neg_ne_zero.mpr (hcoords i).2
  · exact (hcoords (i + 1)).1
  · exact (hcoords (i + 1)).2
  · exact hextent

theorem kwEndpointParameterData_parameter_one
    {n M : ℕ} [NeZero n]
    (polygon : KWFiniteSimplePolygon n)
    (beta : ℝ) (alpha : Fin n → ℝ)
    (hM : 0 < M) (hbeta : 0 < beta)
    (halpha : ∀ i, 0 < alpha i)
    (hsum : ∀ i, alpha i + beta < 1)
    (i : Fin n) :
    (kwEndpointParameterData polygon M beta alpha hM hbeta halpha hsum).parameter
        i (0 : Fin (M + 2)).succ = beta := by
  dsimp only [kwEndpointParameterData]
  convert kwEndpointParameter_one M beta (alpha (i + 1)) hM using 1

theorem kwEndpointParameterData_parameter_penultimate
    {n M : ℕ} [NeZero n]
    (polygon : KWFiniteSimplePolygon n)
    (beta : ℝ) (alpha : Fin n → ℝ)
    (hM : 0 < M) (hbeta : 0 < beta)
    (halpha : ∀ i, 0 < alpha i)
    (hsum : ∀ i, alpha i + beta < 1)
    (i : Fin n) :
    (kwEndpointParameterData polygon M beta alpha hM hbeta halpha hsum).parameter
        i (Fin.last (M + 1)).castSucc = 1 - alpha (i + 1) := by
  dsimp only [kwEndpointParameterData]
  exact kwEndpointParameter_penultimate M beta (alpha (i + 1)) hM



theorem kwEndpointParameterData_incident_legs_disjoint
    {n M : ℕ} [NeZero n]
    (polygon : KWFiniteSimplePolygon n)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    (beta : ℝ) (alpha : Fin n → ℝ)
    (hM : 0 < M) (hbeta : 0 < beta)
    (halpha : ∀ i, 0 < alpha i)
    (hsum : ∀ i, alpha i + beta < 1)
    (hextent : ∀ i : Fin n,
      |alpha i * (-polygon.edgeVector (i - 1)).re| <
        |beta * (polygon.edgeVector i).re|)
    (i : Fin n) :
    let data := kwEndpointParameterData polygon M beta alpha
      hM hbeta halpha hsum
    Disjoint
      ({z : ℂ | Sbtw ℝ (data.base i (Fin.last (M + 1)).castSucc) z
          (data.corner i (Fin.last (M + 1)))} ∪
        {z : ℂ | Sbtw ℝ (data.corner i (Fin.last (M + 1))) z
          (polygon.vertex (i + 1))})
      ({z : ℂ | Sbtw ℝ (polygon.vertex (i + 1)) z
          (data.corner (i + 1) 0)} ∪
        {z : ℂ | Sbtw ℝ (data.corner (i + 1) 0) z
          (data.base (i + 1) (0 : Fin (M + 2)).succ)}) := by
  dsimp only
  apply KWStairParameterData.incident_endpoint_legs_disjoint
  · exact kwEndpointParameterData_parameter_penultimate
      polygon beta alpha hM hbeta halpha hsum i
  · exact kwEndpointParameterData_parameter_one
      polygon beta alpha hM hbeta halpha hsum (i + 1)
  · exact halpha (i + 1)
  · exact hbeta
  · exact hcoords
  · have hindex : (i + 1) - 1 = i := by
      exact add_sub_cancel_right i 1
    simpa only [hindex] using hextent (i + 1)

theorem kwOutgoingPatchCorner_mem_ball
    (v b : ℂ) (beta R : ℝ) (hbeta : 0 ≤ beta)
    (hsize : beta * ‖b‖ < R) :
    kwOutgoingPatchCorner v b beta ∈ Metric.ball v R := by
  rw [Metric.mem_ball', dist_eq_norm]
  unfold kwOutgoingPatchCorner
  rw [show v - (v + beta * kwHorizontalPart b) =
      -(beta * kwHorizontalPart b) by ring,
    norm_neg, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hbeta]
  exact (mul_le_mul_of_nonneg_left (norm_kwHorizontalPart_le b) hbeta).trans_lt
    hsize

theorem kwOutgoingPatchEnd_mem_ball
    (v b : ℂ) (beta R : ℝ) (hbeta : 0 ≤ beta)
    (hsize : beta * ‖b‖ < R) :
    kwOutgoingPatchEnd v b beta ∈ Metric.ball v R := by
  rw [Metric.mem_ball', dist_eq_norm]
  unfold kwOutgoingPatchEnd
  rw [show v - (v + beta * b) = -(beta * b) by ring,
    norm_neg, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hbeta]
  exact hsize

theorem kwIncomingPatchBase_mem_ball
    (v a : ℂ) (alpha R : ℝ) (halpha : 0 ≤ alpha)
    (hsize : alpha * ‖a‖ < R) :
    kwIncomingPatchBase v a alpha ∈ Metric.ball v R := by
  rw [Metric.mem_ball', dist_eq_norm]
  unfold kwIncomingPatchBase
  rw [show v - (v + alpha * a) = -(alpha * a) by ring,
    norm_neg, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg halpha]
  exact hsize

theorem kwIncomingPatchCorner_mem_ball
    (v a : ℂ) (alpha R : ℝ) (halpha : 0 ≤ alpha)
    (hsize : alpha * ‖a‖ < R) :
    kwIncomingPatchCorner v a alpha ∈ Metric.ball v R := by
  rw [Metric.mem_ball', dist_eq_norm]
  unfold kwIncomingPatchCorner
  rw [show v - (v + alpha * kwVerticalPart a) =
      -(alpha * kwVerticalPart a) by ring,
    norm_neg, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg halpha]
  exact (mul_le_mul_of_nonneg_left (norm_kwVerticalPart_le a) halpha).trans_lt
    hsize



theorem KWStairParameterData.incident_endpoint_legs_subset_ball
    {n M : ℕ} [NeZero n]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := M + 1) polygon)
    (i : Fin n) (alpha beta R : ℝ)
    (halphaParameter :
      data.parameter i (Fin.last M).castSucc = 1 - alpha)
    (hbetaParameter :
      data.parameter (i + 1) (0 : Fin (M + 1)).succ = beta)
    (hR : 0 < R) (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta)
    (halphaSize : alpha * ‖polygon.edgeVector i‖ < R)
    (hbetaSize : beta * ‖polygon.edgeVector (i + 1)‖ < R) :
    segment ℝ (data.base i (Fin.last M).castSucc)
        (data.corner i (Fin.last M)) ⊆
        Metric.ball (polygon.vertex (i + 1)) R ∧
      segment ℝ (data.corner i (Fin.last M))
        (polygon.vertex (i + 1)) ⊆
        Metric.ball (polygon.vertex (i + 1)) R ∧
      segment ℝ (polygon.vertex (i + 1))
        (data.corner (i + 1) 0) ⊆
        Metric.ball (polygon.vertex (i + 1)) R ∧
      segment ℝ (data.corner (i + 1) 0)
        (data.base (i + 1) (0 : Fin (M + 1)).succ) ⊆
        Metric.ball (polygon.vertex (i + 1)) R := by
  have hinBase := data.base_penultimate_eq_incomingPatchBase
    i alpha halphaParameter
  have hinCorner := data.corner_last_eq_incomingPatchCorner
    i alpha halphaParameter
  have houtCorner := data.corner_zero_eq_outgoingPatchCorner
    (i + 1) beta hbetaParameter
  have houtEnd := data.base_one_eq_outgoingPatchEnd
    (i + 1) beta hbetaParameter
  have hv : polygon.vertex (i + 1) ∈
      Metric.ball (polygon.vertex (i + 1)) R := Metric.mem_ball_self hR
  have hinBaseMem : data.base i (Fin.last M).castSucc ∈
      Metric.ball (polygon.vertex (i + 1)) R := by
    rw [hinBase]
    apply kwIncomingPatchBase_mem_ball
    · exact halpha
    · simpa only [norm_neg] using halphaSize
  have hinCornerMem : data.corner i (Fin.last M) ∈
      Metric.ball (polygon.vertex (i + 1)) R := by
    rw [hinCorner]
    apply kwIncomingPatchCorner_mem_ball
    · exact halpha
    · simpa only [norm_neg] using halphaSize
  have houtCornerMem : data.corner (i + 1) 0 ∈
      Metric.ball (polygon.vertex (i + 1)) R := by
    rw [houtCorner]
    exact kwOutgoingPatchCorner_mem_ball _ _ _ _ hbeta hbetaSize
  have houtEndMem : data.base (i + 1) (0 : Fin (M + 1)).succ ∈
      Metric.ball (polygon.vertex (i + 1)) R := by
    rw [houtEnd]
    exact kwOutgoingPatchEnd_mem_ball _ _ _ _ hbeta hbetaSize
  have hconvex := convex_ball (polygon.vertex (i + 1)) R
  exact ⟨hconvex.segment_subset hinBaseMem hinCornerMem,
    hconvex.segment_subset hinCornerMem hv,
    hconvex.segment_subset hv houtCornerMem,
    hconvex.segment_subset houtCornerMem houtEndMem⟩

theorem KWStairParameterData.rawClosedEdge_even_eq_segment
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (i : Fin n) (k : Fin S) :
    kwRawClosedEdge data.vertex (kwStairEvenIndex i k) =
      segment ℝ (data.base i k.castSucc) (data.corner i k) := by
  unfold kwRawClosedEdge
  rw [kwStairEvenIndex_add_one, data.vertex_odd, data.vertex_even]

theorem KWStairParameterData.rawClosedEdge_odd_last_eq_segment
    {n M : ℕ} [NeZero n]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := M + 1) polygon)
    (i : Fin n) :
    kwRawClosedEdge data.vertex (kwStairOddIndex i (Fin.last M)) =
      segment ℝ (data.corner i (Fin.last M)) (polygon.vertex (i + 1)) := by
  unfold kwRawClosedEdge
  rw [data.vertex_odd_last_succ, data.vertex_odd]

theorem KWStairParameterData.rawClosedEdge_odd_zero_eq_segment
    {n M : ℕ} [NeZero n]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := M + 2) polygon)
    (i : Fin n) :
    kwRawClosedEdge data.vertex (kwStairOddIndex i (0 : Fin (M + 2))) =
      segment ℝ (data.corner i 0) (data.base i (0 : Fin (M + 2)).succ) := by
  have hzero : (0 : Fin (M + 1)).castSucc = (0 : Fin (M + 2)) := by
    apply Fin.ext
    rfl
  have hone : (0 : Fin (M + 1)).succ.castSucc =
      (0 : Fin (M + 1)).castSucc.succ := by
    apply Fin.ext
    rfl
  unfold kwRawClosedEdge
  rw [← hzero, data.vertex_odd_castSucc_succ, data.vertex_odd, hone]




theorem KWStairParameterData.incident_nonconsecutive_rawEdges_disjoint
    {n M : ℕ} [NeZero n]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := M + 2) polygon)
    (i : Fin n) (alpha beta : ℝ)
    (halphaParameter :
      data.parameter i (Fin.last (M + 1)).castSucc = 1 - alpha)
    (hbetaParameter :
      data.parameter (i + 1) (0 : Fin (M + 2)).succ = beta)
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hcoords : ∀ j : Fin n,
      (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0)
    (hextent : |alpha * (-polygon.edgeVector i).re| <
      |beta * (polygon.edgeVector (i + 1)).re|) :
    Disjoint
        (kwRawClosedEdge data.vertex
          (kwStairEvenIndex i (Fin.last (M + 1))))
        (kwRawClosedEdge data.vertex
          (kwStairEvenIndex (i + 1) 0)) ∧
      Disjoint
        (kwRawClosedEdge data.vertex
          (kwStairEvenIndex i (Fin.last (M + 1))))
        (kwRawClosedEdge data.vertex
          (kwStairOddIndex (i + 1) 0)) ∧
      Disjoint
        (kwRawClosedEdge data.vertex
          (kwStairOddIndex i (Fin.last (M + 1))))
        (kwRawClosedEdge data.vertex
          (kwStairOddIndex (i + 1) 0)) := by
  have hzero : (0 : Fin (M + 2)).castSucc = (0 : Fin (M + 3)) := by
    apply Fin.ext
    rfl
  have houtBase : data.base (i + 1) (0 : Fin (M + 2)).castSucc =
      polygon.vertex (i + 1) := by
    rw [hzero, data.base_zero]
  rw [data.rawClosedEdge_even_eq_segment,
    data.rawClosedEdge_even_eq_segment,
    data.rawClosedEdge_odd_last_eq_segment,
    data.rawClosedEdge_odd_zero_eq_segment,
    houtBase,
    data.base_penultimate_eq_incomingPatchBase i alpha halphaParameter,
    data.corner_last_eq_incomingPatchCorner i alpha halphaParameter,
    data.corner_zero_eq_outgoingPatchCorner (i + 1) beta hbetaParameter,
    data.base_one_eq_outgoingPatchEnd (i + 1) beta hbetaParameter]
  refine ⟨?_, ?_, ?_⟩
  · apply kw_incidentPatch_incomingHorizontal_closed_disjoint_outgoingHorizontal
    · exact halpha
    · simpa only [Complex.neg_re] using neg_ne_zero.mpr (hcoords i).1
    · simpa only [Complex.neg_im] using neg_ne_zero.mpr (hcoords i).2
  · exact kw_incidentPatch_incomingHorizontal_closed_disjoint_outgoingVertical
      _ _ _ _ _ hbeta (hcoords (i + 1)).2 hextent
  · apply kw_incidentPatch_incomingVertical_closed_disjoint_outgoingVertical
    · exact halpha
    · exact hbeta
    · simpa only [Complex.neg_im] using neg_ne_zero.mpr (hcoords i).2
    · exact (hcoords (i + 1)).1

end StatMech.FrontierA
