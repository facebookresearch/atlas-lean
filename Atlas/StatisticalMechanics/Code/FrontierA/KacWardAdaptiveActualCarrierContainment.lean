/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardAdaptiveActualIncidentSeparation
import Code.FrontierA.KacWardAdaptiveIdealApproximation





namespace StatMech.FrontierA

open scoped NNReal
open Set

def KWAdaptivePatchedData.outgoingParameterCarrier
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) (i : Fin n) : Set ℂ :=
  AffineMap.lineMap (polygon.vertex i) (polygon.vertex (i + 1)) ''
    Icc patch.beta 1

def KWAdaptivePatchedData.incomingParameterCarrier
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) (i : Fin n) : Set ℂ :=
  AffineMap.lineMap (polygon.vertex i) (polygon.vertex (i + 1)) ''
    Icc 0 (1 - patch.alpha (i + 1))

theorem KWAdaptivePatchedData.idealMiddle_subset_outgoingParameterCarrier
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) (even : Bool) :
    patch.idealMiddleClosedEdge i q even ⊆
      patch.outgoingParameterCarrier i := by
  intro z hz
  obtain ⟨u, hu, rfl⟩ :=
    patch.idealMiddleClosedEdge_point_parameter i q even hz
  refine ⟨u, ?_, rfl⟩
  constructor
  · calc
      patch.beta = patch.data.parameter i (0 : Fin (M + 2)).succ :=
        (patch.parameter_one i).symm
      _ ≤ patch.data.parameter i q.succ.castSucc.castSucc :=
        (patch.data.parameter_strictMono i).monotone (by
          apply Fin.mk_le_mk.mpr
          change 1 ≤ q.val + 1
          omega)
      _ ≤ u := hu.1
  · exact hu.2.trans
      (patch.data.parameter_mem_Icc i q.succ.castSucc.succ).2

theorem KWAdaptivePatchedData.idealMiddle_subset_incomingParameterCarrier
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) (even : Bool) :
    patch.idealMiddleClosedEdge i q even ⊆
      patch.incomingParameterCarrier i := by
  intro z hz
  obtain ⟨u, hu, rfl⟩ :=
    patch.idealMiddleClosedEdge_point_parameter i q even hz
  refine ⟨u, ?_, rfl⟩
  constructor
  · exact (patch.data.parameter_mem_Icc i
      q.succ.castSucc.castSucc).1.trans hu.1
  · calc
      u ≤ patch.data.parameter i q.succ.castSucc.succ := hu.2
      _ ≤ patch.data.parameter i (Fin.last (M + 1)).castSucc :=
        (patch.data.parameter_strictMono i).monotone (by
          apply Fin.mk_le_mk.mpr
          change q.val + 2 ≤ M + 1
          omega)
      _ = 1 - patch.alpha (i + 1) := patch.parameter_penultimate i

theorem KWAdaptivePatchedData.outgoingParameterCarrier_isCompact
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) (i : Fin n) :
    IsCompact (patch.outgoingParameterCarrier i) := by
  rw [KWAdaptivePatchedData.outgoingParameterCarrier]
  exact isCompact_Icc.image AffineMap.lineMap_continuous

theorem KWAdaptivePatchedData.incomingParameterCarrier_isCompact
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) (i : Fin n) :
    IsCompact (patch.incomingParameterCarrier i) := by
  rw [KWAdaptivePatchedData.incomingParameterCarrier]
  exact isCompact_Icc.image AffineMap.lineMap_continuous

theorem KWAdaptivePatchedData.outgoingParameterCarrier_subset_portTail
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) (i : Fin n) :
    patch.outgoingParameterCarrier i ⊆
      ({polygon.vertex i + patch.beta * polygon.edgeVector i} ∪
        kwTranslatedOpenRayTail (polygon.vertex i)
          (patch.beta * polygon.edgeVector i)) := by
  rintro z ⟨u, hu, rfl⟩
  rw [AffineMap.lineMap_apply]
  simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul]
  by_cases hub : u = patch.beta
  · left
    rw [Set.mem_singleton_iff, hub]
    unfold KWFiniteSimplePolygon.edgeVector
    ring
  · right
    let t := u / patch.beta
    have ht : 1 < t := by
      apply (lt_div_iff₀ patch.hbeta).mpr
      simpa only [one_mul] using lt_of_le_of_ne hu.1 (Ne.symm hub)
    refine ⟨t, ht, ?_⟩
    dsimp only [t]
    unfold KWFiniteSimplePolygon.edgeVector
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr patch.hbeta.ne']
    ring

theorem KWAdaptivePatchedData.incomingParameterCarrier_subset_portTail
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) (i : Fin n) :
    patch.incomingParameterCarrier i ⊆
      ({polygon.vertex (i + 1) +
          patch.alpha (i + 1) * (-polygon.edgeVector i)} ∪
        kwTranslatedOpenRayTail (polygon.vertex (i + 1))
          (patch.alpha (i + 1) * (-polygon.edgeVector i))) := by
  rintro z ⟨u, hu, rfl⟩
  rw [AffineMap.lineMap_apply]
  simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul]
  have hvertex : polygon.vertex i + u * polygon.edgeVector i =
      polygon.vertex (i + 1) + (1 - u) * (-polygon.edgeVector i) := by
    unfold KWFiniteSimplePolygon.edgeVector
    push_cast
    ring
  rw [show u * (polygon.vertex (i + 1) - polygon.vertex i) +
      polygon.vertex i = polygon.vertex i + u * polygon.edgeVector i by
    unfold KWFiniteSimplePolygon.edgeVector
    ring, hvertex]
  by_cases hua : 1 - u = patch.alpha (i + 1)
  · left
    rw [Set.mem_singleton_iff]
    have huac := congrArg (fun r : ℝ ↦ (r : ℂ)) hua
    push_cast at huac
    rw [huac]
  · right
    let t := (1 - u) / patch.alpha (i + 1)
    have ht : 1 < t := by
      apply (lt_div_iff₀ (patch.halpha (i + 1))).mpr
      have hle : patch.alpha (i + 1) ≤ 1 - u := by linarith [hu.2]
      simpa only [one_mul] using lt_of_le_of_ne hle (Ne.symm hua)
    refine ⟨t, ht, ?_⟩
    dsimp only [t]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr (patch.halpha (i + 1)).ne']

theorem KWAdaptivePatchedData.firstConnector_disjoint_outgoingParameterCarrier
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j)
      (polygon.edgeVector (j + 1)) ≠ 0)
    (hcoords : ∀ j : Fin n,
      (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0)
    (i : Fin n) :
    Disjoint
      (kwRawClosedEdge patch.idealVertex
        (kwStairEvenIndex i (Fin.last M)))
      (patch.outgoingParameterCarrier (i + 1)) :=
  (patch.idealConnectorFirstClosedEdge_disjoint_outgoingPortTail
    hcross hcoords i).mono_right
      (patch.outgoingParameterCarrier_subset_portTail (i + 1))

theorem KWAdaptivePatchedData.secondConnector_disjoint_incomingParameterCarrier
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j)
      (polygon.edgeVector (j + 1)) ≠ 0)
    (hcoords : ∀ j : Fin n,
      (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0)
    (i : Fin n) :
    Disjoint
      (kwRawClosedEdge patch.idealVertex
        (kwStairOddIndex i (Fin.last M)))
      (patch.incomingParameterCarrier i) :=
  (patch.idealConnectorSecondClosedEdge_disjoint_incomingPortTail
    hcross hcoords i).mono_right
      (patch.incomingParameterCarrier_subset_portTail i)

theorem KWAdaptivePatchedData.dist_middleCorner_ideal_lt_two_mul_of_interiorMesh
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (r : ℝ≥0) (hfine : KWEndpointInteriorMeshWithin patch.data r)
    (i : Fin n) (q : Fin M) :
    dist (patch.middleCorner i q) (patch.idealMiddleCorner i q) < 2 * r := by
  let base := patch.data.base i q.succ.castSucc.castSucc
  have hk0 : q.succ.castSucc ≠ (0 : Fin (M + 2)) := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_zero] at hval
    omega
  have hklast : q.succ.castSucc ≠ Fin.last (M + 1) := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last] at hval
    exact (Nat.ne_of_lt q.isLt) (by omega)
  have hmesh := hfine i q.succ.castSucc hk0 hklast
  have hdelta : 0 < patch.data.parameter i q.succ.castSucc.succ -
      patch.data.parameter i q.succ.castSucc.castSucc :=
    patch.middleDelta_pos i q
  have hactual : ‖patch.middleCorner i q - base‖ < r := by
    rw [patch.middleCorner_sub_base, norm_mul, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdelta]
    by_cases hv : patch.sliceUsesVerticalFirst i q
    · rw [if_pos hv]
      exact (mul_le_mul_of_nonneg_left
        (norm_kwVerticalPart_le (polygon.edgeVector i)) hdelta.le).trans_lt hmesh
    · rw [if_neg hv]
      exact (mul_le_mul_of_nonneg_left
        (norm_kwHorizontalPart_le (polygon.edgeVector i)) hdelta.le).trans_lt hmesh
  have hideal : ‖patch.idealMiddleCorner i q - base‖ < r := by
    have hdeltaNorm :
        ‖(patch.data.parameter i q.succ.castSucc.succ : ℝ) -
          patch.data.parameter i q.succ.castSucc.castSucc‖ =
        (patch.data.parameter i q.succ.castSucc.succ : ℝ) -
          patch.data.parameter i q.succ.castSucc.castSucc :=
      Real.norm_of_nonneg hdelta.le
    rw [patch.idealMiddleCorner_sub_base, norm_mul, norm_mul,
      ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real, hdeltaNorm]
    norm_num
    have hprod : 0 ≤
        (patch.data.parameter i q.castSucc.succ.succ -
            patch.data.parameter i q.castSucc.castSucc.succ) *
          ‖polygon.edgeVector i‖ :=
      mul_nonneg hdelta.le (norm_nonneg _)
    have hmesh' :
        (patch.data.parameter i q.castSucc.succ.succ -
            patch.data.parameter i q.castSucc.castSucc.succ) *
          ‖polygon.edgeVector i‖ < r := hmesh
    unfold KWFiniteSimplePolygon.edgeVector at hmesh' hprod
    unfold kwCyclicEdgeVector
    nlinarith [hmesh']
  rw [dist_eq_norm]
  have heq : patch.middleCorner i q - patch.idealMiddleCorner i q =
      (patch.middleCorner i q - base) -
        (patch.idealMiddleCorner i q - base) := by ring
  rw [heq]
  exact (norm_sub_le _ _).trans_lt (by
    have hr : (r : ℝ) + r = 2 * r := by ring
    rw [← hr]
    exact add_lt_add hactual hideal)

theorem KWAdaptivePatchedData.dist_vertex_idealVertex_lt_two_mul_of_interiorMesh
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (r : ℝ≥0) (hr : 0 < r)
    (hfine : KWEndpointInteriorMeshWithin patch.data r) :
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
      exact patch.dist_middleCorner_ideal_lt_two_mul_of_interiorMesh
        r hfine i q

theorem KWAdaptivePatchedData.actualConnectorMiddle_disjoint_of_carrier
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (r sep : ℝ≥0) (hr : 0 < r)
    (hfine : KWEndpointInteriorMeshWithin patch.data r)
    (a : Fin (n * (2 * (M + 1))))
    (i : Fin n) (q : Fin M) (even : Bool) (carrier : Set ℂ)
    (hcarrier : patch.idealMiddleClosedEdge i q even ⊆ carrier)
    (hsep : ∀ x ∈ kwRawClosedEdge patch.idealVertex a,
      ∀ y ∈ carrier, (sep : ℝ) < dist x y)
    (hsmall : 4 * (r : ℝ) < sep) :
    Disjoint (kwRawClosedEdge patch.vertex a)
      (patch.middleClosedEdge i q even) := by
  rw [kwRawClosedEdge, KWAdaptivePatchedData.middleClosedEdge,
    kwRawClosedEdge]
  apply segment_disjoint_of_perturbation
    (le_of_lt (patch.dist_vertex_idealVertex_lt_two_mul_of_interiorMesh
      r hr hfine a))
    (le_of_lt (patch.dist_vertex_idealVertex_lt_two_mul_of_interiorMesh
      r hr hfine (a + 1)))
    (le_of_lt (patch.dist_vertex_idealVertex_lt_two_mul_of_interiorMesh
      r hr hfine
      (kwAdaptiveMiddleIndex i q even)))
    (le_of_lt (patch.dist_vertex_idealVertex_lt_two_mul_of_interiorMesh
      r hr hfine
      (kwAdaptiveMiddleIndex i q even + 1)))
    (by
      intro x hx y hy
      apply hsep x
      · simpa only [kwRawClosedEdge] using hx
      · apply hcarrier
        cases even <;> simpa [KWAdaptivePatchedData.idealMiddleClosedEdge,
          kwAdaptiveMiddleIndex, kwRawClosedEdge] using hy)
  norm_num at hsmall ⊢
  linarith

private theorem kwRawClosedEdge_isCompact
    {N : ℕ} [NeZero N] (vertex : Fin N → ℂ) (i : Fin N) :
    IsCompact (kwRawClosedEdge vertex i) := by
  rw [kwRawClosedEdge, segment_eq_image_lineMap]
  exact isCompact_Icc.image AffineMap.lineMap_continuous

theorem KWAdaptivePatchedData.exists_remoteParameter_dist_separation
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j)
      (polygon.edgeVector (j + 1)) ≠ 0)
    (hcoords : ∀ j : Fin n,
      (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0)
    (i : Fin n) (first : Bool) :
    ∃ sep : ℝ≥0, 0 < sep ∧
      ∀ x ∈ (if first then
          kwRawClosedEdge patch.idealVertex
            (kwStairEvenIndex i (Fin.last M))
        else kwRawClosedEdge patch.idealVertex
          (kwStairOddIndex i (Fin.last M))),
      ∀ y ∈ (if first then patch.outgoingParameterCarrier (i + 1)
        else patch.incomingParameterCarrier i),
        (sep : ℝ) < dist x y := by
  cases first with
  | false =>
      obtain ⟨sep, hsep, hdist⟩ := Metric.exists_pos_forall_lt_edist
        (kwRawClosedEdge_isCompact patch.idealVertex
          (kwStairOddIndex i (Fin.last M)))
        (patch.incomingParameterCarrier_isCompact i).isClosed
        (patch.secondConnector_disjoint_incomingParameterCarrier
          hcross hcoords i)
      refine ⟨sep, hsep, ?_⟩
      intro x hx y hy
      have h := hdist x (by simpa using hx) y hy
      rw [edist_dist] at h
      exact ENNReal.coe_lt_ofReal.mp h
  | true =>
      obtain ⟨sep, hsep, hdist⟩ := Metric.exists_pos_forall_lt_edist
        (kwRawClosedEdge_isCompact patch.idealVertex
          (kwStairEvenIndex i (Fin.last M)))
        (patch.outgoingParameterCarrier_isCompact (i + 1)).isClosed
        (patch.firstConnector_disjoint_outgoingParameterCarrier
          hcross hcoords i)
      refine ⟨sep, hsep, ?_⟩
      intro x hx y hy
      have h := hdist x (by simpa using hx) y hy
      rw [edist_dist] at h
      exact ENNReal.coe_lt_ofReal.mp h

end StatMech.FrontierA
