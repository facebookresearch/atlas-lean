/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardAdaptiveActualUniformRadius





namespace StatMech.FrontierA

open scoped NNReal
open Set

theorem KWAdaptivePatchedData.middle_subset_edgeTube
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    {eps : ℝ} (heps : 0 < eps ∧ eps < 1 / 2)
    (hepsBeta : eps ≤ patch.beta) (hepsAlpha : ∀ i, eps ≤ patch.alpha i)
    (neighborhood : KWVertexNeighborhoodData polygon)
    (r : ℝ≥0) (hr : 0 < r)
    (hfine : KWEndpointInteriorMeshWithin patch.data r)
    (hrScale : r ≤ neighborhood.scale / 2)
    (i : Fin n) (q : Fin M) (even : Bool) :
    patch.middleClosedEdge i q even ⊆ neighborhood.edgeTube i := by
  obtain ⟨heven, hodd⟩ := patch.middle_rawClosedEdges_subset_coreTube
    r hr hfine hepsBeta hepsAlpha i q
  have hsub : polygon.closedEdgeCoreTube eps r i ⊆
      neighborhood.edgeTube i := by
    rintro z ⟨x, hx, hzx⟩
    refine ⟨x, ?_, ?_⟩
    · exact mem_segment_iff_wbtw.mpr
        ((polygon.closedEdgeCore_subset_edgeInterior heps i hx).1)
    · exact hzx.trans_le (by
        simpa only [KWVertexNeighborhoodData.edgeTube] using hrScale)
  cases even
  · exact (by
      simpa [KWAdaptivePatchedData.middleClosedEdge,
        kwAdaptiveMiddleIndex] using hodd.trans hsub)
  · exact (by
      simpa [KWAdaptivePatchedData.middleClosedEdge,
        kwAdaptiveMiddleIndex] using heven.trans hsub)

theorem KWSmallAdaptiveConnectorScales.actualConnector_subset_vertexBall
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (neighborhood : KWVertexNeighborhoodData polygon)
    (scales : KWSmallAdaptiveConnectorScales polygon neighborhood.scale)
    (hM : 2 ≤ M) (i : Fin n) (even : Bool) :
    let patch := scales.toPatchedData hM
    kwRawClosedEdge patch.vertex
        (kwAdaptiveIdealIndex i (Fin.last M) even) ⊆
      neighborhood.vertexBall (i + 1) := by
  dsimp only
  let patch := scales.toPatchedData hM
  have hin : patch.alpha (i + 1) * ‖polygon.edgeVector i‖ <
      (neighborhood.scale : ℝ) / 4 := by
    have h := scales.incoming_norm_lt (i + 1)
    have hi : i + 1 - 1 = i := by abel
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (scales.halpha (i + 1)), norm_neg, hi] at h
    exact h
  have hout : patch.beta * ‖polygon.edgeVector (i + 1)‖ <
      (neighborhood.scale : ℝ) / 4 := by
    have h := scales.outgoing_norm_lt (i + 1)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos scales.hbeta] at h
    exact h
  have h := patch.connector_rawClosedEdges_subset_ball i
    ((neighborhood.scale : ℝ) / 2) (half_pos neighborhood.scale_pos)
    (by convert hin using 1 <;> ring)
    (by convert hout using 1 <;> ring)
  cases even
  · simpa [kwAdaptiveIdealIndex, KWVertexNeighborhoodData.vertexBall] using h.2
  · simpa [kwAdaptiveIdealIndex, KWVertexNeighborhoodData.vertexBall] using h.1

private theorem KWSmallAdaptiveConnectorScales.actualConnector_disjoint_of_owner_ne
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (neighborhood : KWVertexNeighborhoodData polygon)
    (scales : KWSmallAdaptiveConnectorScales polygon neighborhood.scale)
    (hM : 2 ≤ M) {i j : Fin n} (hij : i ≠ j) (ei ej : Bool) :
    let patch := scales.toPatchedData hM
    Disjoint
      (kwRawClosedEdge patch.vertex
        (kwAdaptiveIdealIndex i (Fin.last M) ei))
      (kwRawClosedEdge patch.vertex
        (kwAdaptiveIdealIndex j (Fin.last M) ej)) := by
  dsimp only
  apply (neighborhood.vertexBall_disjoint (i := i + 1) (j := j + 1)
    (fun h ↦ hij (add_right_cancel h))).mono
  · exact scales.actualConnector_subset_vertexBall neighborhood hM i ei
  · exact scales.actualConnector_subset_vertexBall neighborhood hM j ej

private theorem KWSmallAdaptiveConnectorScales.actualConnector_disjoint_unrelatedMiddle
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (neighborhood : KWVertexNeighborhoodData polygon)
    (scales : KWSmallAdaptiveConnectorScales polygon neighborhood.scale)
    (hM : 2 ≤ M)
    {eps : ℝ} (heps : 0 < eps ∧ eps < 1 / 2)
    (hepsBeta : eps ≤ scales.beta) (hepsAlpha : ∀ i, eps ≤ scales.alpha i)
    (r : ℝ≥0) (hr : 0 < r)
    (hfine : KWEndpointInteriorMeshWithin (scales.toPatchedData hM).data r)
    (hrScale : r ≤ neighborhood.scale / 2)
    (i j : Fin n) (hji : j ≠ i) (hjv : j ≠ i + 1)
    (ei ej : Bool) (q : Fin M) :
    let patch := scales.toPatchedData hM
    Disjoint
      (kwRawClosedEdge patch.vertex
        (kwAdaptiveIdealIndex i (Fin.last M) ei))
      (patch.middleClosedEdge j q ej) := by
  dsimp only
  have hvj : KWVertexEdgeNonincident (i + 1) j := by
    refine ⟨hjv.symm, ?_⟩
    intro h
    apply hji
    exact add_right_cancel h.symm
  apply (neighborhood.vertexBall_disjoint_edgeTube hvj).mono
  · exact scales.actualConnector_subset_vertexBall neighborhood hM i ei
  · exact (scales.toPatchedData hM).middle_subset_edgeTube heps
      hepsBeta hepsAlpha neighborhood r hr hfine hrScale j q ej

private theorem KWAdaptivePatchedData.actualMiddle_disjoint_of_owner_ne
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    {eps : ℝ} (r : ℝ≥0) (hr : 0 < r)
    (hfine : KWEndpointInteriorMeshWithin patch.data r)
    (hepsBeta : eps ≤ patch.beta) (hepsAlpha : ∀ i, eps ≤ patch.alpha i)
    (hcore : ∀ i j : Fin n, i ≠ j →
      Disjoint (polygon.closedEdgeCoreTube eps r i)
        (polygon.closedEdgeCoreTube eps r j))
    {i j : Fin n} (hij : i ≠ j) (q s : Fin M) (ei ej : Bool) :
    Disjoint (patch.middleClosedEdge i q ei)
      (patch.middleClosedEdge j s ej) := by
  obtain ⟨hiEven, hiOdd⟩ := patch.middle_rawClosedEdges_subset_coreTube
    r hr hfine hepsBeta hepsAlpha i q
  obtain ⟨hjEven, hjOdd⟩ := patch.middle_rawClosedEdges_subset_coreTube
    r hr hfine hepsBeta hepsAlpha j s
  cases ei <;> cases ej
  · exact (hcore i j hij).mono (by
      simpa [KWAdaptivePatchedData.middleClosedEdge,
        kwAdaptiveMiddleIndex] using hiOdd) (by
      simpa [KWAdaptivePatchedData.middleClosedEdge,
        kwAdaptiveMiddleIndex] using hjOdd)
  · exact (hcore i j hij).mono (by
      simpa [KWAdaptivePatchedData.middleClosedEdge,
        kwAdaptiveMiddleIndex] using hiOdd) (by
      simpa [KWAdaptivePatchedData.middleClosedEdge,
        kwAdaptiveMiddleIndex] using hjEven)
  · exact (hcore i j hij).mono (by
      simpa [KWAdaptivePatchedData.middleClosedEdge,
        kwAdaptiveMiddleIndex] using hiEven) (by
      simpa [KWAdaptivePatchedData.middleClosedEdge,
        kwAdaptiveMiddleIndex] using hjOdd)
  · exact (hcore i j hij).mono (by
      simpa [KWAdaptivePatchedData.middleClosedEdge,
        kwAdaptiveMiddleIndex] using hiEven) (by
      simpa [KWAdaptivePatchedData.middleClosedEdge,
        kwAdaptiveMiddleIndex] using hjEven)

private theorem KWSmallAdaptiveConnectorScales.actualConnectorMiddle_disjoint
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (neighborhood : KWVertexNeighborhoodData polygon)
    (scales : KWSmallAdaptiveConnectorScales polygon neighborhood.scale)
    (hM : 2 ≤ M)
    {eps : ℝ} (heps : 0 < eps ∧ eps < 1 / 2)
    (hepsBeta : eps ≤ scales.beta) (hepsAlpha : ∀ i, eps ≤ scales.alpha i)
    (r sep : ℝ≥0) (hr : 0 < r)
    (hfine : KWEndpointInteriorMeshWithin (scales.toPatchedData hM).data r)
    (hrScale : r ≤ neighborhood.scale / 2)
    (hcoords : ∀ j : Fin n,
      (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0)
    (hsep : let patch := scales.toPatchedData hM
      ∀ i : Fin n, ∀ first : Bool,
      ∀ x ∈ (if first then
          kwRawClosedEdge patch.idealVertex
            (kwStairEvenIndex i (Fin.last M))
        else kwRawClosedEdge patch.idealVertex
          (kwStairOddIndex i (Fin.last M))),
      ∀ y ∈ (if first then patch.outgoingParameterCarrier (i + 1)
        else patch.incomingParameterCarrier i),
        (sep : ℝ) < dist x y)
    (hsmall : 4 * (r : ℝ) < sep)
    (i j : Fin n) (ei ej : Bool) (q : Fin M)
    (hnon : KWEdgesNonincident
      (kwAdaptiveIdealIndex i (Fin.last M) ei)
      (kwAdaptiveIdealIndex j q.castSucc ej)) :
    let patch := scales.toPatchedData hM
    Disjoint
      (kwRawClosedEdge patch.vertex
        (kwAdaptiveIdealIndex i (Fin.last M) ei))
      (patch.middleClosedEdge j q ej) := by
  dsimp only at hsep ⊢
  let patch := scales.toPatchedData hM
  by_cases hji : j = i
  · subst j
    cases ei with
    | false =>
        simpa [patch, kwAdaptiveIdealIndex,
          KWAdaptivePatchedData.middleClosedEdge, kwAdaptiveMiddleIndex] using
          patch.secondConnector_disjoint_incomingMiddle_of_fine
            r sep hr hfine hsep hsmall i q ej
    | true =>
        by_cases hex : q = patch.lastMiddleIndex ∧ ej = false
        · rcases hex with ⟨rfl, rfl⟩
          have hlast : patch.lastMiddleIndex.succ = Fin.last M := by
            apply Fin.ext
            simp [KWAdaptivePatchedData.lastMiddleIndex]
            have := patch.hM
            omega
          apply (hnon.2.1 ?_).elim
          simp only [kwAdaptiveIdealIndex, if_pos, Bool.false_eq_true, if_false]
          rw [kwStairOddIndex_castSucc_add_one, hlast]
        · have hnot : q ≠ patch.lastMiddleIndex ∨ ej = true := by
            cases ej <;> simp_all
          have hdis := patch.connector_disjoint_incomingMiddle_of_fine
            hcoords r sep hr hfine hsep hsmall i q ej hnot
          simpa [patch, kwAdaptiveIdealIndex,
            KWAdaptivePatchedData.middleClosedEdge,
            kwAdaptiveMiddleIndex] using hdis.mono_left Set.subset_union_left
  · by_cases hjv : j = i + 1
    · subst j
      cases ei with
      | true =>
          simpa [patch, kwAdaptiveIdealIndex,
            KWAdaptivePatchedData.middleClosedEdge,
            kwAdaptiveMiddleIndex] using
            patch.firstConnector_disjoint_outgoingMiddle_of_fine
              r sep hr hfine hsep hsmall i q ej
      | false =>
          by_cases hex : q = 0 ∧ ej = true
          · rcases hex with ⟨rfl, rfl⟩
            apply (hnon.2.2 ?_).elim
            simp only [kwAdaptiveIdealIndex, Bool.false_eq_true, if_false,
              if_pos]
            exact kwStairOddIndex_last_add_one i
          · have hnot : q ≠ 0 ∨ ej = false := by
              cases ej <;> simp_all
            have hdis := patch.connector_disjoint_outgoingMiddle_of_fine
              hcoords r sep hr hfine hsep hsmall i q ej hnot
            simpa [patch, kwAdaptiveIdealIndex,
              KWAdaptivePatchedData.middleClosedEdge,
              kwAdaptiveMiddleIndex] using hdis.mono_left Set.subset_union_right
    · exact scales.actualConnector_disjoint_unrelatedMiddle neighborhood hM
        heps hepsBeta hepsAlpha r hr hfine hrScale i j hji hjv ei ej q

private theorem KWSmallAdaptiveConnectorScales.actualMiddleMiddle_disjoint
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (scales : KWSmallAdaptiveConnectorScales polygon R)
    (hM : 2 ≤ M) {eps : ℝ} (r : ℝ≥0) (hr : 0 < r)
    (hfine : KWEndpointInteriorMeshWithin (scales.toPatchedData hM).data r)
    (hepsBeta : eps ≤ scales.beta) (hepsAlpha : ∀ i, eps ≤ scales.alpha i)
    (hcore : ∀ i j : Fin n, i ≠ j →
      Disjoint (polygon.closedEdgeCoreTube eps r i)
        (polygon.closedEdgeCoreTube eps r j))
    (hcoords : ∀ j : Fin n,
      (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0)
    (i j : Fin n) (ei ej : Bool) (q s : Fin M)
    (hnon : KWEdgesNonincident
      (kwAdaptiveIdealIndex i q.castSucc ei)
      (kwAdaptiveIdealIndex j s.castSucc ej)) :
    let patch := scales.toPatchedData hM
    Disjoint (patch.middleClosedEdge i q ei)
      (patch.middleClosedEdge j s ej) := by
  dsimp only
  let patch := scales.toPatchedData hM
  by_cases hij : i = j
  · subst j
    apply patch.middleClosedEdges_disjoint_sameOwner hcoords i q s ei ej
    simpa [kwAdaptiveIdealIndex, kwAdaptiveMiddleIndex] using hnon
  · exact patch.actualMiddle_disjoint_of_owner_ne r hr hfine
      hepsBeta hepsAlpha hcore hij q s ei ej

theorem KWSmallAdaptiveConnectorScales.actual_nonincident_disjoint
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (neighborhood : KWVertexNeighborhoodData polygon)
    (scales : KWSmallAdaptiveConnectorScales polygon neighborhood.scale)
    (hM : 2 ≤ M)
    {eps : ℝ} (heps : 0 < eps ∧ eps < 1 / 2)
    (hepsBeta : eps ≤ scales.beta) (hepsAlpha : ∀ i, eps ≤ scales.alpha i)
    (r sep : ℝ≥0) (hr : 0 < r)
    (hfine : KWEndpointInteriorMeshWithin (scales.toPatchedData hM).data r)
    (hrScale : r ≤ neighborhood.scale / 2)
    (hcore : ∀ i j : Fin n, i ≠ j →
      Disjoint (polygon.closedEdgeCoreTube eps r i)
        (polygon.closedEdgeCoreTube eps r j))
    (hcoords : ∀ j : Fin n,
      (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0)
    (hsep : let patch := scales.toPatchedData hM
      ∀ i : Fin n, ∀ first : Bool,
      ∀ x ∈ (if first then
          kwRawClosedEdge patch.idealVertex
            (kwStairEvenIndex i (Fin.last M))
        else kwRawClosedEdge patch.idealVertex
          (kwStairOddIndex i (Fin.last M))),
      ∀ y ∈ (if first then patch.outgoingParameterCarrier (i + 1)
        else patch.incomingParameterCarrier i),
        (sep : ℝ) < dist x y)
    (hsmall : 4 * (r : ℝ) < sep) :
    let patch := scales.toPatchedData hM
    ∀ a b : Fin (n * (2 * (M + 1))), KWEdgesNonincident a b →
      Disjoint (kwRawClosedEdge patch.vertex a)
        (kwRawClosedEdge patch.vertex b) := by
  dsimp only at hsep ⊢
  intro a b hnon
  obtain ⟨i, k, rfl | rfl⟩ := kwStairIndex_even_or_odd a
  · by_cases hk : k = Fin.last M
    · subst k
      obtain ⟨j, l, rfl | rfl⟩ := kwStairIndex_even_or_odd b
      · by_cases hl : l = Fin.last M
        · subst l
          by_cases hij : i = j
          · subst j; exact (hnon.1 rfl).elim
          · exact scales.actualConnector_disjoint_of_owner_ne neighborhood hM
              hij true true
        · obtain ⟨s, rfl⟩ := Fin.eq_castSucc_of_ne_last hl
          exact scales.actualConnectorMiddle_disjoint neighborhood hM heps
            hepsBeta hepsAlpha r sep hr hfine hrScale hcoords hsep hsmall
              i j true true s hnon
      · by_cases hl : l = Fin.last M
        · subst l
          by_cases hij : i = j
          · subst j
            exact (hnon.2.2 (kwStairEvenIndex_add_one i (Fin.last M))).elim
          · exact scales.actualConnector_disjoint_of_owner_ne neighborhood hM
              hij true false
        · obtain ⟨s, rfl⟩ := Fin.eq_castSucc_of_ne_last hl
          exact scales.actualConnectorMiddle_disjoint neighborhood hM heps
            hepsBeta hepsAlpha r sep hr hfine hrScale hcoords hsep hsmall
              i j true false s hnon
    · obtain ⟨q, rfl⟩ := Fin.eq_castSucc_of_ne_last hk
      obtain ⟨j, l, rfl | rfl⟩ := kwStairIndex_even_or_odd b
      · by_cases hl : l = Fin.last M
        · subst l
          exact (scales.actualConnectorMiddle_disjoint neighborhood hM heps
            hepsBeta hepsAlpha r sep hr hfine hrScale hcoords hsep hsmall
              j i true true q hnon.symm).symm
        · obtain ⟨s, rfl⟩ := Fin.eq_castSucc_of_ne_last hl
          exact scales.actualMiddleMiddle_disjoint hM r hr hfine
            hepsBeta hepsAlpha hcore hcoords i j true true q s hnon
      · by_cases hl : l = Fin.last M
        · subst l
          exact (scales.actualConnectorMiddle_disjoint neighborhood hM heps
            hepsBeta hepsAlpha r sep hr hfine hrScale hcoords hsep hsmall
              j i false true q hnon.symm).symm
        · obtain ⟨s, rfl⟩ := Fin.eq_castSucc_of_ne_last hl
          exact scales.actualMiddleMiddle_disjoint hM r hr hfine
            hepsBeta hepsAlpha hcore hcoords i j true false q s hnon
  · by_cases hk : k = Fin.last M
    · subst k
      obtain ⟨j, l, rfl | rfl⟩ := kwStairIndex_even_or_odd b
      · by_cases hl : l = Fin.last M
        · subst l
          by_cases hij : i = j
          · subst j
            exact (hnon.2.1 (kwStairEvenIndex_add_one i (Fin.last M)).symm).elim
          · exact scales.actualConnector_disjoint_of_owner_ne neighborhood hM
              hij false true
        · obtain ⟨s, rfl⟩ := Fin.eq_castSucc_of_ne_last hl
          exact scales.actualConnectorMiddle_disjoint neighborhood hM heps
            hepsBeta hepsAlpha r sep hr hfine hrScale hcoords hsep hsmall
              i j false true s hnon
      · by_cases hl : l = Fin.last M
        · subst l
          by_cases hij : i = j
          · subst j; exact (hnon.1 rfl).elim
          · exact scales.actualConnector_disjoint_of_owner_ne neighborhood hM
              hij false false
        · obtain ⟨s, rfl⟩ := Fin.eq_castSucc_of_ne_last hl
          exact scales.actualConnectorMiddle_disjoint neighborhood hM heps
            hepsBeta hepsAlpha r sep hr hfine hrScale hcoords hsep hsmall
              i j false false s hnon
    · obtain ⟨q, rfl⟩ := Fin.eq_castSucc_of_ne_last hk
      obtain ⟨j, l, rfl | rfl⟩ := kwStairIndex_even_or_odd b
      · by_cases hl : l = Fin.last M
        · subst l
          exact (scales.actualConnectorMiddle_disjoint neighborhood hM heps
            hepsBeta hepsAlpha r sep hr hfine hrScale hcoords hsep hsmall
              j i true false q hnon.symm).symm
        · obtain ⟨s, rfl⟩ := Fin.eq_castSucc_of_ne_last hl
          exact scales.actualMiddleMiddle_disjoint hM r hr hfine
            hepsBeta hepsAlpha hcore hcoords i j false true q s hnon
      · by_cases hl : l = Fin.last M
        · subst l
          exact (scales.actualConnectorMiddle_disjoint neighborhood hM heps
            hepsBeta hepsAlpha r sep hr hfine hrScale hcoords hsep hsmall
              j i false false q hnon.symm).symm
        · obtain ⟨s, rfl⟩ := Fin.eq_castSucc_of_ne_last hl
          exact scales.actualMiddleMiddle_disjoint hM r hr hfine
            hepsBeta hepsAlpha hcore hcoords i j false false q s hnon

private theorem closedEdgeCoreTube_mono_radius
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (eps : ℝ) {r s : ℝ≥0} (hrs : r ≤ s) (i : Fin n) :
    polygon.closedEdgeCoreTube eps r i ⊆
      polygon.closedEdgeCoreTube eps s i := by
  rintro z ⟨x, hx, hzx⟩
  exact ⟨x, hx, hzx.trans_le (by exact_mod_cast hrs)⟩

theorem KWSmallAdaptiveConnectorScales.actualRawSimpleData
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (neighborhood : KWVertexNeighborhoodData polygon)
    (scales : KWSmallAdaptiveConnectorScales polygon neighborhood.scale)
    (hM : 2 ≤ M)
    {eps : ℝ} (heps : 0 < eps ∧ eps < 1 / 2)
    (hepsBeta : eps ≤ scales.beta) (hepsAlpha : ∀ i, eps ≤ scales.alpha i)
    (r sep : ℝ≥0) (hr : 0 < r)
    (hfine : KWEndpointInteriorMeshWithin (scales.toPatchedData hM).data r)
    (hrScale : r ≤ neighborhood.scale / 2)
    (hcore : ∀ i j : Fin n, i ≠ j →
      Disjoint (polygon.closedEdgeCoreTube eps r i)
        (polygon.closedEdgeCoreTube eps r j))
    (hcoords : ∀ j : Fin n,
      (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0)
    (hsep : let patch := scales.toPatchedData hM
      ∀ i : Fin n, ∀ first : Bool,
      ∀ x ∈ (if first then
          kwRawClosedEdge patch.idealVertex
            (kwStairEvenIndex i (Fin.last M))
        else kwRawClosedEdge patch.idealVertex
          (kwStairOddIndex i (Fin.last M))),
      ∀ y ∈ (if first then patch.outgoingParameterCarrier (i + 1)
        else patch.incomingParameterCarrier i),
        (sep : ℝ) < dist x y)
    (hsmall : 4 * (r : ℝ) < sep) :
    let patch := scales.toPatchedData hM
    KWRawNonbacktrackingSimpleData patch.vertex := by
  dsimp only at hsep ⊢
  let patch := scales.toPatchedData hM
  apply KWRawNonbacktrackingSimpleData.of_turnAdmissible
  · calc
      3 ≤ n := polygon.three_le
      _ = n * 1 := by omega
      _ ≤ n * (2 * (M + 1)) := Nat.mul_le_mul_left n (by omega)
  · exact patch.rawEdge_ne_zero hcoords
  · exact patch.turnAdmissible hcoords
  · exact scales.actual_nonincident_disjoint neighborhood hM heps
      hepsBeta hepsAlpha r sep hr hfine hrScale hcore hcoords hsep hsmall

theorem KWSmallAdaptiveConnectorScales.exists_actualSimplePolygon_eq_patch
    {n : ℕ} [NeZero n] {polygon : KWFiniteSimplePolygon n}
    (neighborhood : KWVertexNeighborhoodData polygon)
    (scales : KWSmallAdaptiveConnectorScales polygon neighborhood.scale)
    (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j)
      (polygon.edgeVector (j + 1)) ≠ 0)
    (hcoords : ∀ j : Fin n,
      (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0) :
    ∃ M : ℕ, ∃ inst : NeZero M, ∃ hM : 2 ≤ M,
      letI : NeZero M := inst
      ∃ actual : KWFiniteSimplePolygon (n * (2 * (M + 1))),
        actual.vertex = (scales.toPatchedData hM).vertex := by
  obtain ⟨eps, hepsPos, hepsHalf, hepsBeta, hepsAlpha⟩ :=
    exists_common_endpoint_core_trim scales.beta scales.alpha scales.hbeta
      scales.beta_lt_quarter scales.halpha
  have heps : 0 < eps ∧ eps < 1 / 2 := ⟨hepsPos, hepsHalf⟩
  obtain ⟨coreRadius, hcoreRadius, hcore⟩ :=
    polygon.exists_pairwise_disjoint_closedEdgeCoreTubes heps
  obtain ⟨sep, hsep, hremote⟩ :=
    scales.exists_uniform_remoteParameter_radius hcross hcoords
  let r : ℝ≥0 := min coreRadius
    (min (neighborhood.scale / 2) (sep / 8))
  have hr : 0 < r := by
    dsimp only [r]
    exact lt_min hcoreRadius (lt_min (half_pos neighborhood.scale_pos)
      (div_pos hsep (by norm_num)))
  have hrCore : r ≤ coreRadius := min_le_left _ _
  have hrScale : r ≤ neighborhood.scale / 2 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hrSep : r ≤ sep / 8 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hsmall : 4 * (r : ℝ) < sep := by
    have hsepReal : 0 < (sep : ℝ) := by exact_mod_cast hsep
    have hrSepReal : (r : ℝ) ≤ sep / 8 := by exact_mod_cast hrSep
    norm_num at hrSepReal ⊢
    linarith
  obtain ⟨M, hM, hfine⟩ := scales.exists_interiorMesh_patch r hr
  let instM : NeZero M := ⟨by omega⟩
  refine ⟨M, instM, hM, ?_⟩
  letI : NeZero M := instM
  let patch := scales.toPatchedData hM
  have hcore' : ∀ i j : Fin n, i ≠ j →
      Disjoint (polygon.closedEdgeCoreTube eps r i)
        (polygon.closedEdgeCoreTube eps r j) := by
    intro i j hij
    exact (hcore i j hij).mono
      (closedEdgeCoreTube_mono_radius polygon eps hrCore i)
      (closedEdgeCoreTube_mono_radius polygon eps hrCore j)
  have hsepM := hremote hM
  let actual :=
    (scales.actualRawSimpleData neighborhood hM heps hepsBeta hepsAlpha
      r sep hr hfine hrScale hcore' hcoords hsepM hsmall).toFiniteSimplePolygon
  exact ⟨actual, rfl⟩


theorem KWSmallAdaptiveConnectorScales.exists_actualSimplePolygon
    {n : ℕ} [NeZero n] {polygon : KWFiniteSimplePolygon n}
    (neighborhood : KWVertexNeighborhoodData polygon)
    (scales : KWSmallAdaptiveConnectorScales polygon neighborhood.scale)
    (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j)
      (polygon.edgeVector (j + 1)) ≠ 0)
    (hcoords : ∀ j : Fin n,
      (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0) :
    ∃ M : ℕ, ∃ inst : NeZero M, ∃ hM : 2 ≤ M,
      letI : NeZero M := inst
      Nonempty (KWFiniteSimplePolygon (n * (2 * (M + 1)))) := by
  obtain ⟨M, inst, hM, actual, _⟩ :=
    scales.exists_actualSimplePolygon_eq_patch neighborhood hcross hcoords
  exact ⟨M, inst, hM, ⟨actual⟩⟩

end StatMech.FrontierA
