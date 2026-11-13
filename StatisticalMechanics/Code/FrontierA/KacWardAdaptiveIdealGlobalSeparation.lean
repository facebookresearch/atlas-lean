/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardAdaptiveIdealLocalSeparation





namespace StatMech.FrontierA

open scoped NNReal
open Set

def kwAdaptiveIdealIndex
    {n M : ℕ} [NeZero n] [NeZero M]
    (i : Fin n) (k : Fin (M + 1)) (even : Bool) :
    Fin (n * (2 * (M + 1))) :=
  if even then kwStairEvenIndex i k else kwStairOddIndex i k

theorem KWAdaptivePatchedData.idealMiddle_subset_closedEdgeTube
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    {eps : ℝ} (heps : 0 < eps ∧ eps < 1 / 2)
    (hepsBeta : eps ≤ patch.beta) (hepsAlpha : ∀ i, eps ≤ patch.alpha i)
    (neighborhood : KWVertexNeighborhoodData polygon)
    (i : Fin n) (q : Fin M) (even : Bool) :
    patch.idealMiddleClosedEdge i q even ⊆ neighborhood.edgeTube i := by
  have hcoreClosed : polygon.closedEdgeCore eps i ⊆ polygon.closedEdge i := by
    intro z hz
    exact mem_segment_iff_wbtw.mpr
      ((polygon.closedEdgeCore_subset_edgeInterior heps i hz).1)
  have hclosedTube : polygon.closedEdge i ⊆ neighborhood.edgeTube i := by
    unfold KWVertexNeighborhoodData.edgeTube
    apply polygon.closedEdge_subset_closedEdgeTube
    exact div_pos neighborhood.scale_pos (by norm_num)
  cases even with
  | false =>
      exact (patch.idealRawClosedEdge_odd_subset_core
        hepsBeta hepsAlpha i q).trans (hcoreClosed.trans hclosedTube)
  | true =>
      exact (patch.idealRawClosedEdge_even_subset_core
        hepsBeta hepsAlpha i q).trans (hcoreClosed.trans hclosedTube)

theorem KWSmallAdaptiveConnectorScales.idealConnector_subset_vertexBall
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (neighborhood : KWVertexNeighborhoodData polygon)
    (scales : KWSmallAdaptiveConnectorScales polygon neighborhood.scale)
    (hM : 2 ≤ M) (i : Fin n) (even : Bool) :
    let patch := scales.toPatchedData hM
    kwRawClosedEdge patch.idealVertex
        (kwAdaptiveIdealIndex i (Fin.last M) even) ⊆
      neighborhood.vertexBall (i + 1) := by
  dsimp only
  obtain ⟨hfirst, hsecond⟩ :=
    scales.idealConnectorClosedEdges_subset_vertexBall neighborhood hM i
  cases even
  · simpa [kwAdaptiveIdealIndex] using hsecond
  · simpa [kwAdaptiveIdealIndex] using hfirst

private theorem KWAdaptivePatchedData.idealMiddle_disjoint_of_owner_ne
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    {eps : ℝ} (heps : 0 < eps ∧ eps < 1 / 2)
    (hepsBeta : eps ≤ patch.beta) (hepsAlpha : ∀ i, eps ≤ patch.alpha i)
    {i j : Fin n} (hij : i ≠ j) (q r : Fin M) (ei ej : Bool) :
    Disjoint (patch.idealMiddleClosedEdge i q ei)
      (patch.idealMiddleClosedEdge j r ej) := by
  have hcore := polygon.closedEdgeCore_disjoint heps hij
  cases ei <;> cases ej
  · exact hcore.mono
      (patch.idealRawClosedEdge_odd_subset_core hepsBeta hepsAlpha i q)
      (patch.idealRawClosedEdge_odd_subset_core hepsBeta hepsAlpha j r)
  · exact hcore.mono
      (patch.idealRawClosedEdge_odd_subset_core hepsBeta hepsAlpha i q)
      (patch.idealRawClosedEdge_even_subset_core hepsBeta hepsAlpha j r)
  · exact hcore.mono
      (patch.idealRawClosedEdge_even_subset_core hepsBeta hepsAlpha i q)
      (patch.idealRawClosedEdge_odd_subset_core hepsBeta hepsAlpha j r)
  · exact hcore.mono
      (patch.idealRawClosedEdge_even_subset_core hepsBeta hepsAlpha i q)
      (patch.idealRawClosedEdge_even_subset_core hepsBeta hepsAlpha j r)

private theorem KWSmallAdaptiveConnectorScales.idealConnector_disjoint_of_owner_ne
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (neighborhood : KWVertexNeighborhoodData polygon)
    (scales : KWSmallAdaptiveConnectorScales polygon neighborhood.scale)
    (hM : 2 ≤ M) {i j : Fin n} (hij : i ≠ j) (ei ej : Bool) :
    let patch := scales.toPatchedData hM
    Disjoint
      (kwRawClosedEdge patch.idealVertex
        (kwAdaptiveIdealIndex i (Fin.last M) ei))
      (kwRawClosedEdge patch.idealVertex
        (kwAdaptiveIdealIndex j (Fin.last M) ej)) := by
  dsimp only
  apply (neighborhood.vertexBall_disjoint (i := i + 1) (j := j + 1)
    (fun h ↦ hij (add_right_cancel h))).mono
  · exact scales.idealConnector_subset_vertexBall neighborhood hM i ei
  · exact scales.idealConnector_subset_vertexBall neighborhood hM j ej

private theorem KWSmallAdaptiveConnectorScales.idealConnector_disjoint_unrelatedMiddle
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (neighborhood : KWVertexNeighborhoodData polygon)
    (scales : KWSmallAdaptiveConnectorScales polygon neighborhood.scale)
    (hM : 2 ≤ M)
    {eps : ℝ} (heps : 0 < eps ∧ eps < 1 / 2)
    (hepsBeta : eps ≤ scales.beta) (hepsAlpha : ∀ i, eps ≤ scales.alpha i)
    (i j : Fin n) (hji : j ≠ i) (hjv : j ≠ i + 1)
    (ei ej : Bool) (q : Fin M) :
    let patch := scales.toPatchedData hM
    Disjoint
      (kwRawClosedEdge patch.idealVertex
        (kwAdaptiveIdealIndex i (Fin.last M) ei))
      (patch.idealMiddleClosedEdge j q ej) := by
  dsimp only
  have hvj : KWVertexEdgeNonincident (i + 1) j := by
    refine ⟨hjv.symm, ?_⟩
    intro h
    apply hji
    exact add_right_cancel h.symm
  apply (neighborhood.vertexBall_disjoint_edgeTube hvj).mono
  · exact scales.idealConnector_subset_vertexBall neighborhood hM i ei
  · exact (scales.toPatchedData hM).idealMiddle_subset_closedEdgeTube
      heps hepsBeta hepsAlpha neighborhood j q ej

private theorem KWSmallAdaptiveConnectorScales.idealConnectorMiddle_disjoint
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (neighborhood : KWVertexNeighborhoodData polygon)
    (scales : KWSmallAdaptiveConnectorScales polygon neighborhood.scale)
    (hM : 2 ≤ M)
    {eps : ℝ} (heps : 0 < eps ∧ eps < 1 / 2)
    (hepsBeta : eps ≤ scales.beta) (hepsAlpha : ∀ i, eps ≤ scales.alpha i)
    (hcross : ∀ i : Fin n, kwComplexCross (polygon.edgeVector i)
      (polygon.edgeVector (i + 1)) ≠ 0)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    (i j : Fin n) (ei ej : Bool) (q : Fin M)
    (hnon : KWEdgesNonincident
      (kwAdaptiveIdealIndex i (Fin.last M) ei)
      (kwAdaptiveIdealIndex j q.castSucc ej)) :
    let patch := scales.toPatchedData hM
    Disjoint
      (kwRawClosedEdge patch.idealVertex
        (kwAdaptiveIdealIndex i (Fin.last M) ei))
      (patch.idealMiddleClosedEdge j q ej) := by
  dsimp only
  let patch := scales.toPatchedData hM
  by_cases hji : j = i
  · subst j
    cases ei with
    | false =>
        simpa [patch, kwAdaptiveIdealIndex,
          KWAdaptivePatchedData.idealMiddleClosedEdge] using
          patch.idealSecondConnector_disjoint_incomingMiddle
            hcross hcoords i q ej
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
          have hsep := patch.idealConnector_disjoint_incomingMiddle_of_notLastOdd
            hcross hcoords i q ej hnot
          simpa [patch, kwAdaptiveIdealIndex,
            KWAdaptivePatchedData.idealMiddleClosedEdge] using
            hsep.mono_left Set.subset_union_left
  · by_cases hjv : j = i + 1
    · subst j
      cases ei with
      | true =>
          simpa [patch, kwAdaptiveIdealIndex,
            KWAdaptivePatchedData.idealMiddleClosedEdge] using
            patch.idealFirstConnector_disjoint_outgoingMiddle
              hcross hcoords i q ej
      | false =>
          by_cases hex : q = 0 ∧ ej = true
          · rcases hex with ⟨rfl, rfl⟩
            apply (hnon.2.2 ?_).elim
            simp only [kwAdaptiveIdealIndex, Bool.false_eq_true, if_false,
              if_pos]
            exact kwStairOddIndex_last_add_one i
          · have hnot : q ≠ 0 ∨ ej = false := by
              cases ej <;> simp_all
            have hsep := patch.idealConnector_disjoint_outgoingMiddle_of_notFirstEven
              hcross hcoords i q ej hnot
            simpa [patch, kwAdaptiveIdealIndex,
              KWAdaptivePatchedData.idealMiddleClosedEdge] using
              hsep.mono_left Set.subset_union_right
    · exact scales.idealConnector_disjoint_unrelatedMiddle neighborhood hM
        heps hepsBeta hepsAlpha i j hji hjv ei ej q

private theorem KWSmallAdaptiveConnectorScales.idealMiddleMiddle_disjoint
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (neighborhood : KWVertexNeighborhoodData polygon)
    (scales : KWSmallAdaptiveConnectorScales polygon neighborhood.scale)
    (hM : 2 ≤ M)
    {eps : ℝ} (heps : 0 < eps ∧ eps < 1 / 2)
    (hepsBeta : eps ≤ scales.beta) (hepsAlpha : ∀ i, eps ≤ scales.alpha i)
    (i j : Fin n) (ei ej : Bool) (q r : Fin M)
    (hnon : KWEdgesNonincident
      (kwAdaptiveIdealIndex i q.castSucc ei)
      (kwAdaptiveIdealIndex j r.castSucc ej)) :
    let patch := scales.toPatchedData hM
    Disjoint (patch.idealMiddleClosedEdge i q ei)
      (patch.idealMiddleClosedEdge j r ej) := by
  dsimp only
  let patch := scales.toPatchedData hM
  by_cases hij : i = j
  · subst j
    cases ei <;> cases ej
    · apply patch.idealRawClosedEdge_odd_disjoint_odd i q r
      intro hqr
      subst r
      exact hnon.1 rfl
    · exact patch.idealRawClosedEdge_odd_disjoint_even i q r hnon
    · exact patch.idealRawClosedEdge_even_disjoint_odd i q r hnon
    · apply patch.idealRawClosedEdge_even_disjoint_even i q r
      intro hqr
      subst r
      exact hnon.1 rfl
  · exact patch.idealMiddle_disjoint_of_owner_ne heps hepsBeta hepsAlpha
      hij q r ei ej

theorem KWSmallAdaptiveConnectorScales.ideal_nonincident_disjoint
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (neighborhood : KWVertexNeighborhoodData polygon)
    (scales : KWSmallAdaptiveConnectorScales polygon neighborhood.scale)
    (hM : 2 ≤ M)
    (hcross : ∀ i : Fin n, kwComplexCross (polygon.edgeVector i)
      (polygon.edgeVector (i + 1)) ≠ 0)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0) :
    let patch := scales.toPatchedData hM
    ∀ a b : Fin (n * (2 * (M + 1))), KWEdgesNonincident a b →
      Disjoint (kwRawClosedEdge patch.idealVertex a)
        (kwRawClosedEdge patch.idealVertex b) := by
  dsimp only
  obtain ⟨eps, hepsPos, hepsHalf, hepsBeta, hepsAlpha⟩ :=
    exists_common_endpoint_core_trim scales.beta scales.alpha scales.hbeta
      scales.beta_lt_quarter scales.halpha
  have heps : 0 < eps ∧ eps < 1 / 2 := ⟨hepsPos, hepsHalf⟩
  intro a b hnon
  obtain ⟨i, k, rfl | rfl⟩ := kwStairIndex_even_or_odd a
  · by_cases hk : k = Fin.last M
    · subst k
      obtain ⟨j, l, rfl | rfl⟩ := kwStairIndex_even_or_odd b
      · by_cases hl : l = Fin.last M
        · subst l
          by_cases hij : i = j
          · subst j; exact (hnon.1 rfl).elim
          · exact scales.idealConnector_disjoint_of_owner_ne neighborhood hM
              hij true true
        · obtain ⟨r, rfl⟩ := Fin.eq_castSucc_of_ne_last hl
          exact scales.idealConnectorMiddle_disjoint neighborhood hM heps
            hepsBeta hepsAlpha hcross hcoords i j true true r hnon
      · by_cases hl : l = Fin.last M
        · subst l
          by_cases hij : i = j
          · subst j
            exact (hnon.2.2 (kwStairEvenIndex_add_one i (Fin.last M))).elim
          · exact scales.idealConnector_disjoint_of_owner_ne neighborhood hM
              hij true false
        · obtain ⟨r, rfl⟩ := Fin.eq_castSucc_of_ne_last hl
          exact scales.idealConnectorMiddle_disjoint neighborhood hM heps
            hepsBeta hepsAlpha hcross hcoords i j true false r hnon
    · obtain ⟨q, rfl⟩ := Fin.eq_castSucc_of_ne_last hk
      obtain ⟨j, l, rfl | rfl⟩ := kwStairIndex_even_or_odd b
      · by_cases hl : l = Fin.last M
        · subst l
          exact (scales.idealConnectorMiddle_disjoint neighborhood hM heps
            hepsBeta hepsAlpha hcross hcoords j i true true q hnon.symm).symm
        · obtain ⟨r, rfl⟩ := Fin.eq_castSucc_of_ne_last hl
          exact scales.idealMiddleMiddle_disjoint neighborhood hM heps
            hepsBeta hepsAlpha i j true true q r hnon
      · by_cases hl : l = Fin.last M
        · subst l
          exact (scales.idealConnectorMiddle_disjoint neighborhood hM heps
            hepsBeta hepsAlpha hcross hcoords j i false true q hnon.symm).symm
        · obtain ⟨r, rfl⟩ := Fin.eq_castSucc_of_ne_last hl
          exact scales.idealMiddleMiddle_disjoint neighborhood hM heps
            hepsBeta hepsAlpha i j true false q r hnon
  · by_cases hk : k = Fin.last M
    · subst k
      obtain ⟨j, l, rfl | rfl⟩ := kwStairIndex_even_or_odd b
      · by_cases hl : l = Fin.last M
        · subst l
          by_cases hij : i = j
          · subst j
            exact (hnon.2.1 (kwStairEvenIndex_add_one i (Fin.last M)).symm).elim
          · exact scales.idealConnector_disjoint_of_owner_ne neighborhood hM
              hij false true
        · obtain ⟨r, rfl⟩ := Fin.eq_castSucc_of_ne_last hl
          exact scales.idealConnectorMiddle_disjoint neighborhood hM heps
            hepsBeta hepsAlpha hcross hcoords i j false true r hnon
      · by_cases hl : l = Fin.last M
        · subst l
          by_cases hij : i = j
          · subst j; exact (hnon.1 rfl).elim
          · exact scales.idealConnector_disjoint_of_owner_ne neighborhood hM
              hij false false
        · obtain ⟨r, rfl⟩ := Fin.eq_castSucc_of_ne_last hl
          exact scales.idealConnectorMiddle_disjoint neighborhood hM heps
            hepsBeta hepsAlpha hcross hcoords i j false false r hnon
    · obtain ⟨q, rfl⟩ := Fin.eq_castSucc_of_ne_last hk
      obtain ⟨j, l, rfl | rfl⟩ := kwStairIndex_even_or_odd b
      · by_cases hl : l = Fin.last M
        · subst l
          exact (scales.idealConnectorMiddle_disjoint neighborhood hM heps
            hepsBeta hepsAlpha hcross hcoords j i true false q hnon.symm).symm
        · obtain ⟨r, rfl⟩ := Fin.eq_castSucc_of_ne_last hl
          exact scales.idealMiddleMiddle_disjoint neighborhood hM heps
            hepsBeta hepsAlpha i j false true q r hnon
      · by_cases hl : l = Fin.last M
        · subst l
          exact (scales.idealConnectorMiddle_disjoint neighborhood hM heps
            hepsBeta hepsAlpha hcross hcoords j i false false q hnon.symm).symm
        · obtain ⟨r, rfl⟩ := Fin.eq_castSucc_of_ne_last hl
          exact scales.idealMiddleMiddle_disjoint neighborhood hM heps
            hepsBeta hepsAlpha i j false false q r hnon

end StatMech.FrontierA
