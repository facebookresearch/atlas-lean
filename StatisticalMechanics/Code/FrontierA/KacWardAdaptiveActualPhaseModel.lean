/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardAdaptiveActualGlobalSeparation
import Code.FrontierA.KacWardAdaptiveIdealPhaseHomotopy
import Code.FrontierA.KacWardAdaptiveSourcePhase
import Code.FrontierA.KacWardAxisRationalNormalization





namespace StatMech.FrontierA

private theorem KWAdaptiveConnectorData.firstVector_axis'
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

private theorem KWAdaptiveConnectorData.secondVector_axis'
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


theorem KWAdaptivePatchedData.rawEdge_axis
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) :
    ∀ j, (kwRawEdge patch.vertex j).re = 0 ∨
      (kwRawEdge patch.vertex j).im = 0 := by
  intro j
  obtain ⟨i, k, rfl | rfl⟩ := kwStairIndex_even_or_odd j
  · refine Fin.lastCases ?_ (fun q ↦ ?_) k
    · rw [patch.rawEdge_even_last]
      have hi : i + 1 - 1 = i := by abel
      simpa only [hi] using (patch.connector (i + 1)).firstVector_axis'
    · rw [patch.rawEdge_even_castSucc]
      by_cases hv : patch.sliceUsesVerticalFirst i q
      · rw [if_pos hv]
        left
        simp [kwVerticalPart]
      · rw [if_neg hv]
        right
        simp [kwHorizontalPart]
  · refine Fin.lastCases ?_ (fun q ↦ ?_) k
    · rw [patch.rawEdge_odd_last]
      exact (patch.connector (i + 1)).secondVector_axis'
    · rw [patch.rawEdge_odd_castSucc]
      by_cases hv : patch.sliceUsesVerticalFirst i q
      · rw [if_pos hv]
        right
        simp [kwHorizontalPart]
      · rw [if_neg hv]
        left
        simp [kwVerticalPart]



theorem KWSmallAdaptiveConnectorScales.exists_actualSimplePhaseModel
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
        actual.vertex = (scales.toPatchedData hM).vertex ∧
        kwVectorPhaseCycle actual.edgeList =
          kwVectorPhaseCycle
            (List.ofFn (kwRawEdge (scales.toPatchedData hM).idealVertex)) := by
  obtain ⟨M, inst, hM, actual, hactual⟩ :=
    scales.exists_actualSimplePolygon_eq_patch neighborhood hcross hcoords
  refine ⟨M, inst, hM, actual, hactual, ?_⟩
  letI : NeZero M := inst
  have hphase :=
    (scales.toPatchedData hM).idealAxisHomotopy_phaseCycle hcoords
  rw [KWFiniteSimplePolygon.edgeList]
  change kwVectorPhaseCycle (List.ofFn (kwRawEdge actual.vertex)) = _
  rw [hactual]
  exact hphase.symm



theorem KWSmallAdaptiveConnectorScales.exists_actualSimpleSourcePhaseModel
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
        actual.vertex = (scales.toPatchedData hM).vertex ∧
        kwVectorPhaseCycle actual.edgeList =
          kwVectorPhaseCycle polygon.edgeList := by
  obtain ⟨M, inst, hM, actual, hactual, hactualIdeal⟩ :=
    scales.exists_actualSimplePhaseModel neighborhood hcross hcoords
  refine ⟨M, inst, hM, actual, hactual, ?_⟩
  letI : NeZero M := inst
  exact hactualIdeal.trans
    ((scales.toPatchedData hM).ideal_phaseCycle_eq_source hcoords hcross)




theorem KWFiniteSimplePolygon.phaseCycle_eq_neg_one_of_generic
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j)
      (polygon.edgeVector (j + 1)) ≠ 0)
    (hcoords : ∀ j : Fin n,
      (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0) :
    kwVectorPhaseCycle polygon.edgeList = -1 := by
  let neighborhood := polygon.exists_vertexNeighborhoodData.some
  let scales := (polygon.exists_smallAdaptiveConnectorScales hcoords
    neighborhood.scale_pos).some
  obtain ⟨M, inst, hM, actual, hactual, hactualPhase⟩ :=
    scales.exists_actualSimplePhaseModel neighborhood hcross hcoords
  letI : NeZero M := inst
  let patch := scales.toPatchedData hM
  have haxis : ∀ i, (actual.edgeVector i).re = 0 ∨
      (actual.edgeVector i).im = 0 := by
    intro i
    rw [KWFiniteSimplePolygon.edgeVector, hactual]
    exact patch.rawEdge_axis i
  have hturn : ∀ i, KWRawTurnAdmissible actual.vertex i := by
    intro i
    rw [hactual]
    exact patch.turnAdmissible hcoords i
  have hactualSign := actual.axis_phaseCycle_eq_neg_one haxis hturn
  have hidealSource := patch.ideal_phaseCycle_eq_source hcoords hcross
  exact hidealSource.symm.trans (hactualPhase.symm.trans hactualSign)

end StatMech.FrontierA
