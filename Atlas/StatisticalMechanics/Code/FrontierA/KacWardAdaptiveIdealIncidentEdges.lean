/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardAdaptiveIdealIncidentSeparation





namespace StatMech.FrontierA

open Set

theorem KWAdaptivePatchedData.idealConnectorFirst_disjoint_outgoingEven
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j)
      (polygon.edgeVector (j + 1)) ≠ 0)
    (hcoords : ∀ j : Fin n,
      (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0)
    (i : Fin n) (q : Fin M) :
    Disjoint
      (kwRawClosedEdge patch.idealVertex
        (kwStairEvenIndex i (Fin.last M)))
      (kwRawClosedEdge patch.idealVertex
        (kwStairEvenIndex (i + 1) q.castSucc)) := by
  exact (patch.idealConnectorFirstClosedEdge_disjoint_outgoingPortTail
    hcross hcoords i).mono_right
      (patch.idealRawClosedEdge_even_subset_outgoingPortTail (i + 1) q)

theorem KWAdaptivePatchedData.idealConnectorFirst_disjoint_outgoingOdd
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j)
      (polygon.edgeVector (j + 1)) ≠ 0)
    (hcoords : ∀ j : Fin n,
      (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0)
    (i : Fin n) (q : Fin M) :
    Disjoint
      (kwRawClosedEdge patch.idealVertex
        (kwStairEvenIndex i (Fin.last M)))
      (kwRawClosedEdge patch.idealVertex
        (kwStairOddIndex (i + 1) q.castSucc)) := by
  exact (patch.idealConnectorFirstClosedEdge_disjoint_outgoingPortTail
    hcross hcoords i).mono_right (fun _ hz ↦ Or.inr
      (patch.idealRawClosedEdge_odd_subset_outgoingTail (i + 1) q hz))

theorem KWAdaptivePatchedData.idealConnectorSecond_disjoint_incomingEven
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j)
      (polygon.edgeVector (j + 1)) ≠ 0)
    (hcoords : ∀ j : Fin n,
      (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0)
    (i : Fin n) (q : Fin M) :
    Disjoint
      (kwRawClosedEdge patch.idealVertex
        (kwStairOddIndex i (Fin.last M)))
      (kwRawClosedEdge patch.idealVertex
        (kwStairEvenIndex i q.castSucc)) := by
  exact (patch.idealConnectorSecondClosedEdge_disjoint_incomingPortTail
    hcross hcoords i).mono_right (fun _ hz ↦ Or.inr
      (patch.idealRawClosedEdge_even_subset_incomingTail i q hz))

theorem KWAdaptivePatchedData.idealConnectorSecond_disjoint_incomingOdd
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j)
      (polygon.edgeVector (j + 1)) ≠ 0)
    (hcoords : ∀ j : Fin n,
      (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0)
    (i : Fin n) (q : Fin M) :
    Disjoint
      (kwRawClosedEdge patch.idealVertex
        (kwStairOddIndex i (Fin.last M)))
      (kwRawClosedEdge patch.idealVertex
        (kwStairOddIndex i q.castSucc)) := by
  exact (patch.idealConnectorSecondClosedEdge_disjoint_incomingPortTail
    hcross hcoords i).mono_right
      (patch.idealRawClosedEdge_odd_subset_incomingPortTail i q)

theorem KWAdaptivePatchedData.idealConnectorFirst_disjoint_incomingEven
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j)
      (polygon.edgeVector (j + 1)) ≠ 0)
    (hcoords : ∀ j : Fin n,
      (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0)
    (i : Fin n) (q : Fin M) :
    Disjoint
      (kwRawClosedEdge patch.idealVertex
        (kwStairEvenIndex i (Fin.last M)))
      (kwRawClosedEdge patch.idealVertex
        (kwStairEvenIndex i q.castSucc)) := by
  exact (patch.idealConnectorClosedEdges_disjoint_incidentTails
    hcross hcoords i).mono
      (fun _ hz ↦ Or.inl hz)
      (fun _ hz ↦ Or.inl
        (patch.idealRawClosedEdge_even_subset_incomingTail i q hz))

theorem KWAdaptivePatchedData.idealConnectorFirst_disjoint_incomingOdd
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j)
      (polygon.edgeVector (j + 1)) ≠ 0)
    (hcoords : ∀ j : Fin n,
      (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0)
    (i : Fin n) (q : Fin M) (hq : q ≠ patch.lastMiddleIndex) :
    Disjoint
      (kwRawClosedEdge patch.idealVertex
        (kwStairEvenIndex i (Fin.last M)))
      (kwRawClosedEdge patch.idealVertex
        (kwStairOddIndex i q.castSucc)) := by
  exact (patch.idealConnectorClosedEdges_disjoint_incidentTails
    hcross hcoords i).mono
      (fun _ hz ↦ Or.inl hz)
      (fun _ hz ↦ Or.inl
        (patch.idealRawClosedEdge_odd_subset_incomingTail i q hq hz))

theorem KWAdaptivePatchedData.idealConnectorSecond_disjoint_outgoingEven
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j)
      (polygon.edgeVector (j + 1)) ≠ 0)
    (hcoords : ∀ j : Fin n,
      (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0)
    (i : Fin n) (q : Fin M) (hq : q ≠ 0) :
    Disjoint
      (kwRawClosedEdge patch.idealVertex
        (kwStairOddIndex i (Fin.last M)))
      (kwRawClosedEdge patch.idealVertex
        (kwStairEvenIndex (i + 1) q.castSucc)) := by
  exact (patch.idealConnectorClosedEdges_disjoint_incidentTails
    hcross hcoords i).mono
      (fun _ hz ↦ Or.inr hz)
      (fun _ hz ↦ Or.inr
        (patch.idealRawClosedEdge_even_subset_outgoingTail (i + 1) q hq hz))

theorem KWAdaptivePatchedData.idealConnectorSecond_disjoint_outgoingOdd
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j)
      (polygon.edgeVector (j + 1)) ≠ 0)
    (hcoords : ∀ j : Fin n,
      (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0)
    (i : Fin n) (q : Fin M) :
    Disjoint
      (kwRawClosedEdge patch.idealVertex
        (kwStairOddIndex i (Fin.last M)))
      (kwRawClosedEdge patch.idealVertex
        (kwStairOddIndex (i + 1) q.castSucc)) := by
  exact (patch.idealConnectorClosedEdges_disjoint_incidentTails
    hcross hcoords i).mono
      (fun _ hz ↦ Or.inr hz)
      (fun _ hz ↦ Or.inr
        (patch.idealRawClosedEdge_odd_subset_outgoingTail (i + 1) q hz))

end StatMech.FrontierA
