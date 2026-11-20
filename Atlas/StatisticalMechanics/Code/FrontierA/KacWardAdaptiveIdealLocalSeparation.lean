/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardAdaptiveIdealIncidentSeparation
import Code.FrontierA.KacWardAdaptiveIdealMiddleGeometry





namespace StatMech.FrontierA

open Set

private theorem KWAdaptivePatchedData.idealMiddle_subset_outgoingPortTail
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) (even : Bool) :
    patch.idealMiddleClosedEdge i q even ⊆
      ({polygon.vertex i + patch.beta * polygon.edgeVector i} ∪
        kwTranslatedOpenRayTail (polygon.vertex i)
          (patch.beta * polygon.edgeVector i)) := by
  intro z hz
  obtain ⟨w, hw, rfl⟩ :=
    patch.idealMiddleClosedEdge_subset_outgoingPortRay i q even hz
  rcases hw with rfl | ⟨t, ht, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨t, ht, rfl⟩

private theorem KWAdaptivePatchedData.idealMiddle_subset_incomingPortTail
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) (even : Bool) :
    patch.idealMiddleClosedEdge i q even ⊆
      ({polygon.vertex (i + 1) +
          patch.alpha (i + 1) * (-polygon.edgeVector i)} ∪
        kwTranslatedOpenRayTail (polygon.vertex (i + 1))
          (patch.alpha (i + 1) * (-polygon.edgeVector i))) := by
  intro z hz
  obtain ⟨w, hw, rfl⟩ :=
    patch.idealMiddleClosedEdge_subset_incomingPortRay i q even hz
  rcases hw with rfl | ⟨t, ht, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨t, ht, rfl⟩

private theorem KWAdaptivePatchedData.idealMiddle_subset_outgoingTail
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) (even : Bool)
    (hnotFirst : q ≠ 0 ∨ even = false) :
    patch.idealMiddleClosedEdge i q even ⊆
      kwTranslatedOpenRayTail (polygon.vertex i)
        (patch.beta * polygon.edgeVector i) := by
  intro z hz
  obtain ⟨w, ⟨t, ht, rfl⟩, rfl⟩ :=
    patch.idealMiddleClosedEdge_subset_outgoingRay i q even hnotFirst hz
  exact ⟨t, ht, rfl⟩

private theorem KWAdaptivePatchedData.idealMiddle_subset_incomingTail
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) (even : Bool)
    (hnotLast : q ≠ patch.lastMiddleIndex ∨ even = true) :
    patch.idealMiddleClosedEdge i q even ⊆
      kwTranslatedOpenRayTail (polygon.vertex (i + 1))
        (patch.alpha (i + 1) * (-polygon.edgeVector i)) := by
  intro z hz
  obtain ⟨w, ⟨t, ht, rfl⟩, rfl⟩ :=
    patch.idealMiddleClosedEdge_subset_incomingRay i q even hnotLast hz
  exact ⟨t, ht, rfl⟩

theorem KWAdaptivePatchedData.idealFirstConnector_disjoint_outgoingMiddle
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j)
      (polygon.edgeVector (j + 1)) ≠ 0)
    (hcoords : ∀ j : Fin n,
      (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0)
    (i : Fin n) (q : Fin M) (even : Bool) :
    Disjoint
      (kwRawClosedEdge patch.idealVertex (kwStairEvenIndex i (Fin.last M)))
      (patch.idealMiddleClosedEdge (i + 1) q even) := by
  apply (patch.idealConnectorFirstClosedEdge_disjoint_outgoingPortTail
    hcross hcoords i).mono_right
  exact patch.idealMiddle_subset_outgoingPortTail (i + 1) q even

theorem KWAdaptivePatchedData.idealSecondConnector_disjoint_incomingMiddle
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j)
      (polygon.edgeVector (j + 1)) ≠ 0)
    (hcoords : ∀ j : Fin n,
      (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0)
    (i : Fin n) (q : Fin M) (even : Bool) :
    Disjoint
      (kwRawClosedEdge patch.idealVertex (kwStairOddIndex i (Fin.last M)))
      (patch.idealMiddleClosedEdge i q even) := by
  apply (patch.idealConnectorSecondClosedEdge_disjoint_incomingPortTail
    hcross hcoords i).mono_right
  exact patch.idealMiddle_subset_incomingPortTail i q even

theorem KWAdaptivePatchedData.idealConnector_disjoint_incomingMiddle_of_notLastOdd
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j)
      (polygon.edgeVector (j + 1)) ≠ 0)
    (hcoords : ∀ j : Fin n,
      (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0)
    (i : Fin n) (q : Fin M) (even : Bool)
    (hnotLast : q ≠ patch.lastMiddleIndex ∨ even = true) :
    Disjoint
      (kwRawClosedEdge patch.idealVertex (kwStairEvenIndex i (Fin.last M)) ∪
        kwRawClosedEdge patch.idealVertex (kwStairOddIndex i (Fin.last M)))
      (patch.idealMiddleClosedEdge i q even) := by
  apply (patch.idealConnectorClosedEdges_disjoint_incidentTails
    hcross hcoords i).mono_right
  exact (patch.idealMiddle_subset_incomingTail i q even hnotLast).trans
    Set.subset_union_left

theorem KWAdaptivePatchedData.idealConnector_disjoint_outgoingMiddle_of_notFirstEven
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j)
      (polygon.edgeVector (j + 1)) ≠ 0)
    (hcoords : ∀ j : Fin n,
      (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0)
    (i : Fin n) (q : Fin M) (even : Bool)
    (hnotFirst : q ≠ 0 ∨ even = false) :
    Disjoint
      (kwRawClosedEdge patch.idealVertex (kwStairEvenIndex i (Fin.last M)) ∪
        kwRawClosedEdge patch.idealVertex (kwStairOddIndex i (Fin.last M)))
      (patch.idealMiddleClosedEdge (i + 1) q even) := by
  apply (patch.idealConnectorClosedEdges_disjoint_incidentTails
    hcross hcoords i).mono_right
  exact (patch.idealMiddle_subset_outgoingTail (i + 1) q even hnotFirst).trans
    Set.subset_union_right

end StatMech.FrontierA
