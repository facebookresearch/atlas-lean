/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardRawSimpleFromEdges
import Code.FrontierA.KacWardStaircaseCorePlacement
import Code.FrontierA.KacWardVertexEdgeSeparation









namespace StatMech.FrontierA

open scoped NNReal Convex
open Set

def kwStairOwner
    {n S : ℕ} [NeZero n] [NeZero S]
    (j : Fin (n * (2 * S))) : Fin n :=
  (finProdFinEquiv.symm j).1

@[simp] theorem kwStairOwner_even
    {n S : ℕ} [NeZero n] [NeZero S]
    (i : Fin n) (k : Fin S) :
    kwStairOwner (kwStairEvenIndex i k) = i := by
  simp [kwStairOwner, kwStairEvenIndex]

@[simp] theorem kwStairOwner_odd
    {n S : ℕ} [NeZero n] [NeZero S]
    (i : Fin n) (k : Fin S) :
    kwStairOwner (kwStairOddIndex i k) = i := by
  simp [kwStairOwner, kwStairOddIndex]

theorem KWStairParameterData.rawClosedEdge_subset_ownerTube_exact
    {n M : ℕ} [NeZero n]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := M + 1) polygon)
    (r : ℝ≥0) (hr : 0 < r) (hfine : data.MeshWithin r)
    (j : Fin (n * (2 * (M + 1)))) :
    kwRawClosedEdge data.vertex j ⊆
      polygon.closedEdgeTube r (kwStairOwner j) := by
  obtain ⟨i, k, rfl | rfl⟩ := kwStairIndex_even_or_odd j
  · simpa only [kwStairOwner_even] using
      data.rawClosedEdge_even_subset_closedEdgeTube r hr hfine i k
  · refine Fin.lastCases ?_ (fun q ↦ ?_) k
    · simpa only [kwStairOwner_odd] using
        data.rawClosedEdge_odd_last_subset_closedEdgeTube r hr hfine i
    · simpa only [kwStairOwner_odd] using
        data.rawClosedEdge_odd_castSucc_subset_closedEdgeTube r hr hfine i q

theorem KWStairParameterData.rawClosedEdges_disjoint_of_owner_nonincident
    {n M : ℕ} [NeZero n]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := M + 1) polygon)
    (r : ℝ≥0) (hr : 0 < r) (hfine : data.MeshWithin r)
    (htubes : ∀ i j : Fin n, KWEdgesNonincident i j →
      Disjoint (polygon.closedEdgeTube r i)
        (polygon.closedEdgeTube r j))
    (j l : Fin (n * (2 * (M + 1))))
    (howners : KWEdgesNonincident (kwStairOwner j) (kwStairOwner l)) :
    Disjoint (kwRawClosedEdge data.vertex j)
      (kwRawClosedEdge data.vertex l) := by
  exact (htubes (kwStairOwner j) (kwStairOwner l) howners).mono
    (data.rawClosedEdge_subset_ownerTube_exact r hr hfine j)
    (data.rawClosedEdge_subset_ownerTube_exact r hr hfine l)

theorem KWStairParameterData.rawClosedEdges_disjoint_of_sameOwner
    {n M : ℕ} [NeZero n]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := M + 1) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    (j l : Fin (n * (2 * (M + 1))))
    (howner : kwStairOwner j = kwStairOwner l)
    (hnon : KWEdgesNonincident j l) :
    Disjoint (kwRawClosedEdge data.vertex j)
      (kwRawClosedEdge data.vertex l) := by
  apply data.rawClosedEdges_disjoint_sameOwner hcoords (kwStairOwner j) j l
  · rfl
  · exact howner.symm
  · exact hnon

end StatMech.FrontierA
