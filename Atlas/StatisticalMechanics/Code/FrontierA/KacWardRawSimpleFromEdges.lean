/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardStaircaseSameEdge










namespace StatMech.FrontierA

open scoped Convex
open Set

theorem kwRaw_vertex_injective_of_cross_nonincident
    {n : ℕ} [NeZero n] (vertex : Fin n → ℂ)
    (hcross : ∀ i : Fin n,
      kwComplexCross (kwRawEdge vertex i)
        (kwRawEdge vertex (i + 1)) ≠ 0)
    (hedges : ∀ i j : Fin n, KWEdgesNonincident i j →
      Disjoint (kwRawClosedEdge vertex i) (kwRawClosedEdge vertex j)) :
    Function.Injective vertex := by
  intro i j hij
  by_contra hne
  by_cases hprev : i = j + 1
  · have hedge : kwRawEdge vertex j = 0 := by
      unfold kwRawEdge
      rw [← hprev, hij]
      exact sub_self _
    apply hcross j
    rw [hedge]
    simp [kwComplexCross]
  by_cases hnext : i + 1 = j
  · have hedge : kwRawEdge vertex i = 0 := by
      unfold kwRawEdge
      rw [hnext, hij]
      exact sub_self _
    apply hcross i
    rw [hedge]
    simp [kwComplexCross]
  have hnon : KWEdgesNonincident i j := ⟨hne, hprev, hnext⟩
  apply Set.disjoint_left.mp (hedges i j hnon)
  · exact left_mem_segment ℝ _ _
  · rw [kwRawClosedEdge, ← hij]
    exact left_mem_segment ℝ _ _



theorem KWRawSimplePolygonData.of_cross_nonincident
    {n : ℕ} [NeZero n] (vertex : Fin n → ℂ)
    (hthree : 3 ≤ n)
    (hcross : ∀ i : Fin n,
      kwComplexCross (kwRawEdge vertex i)
        (kwRawEdge vertex (i + 1)) ≠ 0)
    (hedges : ∀ i j : Fin n, KWEdgesNonincident i j →
      Disjoint (kwRawClosedEdge vertex i) (kwRawClosedEdge vertex j)) :
    KWRawSimplePolygonData vertex where
  three_le := hthree
  vertex_injective :=
    kwRaw_vertex_injective_of_cross_nonincident vertex hcross hedges
  cross_ne_zero := hcross
  nonincident_disjoint := hedges



theorem KWStairParameterData.rawSimplePolygonData_of_nonincident
    {n M : ℕ} [NeZero n]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := M + 1) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    (hedges : ∀ i j : Fin (n * (2 * (M + 1))),
      KWEdgesNonincident i j →
      Disjoint (kwRawClosedEdge data.vertex i)
        (kwRawClosedEdge data.vertex j)) :
    KWRawSimplePolygonData data.vertex := by
  apply KWRawSimplePolygonData.of_cross_nonincident
  · calc
      3 ≤ n := polygon.three_le
      _ = n * 1 := by omega
      _ ≤ n * (2 * (M + 1)) := Nat.mul_le_mul_left n (by omega)
  · exact data.cross_ne_zero hcoords
  · exact hedges

end StatMech.FrontierA
