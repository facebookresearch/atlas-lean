/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardStaircaseAssembly
import Code.FrontierA.KacWardPolygonPerturbation









namespace StatMech.FrontierA

open scoped NNReal Convex

theorem kwStairParameterDelta_pos
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (i : Fin n) (k : Fin S) :
    0 < data.parameter i k.succ - data.parameter i k.castSucc := by
  exact sub_pos.mpr (data.parameter_strict i k)

theorem kwStairRawEdge_even
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (i : Fin n) (k : Fin S) :
    kwRawEdge data.vertex (kwStairEvenIndex i k) =
      (data.parameter i k.succ - data.parameter i k.castSucc) *
        kwHorizontalPart (polygon.edgeVector i) := by
  unfold kwRawEdge
  rw [kwStairEvenIndex_add_one, data.vertex_odd, data.vertex_even]
  exact data.corner_sub_base i k

theorem kwStairRawEdge_odd_castSucc
    {n M : ℕ} [NeZero n]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := M + 1) polygon)
    (i : Fin n) (k : Fin M) :
    kwRawEdge data.vertex (kwStairOddIndex i k.castSucc) =
      (data.parameter i k.castSucc.succ -
          data.parameter i k.castSucc.castSucc) *
        kwVerticalPart (polygon.edgeVector i) := by
  unfold kwRawEdge
  rw [data.vertex_odd_castSucc_succ, data.vertex_odd]
  exact data.base_succ_sub_corner i k.castSucc

theorem kwStairRawEdge_odd_last
    {n M : ℕ} [NeZero n]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := M + 1) polygon)
    (i : Fin n) :
    kwRawEdge data.vertex (kwStairOddIndex i (Fin.last M)) =
      (data.parameter i (Fin.last M).succ -
          data.parameter i (Fin.last M).castSucc) *
        kwVerticalPart (polygon.edgeVector i) := by
  unfold kwRawEdge
  rw [data.vertex_odd_last_succ, data.vertex_odd]
  rw [← data.base_last i]
  exact data.base_succ_sub_corner i (Fin.last M)

theorem kwStairIndex_even_or_odd
    {n S : ℕ} [NeZero n] [NeZero S]
    (j : Fin (n * (2 * S))) :
    ∃ i : Fin n, ∃ k : Fin S,
      j = kwStairEvenIndex i k ∨ j = kwStairOddIndex i k := by
  let p := finProdFinEquiv.symm j
  rcases kwStairLocal_even_or_odd p.2 with ⟨k, heven | hodd⟩
  · refine ⟨p.1, k, Or.inl ?_⟩
    rw [← finProdFinEquiv.apply_symm_apply j]
    exact congrArg finProdFinEquiv (Prod.ext rfl heven)
  · refine ⟨p.1, k, Or.inr ?_⟩
    rw [← finProdFinEquiv.apply_symm_apply j]
    exact congrArg finProdFinEquiv (Prod.ext rfl hodd)

private theorem kwCross_scaled_horizontal_vertical_ne_zero
    {z : ℂ} {a b : ℝ} (hx : z.re ≠ 0) (hy : z.im ≠ 0)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    kwComplexCross (a * kwHorizontalPart z)
      (b * kwVerticalPart z) ≠ 0 := by
  unfold kwComplexCross kwHorizontalPart kwVerticalPart
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  norm_num
  exact ⟨⟨ha, hx⟩, hb, hy⟩

private theorem kwCross_scaled_vertical_horizontal_ne_zero
    {z w : ℂ} {a b : ℝ} (hy : z.im ≠ 0) (hu : w.re ≠ 0)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    kwComplexCross (a * kwVerticalPart z)
      (b * kwHorizontalPart w) ≠ 0 := by
  unfold kwComplexCross kwHorizontalPart kwVerticalPart
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  norm_num
  exact ⟨⟨ha, hy⟩, hb, hu⟩

theorem kwStairCross_even_ne_zero
    {n M : ℕ} [NeZero n]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := M + 1) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    (i : Fin n) (k : Fin (M + 1)) :
    kwComplexCross (kwRawEdge data.vertex (kwStairEvenIndex i k))
      (kwRawEdge data.vertex (kwStairEvenIndex i k + 1)) ≠ 0 := by
  rw [kwStairEvenIndex_add_one, kwStairRawEdge_even data]
  refine Fin.lastCases ?_ (fun q ↦ ?_) k
  · rw [kwStairRawEdge_odd_last data]
    simpa only [Complex.ofReal_sub] using
      kwCross_scaled_horizontal_vertical_ne_zero
        (z := polygon.edgeVector i)
        (a := data.parameter i (Fin.last M).succ -
          data.parameter i (Fin.last M).castSucc)
        (b := data.parameter i (Fin.last M).succ -
          data.parameter i (Fin.last M).castSucc)
        (hcoords i).1 (hcoords i).2
        (ne_of_gt (kwStairParameterDelta_pos data i (Fin.last M)))
        (ne_of_gt (kwStairParameterDelta_pos data i (Fin.last M)))
  · rw [kwStairRawEdge_odd_castSucc data]
    simpa only [Complex.ofReal_sub] using
      kwCross_scaled_horizontal_vertical_ne_zero
        (z := polygon.edgeVector i)
        (a := data.parameter i q.castSucc.succ -
          data.parameter i q.castSucc.castSucc)
        (b := data.parameter i q.castSucc.succ -
          data.parameter i q.castSucc.castSucc)
        (hcoords i).1 (hcoords i).2
        (ne_of_gt (kwStairParameterDelta_pos data i q.castSucc))
        (ne_of_gt (kwStairParameterDelta_pos data i q.castSucc))

theorem kwStairCross_odd_castSucc_ne_zero
    {n M : ℕ} [NeZero n]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := M + 1) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    (i : Fin n) (k : Fin M) :
    kwComplexCross (kwRawEdge data.vertex (kwStairOddIndex i k.castSucc))
      (kwRawEdge data.vertex (kwStairOddIndex i k.castSucc + 1)) ≠ 0 := by
  rw [kwStairRawEdge_odd_castSucc data,
    kwStairOddIndex_castSucc_add_one, kwStairRawEdge_even data]
  simpa only [Complex.ofReal_sub] using
    kwCross_scaled_vertical_horizontal_ne_zero
      (z := polygon.edgeVector i) (w := polygon.edgeVector i)
      (a := data.parameter i k.castSucc.succ -
        data.parameter i k.castSucc.castSucc)
      (b := data.parameter i k.succ.succ -
        data.parameter i k.succ.castSucc)
      (hcoords i).2 (hcoords i).1
      (ne_of_gt (kwStairParameterDelta_pos data i k.castSucc))
      (ne_of_gt (kwStairParameterDelta_pos data i k.succ))

theorem kwStairCross_odd_last_ne_zero
    {n M : ℕ} [NeZero n]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := M + 1) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    (i : Fin n) :
    kwComplexCross (kwRawEdge data.vertex (kwStairOddIndex i (Fin.last M)))
      (kwRawEdge data.vertex (kwStairOddIndex i (Fin.last M) + 1)) ≠ 0 := by
  rw [kwStairRawEdge_odd_last data,
    kwStairOddIndex_last_add_one, kwStairRawEdge_even data]
  simpa only [Complex.ofReal_sub] using
    kwCross_scaled_vertical_horizontal_ne_zero
      (z := polygon.edgeVector i) (w := polygon.edgeVector (i + 1))
      (a := data.parameter i (Fin.last M).succ -
        data.parameter i (Fin.last M).castSucc)
      (b := data.parameter (i + 1) (0 : Fin (M + 1)).succ -
        data.parameter (i + 1) (0 : Fin (M + 1)).castSucc)
      (hcoords i).2 (hcoords (i + 1)).1
      (ne_of_gt (kwStairParameterDelta_pos data i (Fin.last M)))
      (ne_of_gt (kwStairParameterDelta_pos data (i + 1) 0))



theorem KWStairParameterData.cross_ne_zero
    {n M : ℕ} [NeZero n]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := M + 1) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0) :
    ∀ j : Fin (n * (2 * (M + 1))),
      kwComplexCross (kwRawEdge data.vertex j)
        (kwRawEdge data.vertex (j + 1)) ≠ 0 := by
  intro j
  obtain ⟨i, k, rfl | rfl⟩ := kwStairIndex_even_or_odd j
  · exact kwStairCross_even_ne_zero data hcoords i k
  · refine Fin.lastCases ?_ (fun q ↦ ?_) k
    · exact kwStairCross_odd_last_ne_zero data hcoords i
    · exact kwStairCross_odd_castSucc_ne_zero data hcoords i q



theorem KWStairParameterData.vertex_injective_of_pairwiseLocal
    {n M : ℕ} [NeZero n]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := M + 1) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    (hpair : ∀ i j : Fin n, i ≠ j →
      Disjoint (Set.range (data.localVertex i))
        (Set.range (data.localVertex j))) :
    Function.Injective data.vertex := by
  intro x y hxy
  let p := finProdFinEquiv.symm x
  let q := finProdFinEquiv.symm y
  have hlocal : data.localVertex p.1 p.2 = data.localVertex q.1 q.2 := hxy
  have hpq : p = q := by
    by_cases hi : p.1 = q.1
    · have hl : p.2 = q.2 := by
        rw [hi] at hlocal
        exact data.localVertex_injective hcoords q.1 hlocal
      exact Prod.ext hi hl
    · exfalso
      exact Set.disjoint_left.mp (hpair p.1 q.1 hi)
        ⟨p.2, rfl⟩ ⟨q.2, hlocal.symm⟩
  exact finProdFinEquiv.symm.injective hpq




theorem KWStairParameterData.rawSimplePolygonData
    {n M : ℕ} [NeZero n]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := M + 1) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    (hpair : ∀ i j : Fin n, i ≠ j →
      Disjoint (Set.range (data.localVertex i))
        (Set.range (data.localVertex j)))
    (hedges : ∀ i j : Fin (n * (2 * (M + 1))),
      KWEdgesNonincident i j →
      Disjoint (kwRawClosedEdge data.vertex i)
        (kwRawClosedEdge data.vertex j)) :
    KWRawSimplePolygonData data.vertex where
  three_le := by
    calc
      3 ≤ n := polygon.three_le
      _ = n * 1 := by omega
      _ ≤ n * (2 * (M + 1)) :=
        Nat.mul_le_mul_left n (by omega)
  vertex_injective := data.vertex_injective_of_pairwiseLocal hcoords hpair
  cross_ne_zero := data.cross_ne_zero hcoords
  nonincident_disjoint := hedges

theorem KWStairParameterData.localVertex_range_subset_closedEdgeTube
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (r : ℝ≥0) (hr : 0 < r) (hfine : data.MeshWithin r)
    (i : Fin n) :
    Set.range (data.localVertex i) ⊆ polygon.closedEdgeTube r i := by
  rintro z ⟨l, rfl⟩
  exact data.localVertex_mem_closedEdgeTube r hr hfine i l



theorem KWStairParameterData.localVertex_ranges_disjoint_of_nonincident
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (r : ℝ≥0) (hr : 0 < r) (hfine : data.MeshWithin r)
    (htubes : ∀ i j : Fin n, KWEdgesNonincident i j →
      Disjoint (polygon.closedEdgeTube r i)
        (polygon.closedEdgeTube r j))
    {i j : Fin n} (hij : KWEdgesNonincident i j) :
    Disjoint (Set.range (data.localVertex i))
      (Set.range (data.localVertex j)) := by
  exact (htubes i j hij).mono
    (data.localVertex_range_subset_closedEdgeTube r hr hfine i)
    (data.localVertex_range_subset_closedEdgeTube r hr hfine j)

theorem KWStairParameterData.rawClosedEdge_even_subset_closedEdgeTube
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (r : ℝ≥0) (hr : 0 < r) (hfine : data.MeshWithin r)
    (i : Fin n) (k : Fin S) :
    kwRawClosedEdge data.vertex (kwStairEvenIndex i k) ⊆
      polygon.closedEdgeTube r i := by
  unfold kwRawClosedEdge
  apply (polygon.closedEdgeTube_convex r i).segment_subset
  · rw [data.vertex_even]
    exact polygon.closedEdge_subset_closedEdgeTube hr i
      (data.base_mem_closedEdge i k.castSucc)
  · rw [kwStairEvenIndex_add_one, data.vertex_odd]
    exact data.corner_mem_closedEdgeTube r hfine i k

theorem KWStairParameterData.rawClosedEdge_odd_castSucc_subset_closedEdgeTube
    {n M : ℕ} [NeZero n]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := M + 1) polygon)
    (r : ℝ≥0) (hr : 0 < r) (hfine : data.MeshWithin r)
    (i : Fin n) (k : Fin M) :
    kwRawClosedEdge data.vertex (kwStairOddIndex i k.castSucc) ⊆
      polygon.closedEdgeTube r i := by
  unfold kwRawClosedEdge
  apply (polygon.closedEdgeTube_convex r i).segment_subset
  · rw [data.vertex_odd]
    exact data.corner_mem_closedEdgeTube r hfine i k.castSucc
  · rw [kwStairOddIndex_castSucc_add_one, data.vertex_even]
    exact polygon.closedEdge_subset_closedEdgeTube hr i
      (data.base_mem_closedEdge i k.succ.castSucc)

theorem KWStairParameterData.rawClosedEdge_odd_last_subset_closedEdgeTube
    {n M : ℕ} [NeZero n]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := M + 1) polygon)
    (r : ℝ≥0) (hr : 0 < r) (hfine : data.MeshWithin r)
    (i : Fin n) :
    kwRawClosedEdge data.vertex (kwStairOddIndex i (Fin.last M)) ⊆
      polygon.closedEdgeTube r i := by
  unfold kwRawClosedEdge
  apply (polygon.closedEdgeTube_convex r i).segment_subset
  · rw [data.vertex_odd]
    exact data.corner_mem_closedEdgeTube r hfine i (Fin.last M)
  · rw [data.vertex_odd_last_succ]
    exact polygon.closedEdge_subset_closedEdgeTube hr i
      (right_mem_segment ℝ (polygon.vertex i) (polygon.vertex (i + 1)))


theorem KWStairParameterData.rawClosedEdge_subset_ownerTube
    {n M : ℕ} [NeZero n]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := M + 1) polygon)
    (r : ℝ≥0) (hr : 0 < r) (hfine : data.MeshWithin r)
    (j : Fin (n * (2 * (M + 1)))) :
    ∃ i : Fin n, kwRawClosedEdge data.vertex j ⊆
      polygon.closedEdgeTube r i := by
  obtain ⟨i, k, rfl | rfl⟩ := kwStairIndex_even_or_odd j
  · exact ⟨i, data.rawClosedEdge_even_subset_closedEdgeTube
      r hr hfine i k⟩
  · refine Fin.lastCases ?_ (fun q ↦ ?_) k
    · exact ⟨i, data.rawClosedEdge_odd_last_subset_closedEdgeTube
        r hr hfine i⟩
    · exact ⟨i, data.rawClosedEdge_odd_castSucc_subset_closedEdgeTube
        r hr hfine i q⟩

end StatMech.FrontierA
