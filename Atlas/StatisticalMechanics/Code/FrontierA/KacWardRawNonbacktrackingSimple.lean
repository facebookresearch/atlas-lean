/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardAdaptiveVertexConnector











namespace StatMech.FrontierA

open scoped Convex
open Set

private theorem fin_add_one_plus_one
    {n : ℕ} [NeZero n] (i : Fin n) :
    i + (1 + 1) = i + 2 := by
  have hone : (1 : Fin n) + 1 = 2 := by
    apply Fin.ext
    change (1 % n + 1 % n) % n = 2 % n
    rw [← Nat.add_mod]
  exact congrArg (fun q : Fin n ↦ i + q) hone

private theorem fin_add_one_add_one
    {n : ℕ} [NeZero n] (i : Fin n) :
    i + 1 + 1 = i + 2 :=
  (add_assoc i 1 1).trans (fin_add_one_plus_one i)


structure KWRawNonbacktrackingSimpleData
    {n : ℕ} [NeZero n] (vertex : Fin n → ℂ) : Prop where
  three_le : 3 ≤ n
  edge_ne_zero : ∀ i : Fin n, kwRawEdge vertex i ≠ 0
  previous_not_between : ∀ i : Fin n,
    ¬Sbtw ℝ (vertex (i + 1)) (vertex i) (vertex (i + 2))
  adjacent_disjoint : ∀ i : Fin n,
    Disjoint
      {z : ℂ | Sbtw ℝ (vertex i) z (vertex (i + 1))}
      {z : ℂ | Sbtw ℝ (vertex (i + 1)) z (vertex (i + 2))}
  nonincident_disjoint : ∀ i j : Fin n, KWEdgesNonincident i j →
    Disjoint (kwRawClosedEdge vertex i) (kwRawClosedEdge vertex j)

theorem KWRawNonbacktrackingSimpleData.vertex_injective
    {n : ℕ} [NeZero n] {vertex : Fin n → ℂ}
    (h : KWRawNonbacktrackingSimpleData vertex) :
    Function.Injective vertex := by
  intro i j hij
  by_contra hne
  by_cases hprev : i = j + 1
  · have hedge : kwRawEdge vertex j = 0 := by
      unfold kwRawEdge
      rw [← hprev, hij]
      exact sub_self _
    exact h.edge_ne_zero j hedge
  by_cases hnext : i + 1 = j
  · have hedge : kwRawEdge vertex i = 0 := by
      unfold kwRawEdge
      rw [hnext, hij]
      exact sub_self _
    exact h.edge_ne_zero i hedge
  have hnon : KWEdgesNonincident i j := ⟨hne, hprev, hnext⟩
  apply Set.disjoint_left.mp (h.nonincident_disjoint i j hnon)
  · exact left_mem_segment ℝ _ _
  · rw [kwRawClosedEdge, ← hij]
    exact left_mem_segment ℝ _ _



noncomputable def KWRawNonbacktrackingSimpleData.toFiniteSimplePolygon
    {n : ℕ} [NeZero n] {vertex : Fin n → ℂ}
    (h : KWRawNonbacktrackingSimpleData vertex) :
    KWFiniteSimplePolygon n where
  vertex := vertex
  three_le := h.three_le
  vertex_injective := h.vertex_injective
  vertex_not_strictly_between := by
    intro i j hji hjs hs
    by_cases hprev : i = j + 1
    · subst i
      exact h.previous_not_between j
        (by simpa only [fin_add_one_plus_one, fin_add_one_add_one] using hs)
    · have hnon : KWEdgesNonincident i j :=
        ⟨hji.symm, hprev, hjs.symm⟩
      apply Set.disjoint_left.mp (h.nonincident_disjoint i j hnon)
      · exact mem_segment_iff_wbtw.mpr hs.1
      · exact left_mem_segment ℝ _ _
  edgeInteriors_disjoint := by
    intro i j hij
    by_cases hnon : KWEdgesNonincident i j
    · exact (h.nonincident_disjoint i j hnon).mono
        (fun _ hz ↦ mem_segment_iff_wbtw.mpr hz.1)
        (fun _ hz ↦ mem_segment_iff_wbtw.mpr hz.1)
    · have hadj : i = j + 1 ∨ i + 1 = j := by
        by_contra hnot
        apply hnon
        refine ⟨hij, ?_, ?_⟩
        · exact (not_or.mp hnot).1
        · exact (not_or.mp hnot).2
      rcases hadj with hprev | hnext
      · subst i
        simpa only [fin_add_one_add_one] using (h.adjacent_disjoint j).symm
      · subst j
        simpa only [fin_add_one_add_one] using h.adjacent_disjoint i

end StatMech.FrontierA
