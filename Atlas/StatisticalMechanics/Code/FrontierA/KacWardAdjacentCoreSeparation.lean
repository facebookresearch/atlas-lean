/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardIncidentStairPatch










namespace StatMech.FrontierA

open scoped NNReal ENNReal
open Set


def KWFiniteSimplePolygon.closedEdgeCore
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (eps : ℝ) (i : Fin n) : Set ℂ :=
  AffineMap.lineMap (polygon.vertex i) (polygon.vertex (i + 1)) ''
    Icc eps (1 - eps)

theorem KWFiniteSimplePolygon.closedEdgeCore_isCompact
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (eps : ℝ) (i : Fin n) :
    IsCompact (polygon.closedEdgeCore eps i) := by
  exact isCompact_Icc.image AffineMap.lineMap_continuous

theorem KWFiniteSimplePolygon.closedEdgeCore_isClosed
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (eps : ℝ) (i : Fin n) :
    IsClosed (polygon.closedEdgeCore eps i) :=
  (polygon.closedEdgeCore_isCompact eps i).isClosed


theorem KWFiniteSimplePolygon.closedEdgeCore_subset_edgeInterior
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    {eps : ℝ} (heps : 0 < eps ∧ eps < 1 / 2) (i : Fin n) :
    polygon.closedEdgeCore eps i ⊆
      {z : ℂ | Sbtw ℝ (polygon.vertex i) z
        (polygon.vertex (i + 1))} := by
  rintro z ⟨t, ht, rfl⟩
  apply sbtw_lineMap_iff.mpr
  refine ⟨polygon.vertex_injective.ne
    (polygon.add_one_ne_self i).symm, ?_, ?_⟩
  · exact heps.1.trans_le ht.1
  · have : 1 - eps < 1 := by linarith
    exact ht.2.trans_lt this



theorem KWFiniteSimplePolygon.closedEdgeCore_disjoint
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    {eps : ℝ} (heps : 0 < eps ∧ eps < 1 / 2)
    {i j : Fin n} (hij : i ≠ j) :
    Disjoint (polygon.closedEdgeCore eps i)
      (polygon.closedEdgeCore eps j) :=
  (polygon.edgeInteriors_disjoint i j hij).mono
    (polygon.closedEdgeCore_subset_edgeInterior heps i)
    (polygon.closedEdgeCore_subset_edgeInterior heps j)


theorem KWFiniteSimplePolygon.exists_closedEdgeCore_separation
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    {eps : ℝ} (heps : 0 < eps ∧ eps < 1 / 2)
    {i j : Fin n} (hij : i ≠ j) :
    ∃ r : ℝ≥0, 0 < r ∧
      ∀ x ∈ polygon.closedEdgeCore eps i,
        ∀ y ∈ polygon.closedEdgeCore eps j,
          (r : ℝ≥0∞) < edist x y := by
  exact Metric.exists_pos_forall_lt_edist
    (polygon.closedEdgeCore_isCompact eps i)
    (polygon.closedEdgeCore_isClosed eps j)
    (polygon.closedEdgeCore_disjoint heps hij)

private theorem exists_uniform_core_radius_finset
    {ι : Type*} (s : Finset ι) (Q : ι → ℝ≥0 → Prop)
    (hQ : ∀ i ∈ s, ∃ r : ℝ≥0, 0 < r ∧ Q i r)
    (hmono : ∀ i ∈ s, ∀ {r r' : ℝ≥0}, r' ≤ r → Q i r → Q i r') :
    ∃ r : ℝ≥0, 0 < r ∧ ∀ i ∈ s, Q i r := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert j s hj ih =>
      obtain ⟨ri, hri, hQi⟩ := hQ j (by simp)
      obtain ⟨rs, hrs, hQs⟩ := ih
        (fun j hj ↦ hQ j (by simp [hj]))
        (fun j hj r r' hle h ↦ hmono j (by simp [hj]) hle h)
      refine ⟨min ri rs, lt_min hri hrs, ?_⟩
      intro l hl
      rcases Finset.mem_insert.mp hl with hEq | hls
      · subst l
        exact hmono _ (by simp) (min_le_left _ _) hQi
      · exact hmono l (by simp [hls]) (min_le_right _ _) (hQs l hls)



theorem KWFiniteSimplePolygon.exists_uniform_closedEdgeCore_separation
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    {eps : ℝ} (heps : 0 < eps ∧ eps < 1 / 2) :
    ∃ r : ℝ≥0, 0 < r ∧
      ∀ i j : Fin n, i ≠ j →
        ∀ x ∈ polygon.closedEdgeCore eps i,
          ∀ y ∈ polygon.closedEdgeCore eps j,
            (r : ℝ≥0∞) < edist x y := by
  classical
  let pairs : Finset (Fin n × Fin n) :=
    Finset.univ.filter (fun p ↦ p.1 ≠ p.2)
  let Q : (Fin n × Fin n) → ℝ≥0 → Prop := fun p r ↦
    ∀ x ∈ polygon.closedEdgeCore eps p.1,
      ∀ y ∈ polygon.closedEdgeCore eps p.2,
        (r : ℝ≥0∞) < edist x y
  have hpair : ∀ p ∈ pairs, ∃ r : ℝ≥0, 0 < r ∧ Q p r := by
    intro p hp
    have hpne : p.1 ≠ p.2 := by
      simpa only [pairs, Finset.mem_filter, Finset.mem_univ, true_and] using hp
    exact polygon.exists_closedEdgeCore_separation heps hpne
  have hmono : ∀ p ∈ pairs, ∀ {r r' : ℝ≥0},
      r' ≤ r → Q p r → Q p r' := by
    intro p _ r r' hle h x hx y hy
    exact (ENNReal.coe_le_coe.mpr hle).trans_lt (h x hx y hy)
  obtain ⟨r, hr, huniform⟩ :=
    exists_uniform_core_radius_finset pairs Q hpair hmono
  refine ⟨r, hr, ?_⟩
  intro i j hij x hx y hy
  exact huniform (i, j) (by simp [pairs, hij]) x hx y hy

end StatMech.FrontierA
