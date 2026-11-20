/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardStaircaseEndpointPatch
import Code.FrontierA.KacWardCoreTubes









namespace StatMech.FrontierA

open scoped NNReal Convex
open Set

def KWEndpointInteriorMeshWithin
    {n M : ℕ} [NeZero n]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := M + 2) polygon) (r : ℝ≥0) : Prop :=
  ∀ i : Fin n, ∀ k : Fin (M + 2), k ≠ 0 → k ≠ Fin.last (M + 1) →
    (data.parameter i k.succ - data.parameter i k.castSucc) *
      ‖polygon.edgeVector i‖ < r

theorem KWStairParameterData.base_mem_closedEdgeCore
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    {eps : ℝ} (i : Fin n) (k : Fin (S + 1))
    (hk : data.parameter i k ∈ Icc eps (1 - eps)) :
    data.base i k ∈ polygon.closedEdgeCore eps i := by
  exact ⟨data.parameter i k, hk, rfl⟩

theorem KWStairParameterData.base_mem_closedEdgeCoreTube
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    {eps : ℝ} (r : ℝ≥0) (hr : 0 < r)
    (i : Fin n) (k : Fin (S + 1))
    (hk : data.parameter i k ∈ Icc eps (1 - eps)) :
    data.base i k ∈ polygon.closedEdgeCoreTube eps r i := by
  exact ⟨data.base i k, data.base_mem_closedEdgeCore i k hk,
    by simpa only [dist_self, NNReal.coe_pos] using hr⟩

theorem KWStairParameterData.corner_mem_closedEdgeCoreTube
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    {eps : ℝ} (r : ℝ≥0) (hfine : data.MeshWithin r)
    (i : Fin n) (k : Fin S)
    (hk : data.parameter i k.castSucc ∈ Icc eps (1 - eps)) :
    data.corner i k ∈ polygon.closedEdgeCoreTube eps r i := by
  refine ⟨data.base i k.castSucc,
    data.base_mem_closedEdgeCore i k.castSucc hk, ?_⟩
  rw [dist_eq_norm, data.corner_sub_base, norm_mul,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hdelta : 0 < data.parameter i k.succ -
      data.parameter i k.castSucc := sub_pos.mpr (data.parameter_strict i k)
  rw [abs_of_pos hdelta]
  exact (mul_le_mul_of_nonneg_left
      (norm_kwHorizontalPart_le (polygon.edgeVector i)) hdelta.le).trans_lt
    (hfine i k)

theorem KWStairParameterData.corner_mem_closedEdgeCoreTube_of_step
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    {eps : ℝ} (r : ℝ≥0)
    (i : Fin n) (k : Fin S)
    (hk : data.parameter i k.castSucc ∈ Icc eps (1 - eps))
    (hstep : (data.parameter i k.succ - data.parameter i k.castSucc) *
      ‖polygon.edgeVector i‖ < r) :
    data.corner i k ∈ polygon.closedEdgeCoreTube eps r i := by
  refine ⟨data.base i k.castSucc,
    data.base_mem_closedEdgeCore i k.castSucc hk, ?_⟩
  rw [dist_eq_norm, data.corner_sub_base, norm_mul,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hdelta : 0 < data.parameter i k.succ -
      data.parameter i k.castSucc := sub_pos.mpr (data.parameter_strict i k)
  rw [abs_of_pos hdelta]
  exact (mul_le_mul_of_nonneg_left
      (norm_kwHorizontalPart_le (polygon.edgeVector i)) hdelta.le).trans_lt hstep

theorem KWStairParameterData.rawClosedEdge_even_subset_closedEdgeCoreTube
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    {eps : ℝ} (r : ℝ≥0) (hr : 0 < r) (hfine : data.MeshWithin r)
    (i : Fin n) (k : Fin S)
    (hk : data.parameter i k.castSucc ∈ Icc eps (1 - eps)) :
    kwRawClosedEdge data.vertex (kwStairEvenIndex i k) ⊆
      polygon.closedEdgeCoreTube eps r i := by
  unfold kwRawClosedEdge
  apply (polygon.closedEdgeCoreTube_convex eps r i).segment_subset
  · rw [data.vertex_even]
    exact data.base_mem_closedEdgeCoreTube r hr i k.castSucc hk
  · rw [kwStairEvenIndex_add_one, data.vertex_odd]
    exact data.corner_mem_closedEdgeCoreTube r hfine i k hk

theorem KWStairParameterData.rawClosedEdge_odd_castSucc_subset_closedEdgeCoreTube
    {n M : ℕ} [NeZero n]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := M + 1) polygon)
    {eps : ℝ} (r : ℝ≥0) (hr : 0 < r) (hfine : data.MeshWithin r)
    (i : Fin n) (k : Fin M)
    (hk : data.parameter i k.castSucc.castSucc ∈ Icc eps (1 - eps))
    (hnext : data.parameter i k.castSucc.succ ∈ Icc eps (1 - eps)) :
    kwRawClosedEdge data.vertex (kwStairOddIndex i k.castSucc) ⊆
      polygon.closedEdgeCoreTube eps r i := by
  unfold kwRawClosedEdge
  apply (polygon.closedEdgeCoreTube_convex eps r i).segment_subset
  · rw [data.vertex_odd]
    exact data.corner_mem_closedEdgeCoreTube r hfine i k.castSucc hk
  · rw [kwStairOddIndex_castSucc_add_one, data.vertex_even]
    exact data.base_mem_closedEdgeCoreTube r hr i k.succ.castSucc hnext



theorem KWStairParameterData.parameter_mem_core_of_ne_zero
    {n M : ℕ} [NeZero n]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := M + 1) polygon)
    (beta : ℝ) (incoming : Fin n → ℝ)
    (hfirst : ∀ i : Fin n,
      data.parameter i (0 : Fin (M + 1)).succ = beta)
    (hlast : ∀ i : Fin n,
      data.parameter i (Fin.last M).castSucc = 1 - incoming i)
    {eps : ℝ} (hepsBeta : eps ≤ beta)
    (hepsIncoming : ∀ i, eps ≤ incoming i)
    (i : Fin n) (k : Fin (M + 1)) (hk : k ≠ 0) :
    data.parameter i k.castSucc ∈ Icc eps (1 - eps) := by
  have hfirstIndex : (0 : Fin (M + 1)).succ ≤ k.castSucc := by
    apply Fin.mk_le_mk.mpr
    have hkpos : 0 < k.val := Nat.pos_of_ne_zero (by
      intro hkval
      apply hk
      exact Fin.ext hkval)
    exact hkpos
  have hlastIndex : k.castSucc ≤ (Fin.last M).castSucc := by
    apply Fin.mk_le_mk.mpr
    exact k.le_last
  constructor
  · calc
      eps ≤ beta := hepsBeta
      _ = data.parameter i (0 : Fin (M + 1)).succ := (hfirst i).symm
      _ ≤ data.parameter i k.castSucc :=
        (data.parameter_strictMono i).monotone hfirstIndex
  · calc
      data.parameter i k.castSucc ≤
          data.parameter i (Fin.last M).castSucc :=
        (data.parameter_strictMono i).monotone hlastIndex
      _ = 1 - incoming i := hlast i
      _ ≤ 1 - eps := sub_le_sub_left (hepsIncoming i) 1

theorem kwEndpointParameterData_parameter_mem_core_of_ne_zero
    {n M : ℕ} [NeZero n]
    (polygon : KWFiniteSimplePolygon n)
    (beta : ℝ) (alpha : Fin n → ℝ)
    (hM : 0 < M) (hbeta : 0 < beta)
    (halpha : ∀ i, 0 < alpha i)
    (hsum : ∀ i, alpha i + beta < 1)
    {eps : ℝ} (hepsBeta : eps ≤ beta)
    (hepsAlpha : ∀ i, eps ≤ alpha i)
    (i : Fin n) (k : Fin (M + 2)) (hk : k ≠ 0) :
    let data := kwEndpointParameterData polygon M beta alpha
      hM hbeta halpha hsum
    data.parameter i k.castSucc ∈ Icc eps (1 - eps) := by
  dsimp only
  apply KWStairParameterData.parameter_mem_core_of_ne_zero
    (incoming := fun i ↦ alpha (i + 1))
  · exact fun j ↦ kwEndpointParameterData_parameter_one
      polygon beta alpha hM hbeta halpha hsum j
  · exact fun j ↦ kwEndpointParameterData_parameter_penultimate
      polygon beta alpha hM hbeta halpha hsum j
  · exact hepsBeta
  · exact fun j ↦ hepsAlpha (j + 1)
  · exact hk



theorem exists_common_endpoint_core_trim
    {n : ℕ} [NeZero n]
    (beta : ℝ) (alpha : Fin n → ℝ)
    (hbeta : 0 < beta) (hbetaQuarter : beta < 1 / 4)
    (halpha : ∀ i, 0 < alpha i) :
    ∃ eps : ℝ, 0 < eps ∧ eps < 1 / 2 ∧ eps ≤ beta ∧
      ∀ i, eps ≤ alpha i := by
  classical
  let hne : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty
  let amin : ℝ := Finset.univ.inf' hne alpha
  have hamin : 0 < amin := by
    dsimp only [amin]
    rw [Finset.lt_inf'_iff]
    intro i _
    exact halpha i
  let eps := min beta amin / 2
  have heps : 0 < eps := div_pos (lt_min hbeta hamin) (by norm_num)
  refine ⟨eps, heps, ?_, ?_, ?_⟩
  · have hepsBetaHalf : eps ≤ beta / 2 := by
      exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    linarith
  · exact (div_le_self (le_min hbeta.le hamin.le) (by norm_num)).trans
      (min_le_left _ _)
  · intro i
    have hepsAmin : eps ≤ amin := by
      exact (div_le_self (le_min hbeta.le hamin.le) (by norm_num)).trans
        (min_le_right _ _)
    exact hepsAmin.trans (Finset.inf'_le alpha (Finset.mem_univ i))



theorem KWFiniteSimplePolygon.exists_fixedEndpointParameterData_meshWithin
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (beta : ℝ) (alpha : Fin n → ℝ)
    (hbeta : 0 < beta) (halpha : ∀ i, 0 < alpha i)
    (hsum : ∀ i, alpha i + beta < 1)
    (r : ℝ≥0) (hr : 0 < r)
    (hbetaMesh : ∀ i : Fin n, beta * ‖polygon.edgeVector i‖ < r)
    (halphaMesh : ∀ i : Fin n,
      alpha (i + 1) * ‖polygon.edgeVector i‖ < r) :
    ∃ M : ℕ, ∃ data : KWStairParameterData (S := M + 2) polygon,
      0 < M ∧ data.MeshWithin r := by
  obtain ⟨N, hmesh⟩ := polygon.exists_uniform_stair_mesh r hr
  let M : ℕ := N + 1
  have hM : 0 < M := by simp [M]
  let data := kwEndpointParameterData polygon M beta alpha hM hbeta halpha hsum
  refine ⟨M, data, hM, ?_⟩
  intro i k
  have hstep := kwEndpointParameter_step_le_max M beta (alpha (i + 1))
    hM hbeta.le (halpha (i + 1)).le (hsum (i + 1)) k
  have hcentral : (M : ℝ)⁻¹ * ‖polygon.edgeVector i‖ < r := by
    calc
      (M : ℝ)⁻¹ * ‖polygon.edgeVector i‖ =
          ‖polygon.edgeVector i‖ / (N + 1 : ℝ) := by
        dsimp only [M]
        norm_num [div_eq_mul_inv, mul_comm]
      _ < r := hmesh i
  have hmax : max beta (max (alpha (i + 1)) (M : ℝ)⁻¹) *
      ‖polygon.edgeVector i‖ < r := by
    rw [max_mul_of_nonneg _ _ (norm_nonneg _),
      max_mul_of_nonneg _ _ (norm_nonneg _), max_lt_iff, max_lt_iff]
    exact ⟨hbetaMesh i, halphaMesh i, hcentral⟩
  exact (mul_le_mul_of_nonneg_right hstep (norm_nonneg _)).trans_lt hmax



theorem KWFiniteSimplePolygon.exists_fixedEndpointParameterData_interiorMesh
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (beta : ℝ) (alpha : Fin n → ℝ)
    (hbeta : 0 < beta) (halpha : ∀ i, 0 < alpha i)
    (hsum : ∀ i, alpha i + beta < 1)
    (r : ℝ≥0) (hr : 0 < r) :
    ∃ M : ℕ, ∃ data : KWStairParameterData (S := M + 2) polygon,
      0 < M ∧ KWEndpointInteriorMeshWithin data r := by
  obtain ⟨N, hmesh⟩ := polygon.exists_uniform_stair_mesh r hr
  let M : ℕ := N + 1
  have hM : 0 < M := by simp [M]
  let data := kwEndpointParameterData polygon M beta alpha hM hbeta halpha hsum
  refine ⟨M, data, hM, ?_⟩
  intro i k hk0 hklast
  have hstep := kwEndpointParameter_middle_step_le_inv
    M beta (alpha (i + 1)) hM hbeta.le (halpha (i + 1)).le k hk0 hklast
  calc
    (data.parameter i k.succ - data.parameter i k.castSucc) *
        ‖polygon.edgeVector i‖ ≤
      (M : ℝ)⁻¹ * ‖polygon.edgeVector i‖ :=
        mul_le_mul_of_nonneg_right hstep (norm_nonneg _)
    _ = ‖polygon.edgeVector i‖ / (N + 1 : ℝ) := by
      dsimp only [M]
      norm_num [div_eq_mul_inv, mul_comm]
    _ < r := hmesh i

end StatMech.FrontierA
