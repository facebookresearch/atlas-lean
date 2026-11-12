/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardAdaptivePatchedWalk





namespace StatMech.FrontierA

open scoped Convex
open Set



def KWRawTurnAdmissible
    {n : ℕ} [NeZero n] (vertex : Fin n → ℂ) (i : Fin n) : Prop :=
  kwComplexCross (kwRawEdge vertex i) (kwRawEdge vertex (i + 1)) ≠ 0 ∨
    ∃ r : ℝ, 0 < r ∧
      kwRawEdge vertex (i + 1) = r * kwRawEdge vertex i

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

private theorem openSegments_disjoint_of_common_forward
    {A B C : ℂ} (hAB : B - A ≠ 0)
    (hforward : ∃ r : ℝ, 0 < r ∧ C - B = r * (B - A)) :
    Disjoint {z : ℂ | Sbtw ℝ A z B}
      {z : ℂ | Sbtw ℝ B z C} := by
  obtain ⟨r, hr, hBC⟩ := hforward
  rw [Set.disjoint_left]
  intro z hzAB hzBC
  obtain ⟨s, hs, hsEq⟩ := hzAB.mem_image_Ioo
  obtain ⟨t, ht, htEq⟩ := hzBC.mem_image_Ioo
  have heq : (-(1 - s) : ℝ) * (B - A) = (t * r) * (B - A) := by
    calc
      (-(1 - s) : ℝ) * (B - A) =
          AffineMap.lineMap A B s - B := by
        rw [AffineMap.lineMap_apply]
        simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul]
        push_cast
        ring
      _ = z - B := by rw [hsEq]
      _ = AffineMap.lineMap B C t - B := by rw [htEq]
      _ = (t * r) * (B - A) := by
        rw [AffineMap.lineMap_apply]
        simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul]
        rw [hBC]
        push_cast
        ring
  have hscalar : -(1 - s) = t * r := by
    have hc : ((-(1 - s) : ℝ) : ℂ) = ((t * r : ℝ) : ℂ) := by
      apply mul_right_cancel₀ hAB
      simpa only [Complex.ofReal_mul] using heq
    exact Complex.ofReal_injective hc
  nlinarith [hs.1, hs.2, ht.1, hr]

private theorem previous_not_between_of_common_forward
    {A B C : ℂ} (hAB : B - A ≠ 0)
    (hforward : ∃ r : ℝ, 0 < r ∧ C - B = r * (B - A)) :
    ¬Sbtw ℝ B A C := by
  obtain ⟨r, hr, hBC⟩ := hforward
  intro hs
  obtain ⟨t, ht, htEq⟩ := hs.mem_image_Ioo
  have heq : -(B - A) = (t * r) * (B - A) := by
    calc
      -(B - A) = A - B := by ring
      _ = AffineMap.lineMap B C t - B := by rw [htEq]
      _ = (t * r) * (B - A) := by
        rw [AffineMap.lineMap_apply]
        simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul]
        rw [hBC]
        push_cast
        ring
  have hscalar : (-1 : ℝ) = t * r := by
    have hc : ((-1 : ℝ) : ℂ) = ((t * r : ℝ) : ℂ) := by
      apply mul_right_cancel₀ hAB
      calc
        ((-1 : ℝ) : ℂ) * (B - A) = -(B - A) := by norm_num
        _ = (t * r) * (B - A) := heq
        _ = ((t * r : ℝ) : ℂ) * (B - A) := by
          push_cast
          ring
    exact Complex.ofReal_injective hc
  nlinarith [ht.1, hr]

theorem KWRawTurnAdmissible.adjacent_disjoint
    {n : ℕ} [NeZero n] {vertex : Fin n → ℂ}
    (hedge : ∀ i : Fin n, kwRawEdge vertex i ≠ 0)
    {i : Fin n} (h : KWRawTurnAdmissible vertex i) :
    Disjoint
      {z : ℂ | Sbtw ℝ (vertex i) z (vertex (i + 1))}
      {z : ℂ | Sbtw ℝ (vertex (i + 1)) z (vertex (i + 2))} := by
  rcases h with hcross | ⟨r, hr, hforward⟩
  · have hcrossCommon : kwComplexCross
        (vertex i - vertex (i + 1))
        (vertex (i + 2) - vertex (i + 1)) ≠ 0 := by
      intro hzero
      apply hcross
      unfold kwRawEdge
      rw [fin_add_one_add_one]
      unfold kwComplexCross at hzero ⊢
      simp only [Complex.sub_re, Complex.sub_im] at hzero ⊢
      linear_combination -hzero
    have hd := kw_openSegments_disjoint_of_common_left_cross_ne hcrossCommon
    rw [Set.disjoint_left]
    intro z hzFirst hzSecond
    exact Set.disjoint_left.mp hd ((sbtw_comm).mpr hzFirst) hzSecond
  · apply openSegments_disjoint_of_common_forward (hedge i)
    refine ⟨r, hr, ?_⟩
    unfold kwRawEdge at hforward
    simpa only [fin_add_one_add_one] using hforward

theorem KWRawTurnAdmissible.previous_not_between
    {n : ℕ} [NeZero n] {vertex : Fin n → ℂ}
    (hedge : ∀ i : Fin n, kwRawEdge vertex i ≠ 0)
    {i : Fin n} (h : KWRawTurnAdmissible vertex i) :
    ¬Sbtw ℝ (vertex (i + 1)) (vertex i) (vertex (i + 2)) := by
  rcases h with hcross | ⟨r, hr, hforward⟩
  · intro hs
    apply hcross
    have hzero := kwComplexCross_eq_zero_of_sbtw hs
    unfold kwRawEdge
    rw [fin_add_one_add_one]
    unfold kwComplexCross at hzero ⊢
    simp only [Complex.sub_re, Complex.sub_im] at hzero ⊢
    linear_combination hzero
  · apply previous_not_between_of_common_forward (hedge i)
    refine ⟨r, hr, ?_⟩
    unfold kwRawEdge at hforward
    simpa only [fin_add_one_add_one] using hforward



theorem KWRawNonbacktrackingSimpleData.of_turnAdmissible
    {n : ℕ} [NeZero n] (vertex : Fin n → ℂ)
    (hthree : 3 ≤ n)
    (hedge : ∀ i : Fin n, kwRawEdge vertex i ≠ 0)
    (hturn : ∀ i : Fin n, KWRawTurnAdmissible vertex i)
    (hnon : ∀ i j : Fin n, KWEdgesNonincident i j →
      Disjoint (kwRawClosedEdge vertex i) (kwRawClosedEdge vertex j)) :
    KWRawNonbacktrackingSimpleData vertex where
  three_le := hthree
  edge_ne_zero := hedge
  previous_not_between i := (hturn i).previous_not_between hedge
  adjacent_disjoint i := (hturn i).adjacent_disjoint hedge
  nonincident_disjoint := hnon

end StatMech.FrontierA
