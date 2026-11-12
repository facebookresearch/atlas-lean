/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardRectilinearSeparation











namespace StatMech.FrontierA

open scoped Convex NNReal
open Set


def kwHorizontalPart (z : ℂ) : ℂ := z.re

def kwVerticalPart (z : ℂ) : ℂ := z.im * Complex.I

theorem kwHorizontalPart_add_verticalPart (z : ℂ) :
    kwHorizontalPart z + kwVerticalPart z = z := by
  apply Complex.ext <;> simp [kwHorizontalPart, kwVerticalPart]

@[simp] theorem kwHorizontalPart_im (z : ℂ) :
    (kwHorizontalPart z).im = 0 := by
  simp [kwHorizontalPart]

@[simp] theorem kwVerticalPart_re (z : ℂ) :
    (kwVerticalPart z).re = 0 := by
  simp [kwVerticalPart]

theorem norm_kwHorizontalPart_le (z : ℂ) :
    ‖kwHorizontalPart z‖ ≤ ‖z‖ := by
  simpa only [kwHorizontalPart, Complex.norm_real, Real.norm_eq_abs] using
    Complex.abs_re_le_norm z

theorem norm_kwVerticalPart_le (z : ℂ) :
    ‖kwVerticalPart z‖ ≤ ‖z‖ := by
  rw [kwVerticalPart, norm_mul, Complex.norm_real, Complex.norm_I,
    mul_one, Real.norm_eq_abs]
  exact Complex.abs_im_le_norm z


noncomputable def kwStairBase (a b : ℂ) (N : ℕ) (k : Fin (N + 2)) : ℂ :=
  AffineMap.lineMap a b (k.val / (N + 1 : ℝ))


noncomputable def kwStairCorner (a b : ℂ) (N : ℕ) (k : Fin (N + 1)) : ℂ :=
  kwStairBase a b N k.castSucc +
    (N + 1 : ℝ)⁻¹ * kwHorizontalPart (b - a)

theorem kwStairBase_mem_segment (a b : ℂ) (N : ℕ)
    (k : Fin (N + 2)) : kwStairBase a b N k ∈ segment ℝ a b := by
  rw [segment_eq_image_lineMap]
  refine ⟨k.val / (N + 1 : ℝ), ?_, rfl⟩
  constructor
  · positivity
  · apply (div_le_one (by positivity)).mpr
    exact_mod_cast (Nat.le_of_lt_succ k.isLt)

theorem kwStairBase_zero (a b : ℂ) (N : ℕ) :
    kwStairBase a b N 0 = a := by
  simp [kwStairBase]

theorem kwStairBase_last (a b : ℂ) (N : ℕ) :
    kwStairBase a b N (Fin.last (N + 1)) = b := by
  unfold kwStairBase
  have hfrac : ((Fin.last (N + 1)).val : ℝ) / (N + 1 : ℝ) = 1 := by
    simp only [Fin.val_last]
    push_cast
    apply div_self
    positivity
  rw [hfrac, AffineMap.lineMap_apply_one]

theorem kwStairBase_succ_sub (a b : ℂ) (N : ℕ)
    (k : Fin (N + 1)) :
    kwStairBase a b N k.succ - kwStairBase a b N k.castSucc =
      (N + 1 : ℝ)⁻¹ * (b - a) := by
  unfold kwStairBase
  rw [AffineMap.lineMap_apply, AffineMap.lineMap_apply]
  simp only [vsub_eq_sub, vadd_eq_add, Fin.val_succ, Fin.val_castSucc,
    Complex.real_smul]
  push_cast
  have hne : (N + 1 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem kwStairCorner_sub_base (a b : ℂ) (N : ℕ)
    (k : Fin (N + 1)) :
    kwStairCorner a b N k - kwStairBase a b N k.castSucc =
      (N + 1 : ℝ)⁻¹ * kwHorizontalPart (b - a) := by
  simp [kwStairCorner]

theorem kwStairBase_succ_sub_corner (a b : ℂ) (N : ℕ)
    (k : Fin (N + 1)) :
    kwStairBase a b N k.succ - kwStairCorner a b N k =
      (N + 1 : ℝ)⁻¹ * kwVerticalPart (b - a) := by
  calc
    kwStairBase a b N k.succ - kwStairCorner a b N k =
        (kwStairBase a b N k.succ -
          kwStairBase a b N k.castSucc) -
        (kwStairCorner a b N k -
          kwStairBase a b N k.castSucc) := by ring
    _ = (N + 1 : ℝ)⁻¹ * (b - a) -
        (N + 1 : ℝ)⁻¹ * kwHorizontalPart (b - a) := by
      rw [kwStairBase_succ_sub, kwStairCorner_sub_base]
    _ = (N + 1 : ℝ)⁻¹ * kwVerticalPart (b - a) := by
      have hdecomp := kwHorizontalPart_add_verticalPart (b - a)
      have hdiff : (b - a) - kwHorizontalPart (b - a) =
          kwVerticalPart (b - a) := by
        nth_rewrite 1 [← hdecomp]
        ring
      rw [← mul_sub, hdiff]

theorem dist_kwStairCorner_base_le (a b : ℂ) (N : ℕ)
    (k : Fin (N + 1)) :
    dist (kwStairCorner a b N k) (kwStairBase a b N k.castSucc) ≤
      ‖b - a‖ / (N + 1 : ℝ) := by
  rw [dist_eq_norm, kwStairCorner_sub_base, norm_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_inv]
  rw [abs_of_nonneg (by positivity : 0 ≤ (N + 1 : ℝ))]
  rw [inv_mul_eq_div]
  exact (div_le_div_iff_of_pos_right (by positivity)).mpr
    (norm_kwHorizontalPart_le (b - a))



theorem KWFiniteSimplePolygon.kwStairCorner_mem_closedEdgeTube
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (i : Fin n) (N : ℕ) (k : Fin (N + 1)) (r : ℝ≥0)
    (hmesh : ‖polygon.edgeVector i‖ / (N + 1 : ℝ) < r) :
    kwStairCorner (polygon.vertex i) (polygon.vertex (i + 1)) N k ∈
      polygon.closedEdgeTube r i := by
  let base := kwStairBase (polygon.vertex i) (polygon.vertex (i + 1))
    N k.castSucc
  refine ⟨base, ?_, ?_⟩
  · simpa only [KWFiniteSimplePolygon.closedEdge, base] using
      kwStairBase_mem_segment (polygon.vertex i)
        (polygon.vertex (i + 1)) N k.castSucc
  exact (dist_kwStairCorner_base_le _ _ _ _).trans_lt
    (by simpa only [KWFiniteSimplePolygon.edgeVector, base] using hmesh)



theorem KWFiniteSimplePolygon.exists_uniform_stair_mesh
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (r : ℝ≥0) (hr : 0 < r) :
    ∃ N : ℕ, ∀ i : Fin n,
      ‖polygon.edgeVector i‖ / (N + 1 : ℝ) < r := by
  let totalLength : ℝ := ∑ i : Fin n, ‖polygon.edgeVector i‖
  have hrReal : 0 < (r : ℝ) := by exact_mod_cast hr
  obtain ⟨N, hN⟩ := exists_nat_gt (totalLength / (r : ℝ))
  refine ⟨N, ?_⟩
  intro i
  have hiTotal : ‖polygon.edgeVector i‖ ≤ totalLength := by
    dsimp only [totalLength]
    exact Finset.single_le_sum (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ i)
  have htotal : totalLength < (N : ℝ) * (r : ℝ) := by
    have := (div_lt_iff₀ hrReal).mp hN
    nlinarith
  apply (div_lt_iff₀ (by positivity : 0 < (N + 1 : ℝ))).mpr
  nlinarith



theorem KWFiniteSimplePolygon.exists_uniform_stair_corners_in_tubes
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (r : ℝ≥0) (hr : 0 < r) :
    ∃ N : ℕ, ∀ i : Fin n, ∀ k : Fin (N + 1),
      kwStairCorner (polygon.vertex i) (polygon.vertex (i + 1)) N k ∈
        polygon.closedEdgeTube r i := by
  obtain ⟨N, hmesh⟩ := polygon.exists_uniform_stair_mesh r hr
  exact ⟨N, fun i k ↦
    polygon.kwStairCorner_mem_closedEdgeTube i N k r (hmesh i)⟩

end StatMech.FrontierA
