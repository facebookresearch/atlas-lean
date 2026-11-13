/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Euclidean.NinePointCircle
public import Mathlib.Geometry.Euclidean.Incenter
public import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Analysis.Convex.StrictConvexBetween
import Mathlib.Geometry.Euclidean.Angle.Sphere
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

section
namespace MetaMathlibExt

open Affine Affine.Simplex EuclideanGeometry
open scoped InnerProductSpace

section WantedAux

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

private lemma compl_eq_pair (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ({i}ᶜ : Set (Fin 3)) = {j, k} := by
  ext x
  fin_cases x <;> fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all

private lemma altitudeFoot_mem_line (s : Triangle ℝ P) (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    s.altitudeFoot i ∈ line[ℝ, s.points j, s.points k] := by
  have h := s.altitudeFoot_mem_affineSpan_faceOpposite i
  rw [Affine.Simplex.range_faceOpposite_points] at h
  have hc : ({i}ᶜ : Set (Fin 3)) = {j, k} := compl_eq_pair i j k hij hik hjk
  rw [hc, Set.image_pair] at h
  exact h

private lemma height_mul_side_sq (s : Triangle ℝ P) (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    4 * (s.height i) ^ 2 * (dist (s.points j) (s.points k)) ^ 2 =
    2 * (dist (s.points i) (s.points j)) ^ 2 * (dist (s.points i) (s.points k)) ^ 2 +
    2 * (dist (s.points i) (s.points k)) ^ 2 * (dist (s.points j) (s.points k)) ^ 2 +
    2 * (dist (s.points j) (s.points k)) ^ 2 * (dist (s.points i) (s.points j)) ^ 2 -
    (dist (s.points i) (s.points j)) ^ 4 - (dist (s.points i) (s.points k)) ^ 4 -
    (dist (s.points j) (s.points k)) ^ 4 := by
  have hmem := altitudeFoot_mem_line s i j k hij hik hjk
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hmem
  obtain ⟨t, ht⟩ := hmem
  set Ai := s.points i with hAi
  set Aj := s.points j with hAj
  set Ak := s.points k with hAk
  set F := s.altitudeFoot i with hF
  have htF : AffineMap.lineMap Aj Ak t = F := ht
  have hline : F = t • (Ak -ᵥ Aj) +ᵥ Aj := by
    rw [← htF, AffineMap.lineMap_apply]
  set n : V := Ai -ᵥ F with hn
  set w : V := Ak -ᵥ Aj with hw
  set u : V := Ai -ᵥ Aj with hu
  have hj0 : ⟪Aj -ᵥ F, Ai -ᵥ F⟫_ℝ = 0 :=
    s.inner_vsub_altitudeFoot_vsub_altitudeFoot_eq_zero hij
  have hk0 : ⟪Ak -ᵥ F, Ai -ᵥ F⟫_ℝ = 0 :=
    s.inner_vsub_altitudeFoot_vsub_altitudeFoot_eq_zero hik
  have hsub : (Aj -ᵥ F) - (Ak -ᵥ F) = Aj -ᵥ Ak := vsub_sub_vsub_cancel_right Aj Ak F
  have hinner_sub : ⟪(Aj -ᵥ F) - (Ak -ᵥ F), Ai -ᵥ F⟫_ℝ = 0 := by
    rw [inner_sub_left, hj0, hk0, sub_self]
  rw [hsub] at hinner_sub
  have hjk_eq : Aj -ᵥ Ak = -w := by
    rw [hw, ← neg_vsub_eq_vsub_rev]
  rw [hjk_eq] at hinner_sub
  have hnw : ⟪n, w⟫_ℝ = 0 := by
    have h1 : ⟪-w, n⟫_ℝ = 0 := by simpa [hn] using hinner_sub
    rw [inner_neg_left] at h1
    have h2 : ⟪w, n⟫_ℝ = 0 := by linarith
    rw [real_inner_comm] at h2
    exact h2
  have hnv : n = u - t • w := by
    rw [hn, hu, hw, hline, vsub_vadd_eq_vsub_sub]
  have hu_eq : u = n + t • w := by
    rw [hnv]
    abel
  have hH : (s.height i) = ‖n‖ := by
    rw [hn, hAi, hF]
    simp [Affine.Simplex.height, dist_eq_norm_vsub]
  have hW : dist Aj Ak = ‖w‖ := by
    rw [hw, hAj, hAk, dist_eq_norm_vsub']
  have hU : dist Ai Aj = ‖u‖ := by
    rw [hu, hAi, hAj, dist_eq_norm_vsub]
  have hV : dist Ai Ak = ‖u - w‖ := by
    have huv : u - w = Ai -ᵥ Ak := by
      rw [hu, hw, vsub_sub_vsub_cancel_right]
    rw [huv, hAi, hAk, dist_eq_norm_vsub]
  have hU2 : ‖u‖ ^ 2 = ‖n‖ ^ 2 + t ^ 2 * ‖w‖ ^ 2 := by
    conv_lhs => rw [hu_eq]
    rw [norm_add_sq_real, inner_smul_right, hnw, mul_zero, mul_zero, add_zero,
      norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hC : ⟪u, w⟫_ℝ = t * ‖w‖ ^ 2 := by
    rw [hu_eq, inner_add_left, hnw, zero_add, inner_smul_left, real_inner_self_eq_norm_sq]
    simp only [starRingEnd_apply, star_trivial]
  have hHW : ‖n‖ ^ 2 * ‖w‖ ^ 2 = ‖u‖ ^ 2 * ‖w‖ ^ 2 - ⟪u, w⟫_ℝ ^ 2 := by
    rw [hU2, hC]
    ring
  have h2C : 2 * ⟪u, w⟫_ℝ = ‖u‖ ^ 2 + ‖w‖ ^ 2 - ‖u - w‖ ^ 2 := by
    have h := norm_sub_sq_real u w
    linarith
  have hH2 : ‖n‖ ^ 2 = (s.height i) ^ 2 := by rw [hH]
  have hW2 : ‖w‖ ^ 2 = (dist Aj Ak) ^ 2 := by rw [hW]
  have hU2' : ‖u‖ ^ 2 = (dist Ai Aj) ^ 2 := by rw [hU]
  have hV2 : ‖u - w‖ ^ 2 = (dist Ai Ak) ^ 2 := by rw [hV]
  have hmain : 4 * (‖n‖ ^ 2 * ‖w‖ ^ 2) =
      2 * (‖u‖ ^ 2 * ‖u - w‖ ^ 2) + 2 * (‖u - w‖ ^ 2 * ‖w‖ ^ 2) +
      2 * (‖w‖ ^ 2 * ‖u‖ ^ 2) - (‖u‖ ^ 2) ^ 2 - (‖u - w‖ ^ 2) ^ 2 - (‖w‖ ^ 2) ^ 2 := by
    have hC2 : ⟪u, w⟫_ℝ ^ 2 = ((‖u‖ ^ 2 + ‖w‖ ^ 2 - ‖u - w‖ ^ 2) / 2) ^ 2 := by
      rw [← h2C]
      ring
    rw [hHW, hC2]
    ring
  rw [hH2, hW2, hU2', hV2] at hmain
  simp only [hAj, hAk, hAi] at hmain ⊢
  linear_combination hmain

private lemma circumradius_mul_K (s : Triangle ℝ P)
    (a b c K D R : ℝ)
    (ha : a = dist (s.points 1) (s.points 2))
    (hb : b = dist (s.points 0) (s.points 2))
    (hc : c = dist (s.points 0) (s.points 1))
    (hD : D = 2 * a ^ 2 * b ^ 2 + 2 * b ^ 2 * c ^ 2 + 2 * c ^ 2 * a ^ 2 - a ^ 4 - b ^ 4 - c ^ 4)
    (hR : R = s.circumradius)
    (ha_pos : 0 < a) (hb_pos : 0 < b) (hc_pos : 0 < c)
    (hK_pos : 0 < K)
    (h4K2 : 4 * K ^ 2 = D) :
    2 * R * K = a * b * c := by
  have hR_pos : 0 < R := by rw [hR]; exact s.circumradius_pos
  have h2R_pos : 0 < 2 * R := by linarith
  have h2R_ne : (2 * R) ≠ 0 := ne_of_gt h2R_pos
  set A : ℝ := ∠ (s.points 1) (s.points 0) (s.points 2) with hA
  have hsine := Affine.Triangle.dist_div_sin_angle_eq_two_mul_circumradius s (i₁ := 1) (i₂ := 0)
    (i₃ := 2) (by decide) (by decide) (by decide)
  rw [← hR, ← ha, ← hA] at hsine
  have hsin_ne : Real.sin A ≠ 0 := by
    intro h0
    rw [h0, div_zero] at hsine
    linarith
  have hsin : a = 2 * R * Real.sin A := by
    rw [div_eq_iff hsin_ne] at hsine
    linarith [hsine]
  have hcos_full := EuclideanGeometry.law_cos (s.points 1) (s.points 0) (s.points 2)
  rw [← hA] at hcos_full
  have h10 : dist (s.points 1) (s.points 0) = c := by rw [hc, dist_comm]
  have h20 : dist (s.points 2) (s.points 0) = b := by rw [hb, dist_comm]
  rw [← ha, h10, h20] at hcos_full
  have hcos_lin : 2 * b * c * Real.cos A = b ^ 2 + c ^ 2 - a ^ 2 := by
    linear_combination hcos_full
  have htrig := Real.sin_sq_add_cos_sq A
  have hsin_sq : (2 * R * Real.sin A) ^ 2 = a ^ 2 := by rw [← hsin]
  have hcos_sq : (2 * b * c * Real.cos A) ^ 2 = (b ^ 2 + c ^ 2 - a ^ 2) ^ 2 := by
    rw [hcos_lin]
  have h1 : 4 * R ^ 2 * (Real.sin A) ^ 2 = a ^ 2 := by linear_combination hsin_sq
  have h2 : 4 * b ^ 2 * c ^ 2 * (Real.cos A) ^ 2 = (b ^ 2 + c ^ 2 - a ^ 2) ^ 2 := by
    linear_combination hcos_sq
  have hR2D : R ^ 2 * D = a ^ 2 * b ^ 2 * c ^ 2 := by
    rw [hD]
    linear_combination b ^ 2 * c ^ 2 * h1 + R ^ 2 * h2 - 4 * R ^ 2 * b ^ 2 * c ^ 2 * htrig
  have hsq : (2 * R * K) ^ 2 = (a * b * c) ^ 2 := by
    have h4 : (2 * R * K) ^ 2 = 4 * R ^ 2 * K ^ 2 := by ring
    have habc : (a * b * c) ^ 2 = a ^ 2 * b ^ 2 * c ^ 2 := by ring
    rw [h4, habc]
    linear_combination R ^ 2 * h4K2 + hR2D
  have hpos1 : 0 ≤ 2 * R * K := by positivity
  have hpos2 : 0 ≤ a * b * c := by positivity
  exact (sq_eq_sq₀ hpos1 hpos2).mp hsq

private lemma ninePoint_vsub (s : Triangle ℝ P) :
    s.ninePointCircle.center -ᵥ s.circumcenter =
    (1 / 2 : ℝ) • (∑ j, (s.points j -ᵥ s.circumcenter)) := by
  have hcenter := s.ninePointCircle_center
  have hcent := s.centroid_vsub_eq s.circumcenter
  rw [hcenter, vadd_vsub, hcent, smul_smul]
  congr 1
  norm_num

private lemma ninePoint_sub_affine (s : Triangle ℝ P) (w : Fin 3 → ℝ) (hw : ∑ i, w i = 1) :
    s.ninePointCircle.center -ᵥ (Finset.univ.affineCombination ℝ s.points w) =
    ∑ j, ((1 / 2 : ℝ) - w j) • (s.points j -ᵥ s.circumcenter) := by
  have hN := ninePoint_vsub s
  have hP : (∑ j, w j • (s.points j -ᵥ s.circumcenter)) =
      (Finset.univ.affineCombination ℝ s.points w) -ᵥ s.circumcenter :=
    Finset.sum_smul_vsub_const_eq_affineCombination_vsub Finset.univ w s.points s.circumcenter hw
  have hNP : s.ninePointCircle.center -ᵥ (Finset.univ.affineCombination ℝ s.points w) =
      (s.ninePointCircle.center -ᵥ s.circumcenter) -
      ((Finset.univ.affineCombination ℝ s.points w) -ᵥ s.circumcenter) := by
    rw [vsub_sub_vsub_cancel_right]
  rw [hNP, hN, ← hP]
  rw [Finset.smul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [sub_smul]

private lemma v_inner_self (s : Triangle ℝ P) (j : Fin 3) :
    ⟪s.points j -ᵥ s.circumcenter, s.points j -ᵥ s.circumcenter⟫_ℝ = s.circumradius ^ 2 := by
  rw [real_inner_self_eq_norm_sq]
  have h : ‖s.points j -ᵥ s.circumcenter‖ = s.circumradius := by
    rw [← dist_eq_norm_vsub]
    exact s.dist_circumcenter_eq_circumradius j
  rw [h]

private lemma v_inner_pair (s : Triangle ℝ P) (j k : Fin 3) :
    ⟪s.points j -ᵥ s.circumcenter, s.points k -ᵥ s.circumcenter⟫_ℝ =
    s.circumradius ^ 2 - (dist (s.points j) (s.points k)) ^ 2 / 2 := by
  have hnorm_j : ‖s.points j -ᵥ s.circumcenter‖ = s.circumradius := by
    rw [← dist_eq_norm_vsub]
    exact s.dist_circumcenter_eq_circumradius j
  have hnorm_k : ‖s.points k -ᵥ s.circumcenter‖ = s.circumradius := by
    rw [← dist_eq_norm_vsub]
    exact s.dist_circumcenter_eq_circumradius k
  have hsub : (s.points j -ᵥ s.circumcenter) - (s.points k -ᵥ s.circumcenter) =
      s.points j -ᵥ s.points k := vsub_sub_vsub_cancel_right _ _ _
  have hnorm_sub : ‖(s.points j -ᵥ s.circumcenter) - (s.points k -ᵥ s.circumcenter)‖ =
      dist (s.points j) (s.points k) := by
    rw [hsub, dist_eq_norm_vsub]
  have h := norm_sub_sq_real (s.points j -ᵥ s.circumcenter) (s.points k -ᵥ s.circumcenter)
  rw [hnorm_j, hnorm_k, hnorm_sub] at h
  linarith

private lemma ninePoint_dist_sq (s : Triangle ℝ P) (w : Fin 3 → ℝ) (hw : ∑ i, w i = 1) :
    (dist s.ninePointCircle.center (Finset.univ.affineCombination ℝ s.points w)) ^ 2 =
    s.circumradius ^ 2 / 4 -
    (((1 / 2 : ℝ) - w 0) * ((1 / 2 : ℝ) - w 1) * (dist (s.points 0) (s.points 1)) ^ 2 +
     ((1 / 2 : ℝ) - w 0) * ((1 / 2 : ℝ) - w 2) * (dist (s.points 0) (s.points 2)) ^ 2 +
     ((1 / 2 : ℝ) - w 1) * ((1 / 2 : ℝ) - w 2) * (dist (s.points 1) (s.points 2)) ^ 2) := by
  have hNP := ninePoint_sub_affine s w hw
  have hdist : dist s.ninePointCircle.center (Finset.univ.affineCombination ℝ s.points w) =
      ‖s.ninePointCircle.center -ᵥ (Finset.univ.affineCombination ℝ s.points w)‖ := by
    rw [dist_eq_norm_vsub]
  rw [hdist, hNP]
  set c : Fin 3 → ℝ := fun j => (1 / 2 : ℝ) - w j with hc
  set v : Fin 3 → V := fun j => s.points j -ᵥ s.circumcenter with hv
  set R := s.circumradius with hR
  have hsum : c 0 + c 1 + c 2 = 1 / 2 := by
    have hw3 : w 0 + w 1 + w 2 = 1 := by
      have h := hw
      rw [Fin.sum_univ_three] at h
      exact h
    simp only [hc]
    linarith
  have hS : (∑ j, c j • v j) = c 0 • v 0 + c 1 • v 1 + c 2 • v 2 := Fin.sum_univ_three _
  have hnorm : (‖∑ j, c j • v j‖) ^ 2 = ⟪∑ j, c j • v j, ∑ j, c j • v j⟫_ℝ := by
    rw [real_inner_self_eq_norm_sq]
  rw [hnorm, hS]
  have hexpand : ⟪c 0 • v 0 + c 1 • v 1 + c 2 • v 2, c 0 • v 0 + c 1 • v 1 + c 2 • v 2⟫_ℝ =
      c 0 * c 0 * ⟪v 0, v 0⟫_ℝ + c 0 * c 1 * ⟪v 0, v 1⟫_ℝ + c 0 * c 2 * ⟪v 0, v 2⟫_ℝ +
      c 1 * c 0 * ⟪v 1, v 0⟫_ℝ + c 1 * c 1 * ⟪v 1, v 1⟫_ℝ + c 1 * c 2 * ⟪v 1, v 2⟫_ℝ +
      c 2 * c 0 * ⟪v 2, v 0⟫_ℝ + c 2 * c 1 * ⟪v 2, v 1⟫_ℝ + c 2 * c 2 * ⟪v 2, v 2⟫_ℝ := by
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      starRingEnd_apply, star_trivial]
    ring
  rw [hexpand]
  have h00 : ⟪v 0, v 0⟫_ℝ = R ^ 2 := by simp only [hv, hR]; exact v_inner_self s 0
  have h11 : ⟪v 1, v 1⟫_ℝ = R ^ 2 := by simp only [hv, hR]; exact v_inner_self s 1
  have h22 : ⟪v 2, v 2⟫_ℝ = R ^ 2 := by simp only [hv, hR]; exact v_inner_self s 2
  have h01 : ⟪v 0, v 1⟫_ℝ = R ^ 2 - (dist (s.points 0) (s.points 1)) ^ 2 / 2 := by
    simp only [hv, hR]; exact v_inner_pair s 0 1
  have h02 : ⟪v 0, v 2⟫_ℝ = R ^ 2 - (dist (s.points 0) (s.points 2)) ^ 2 / 2 := by
    simp only [hv, hR]; exact v_inner_pair s 0 2
  have h12 : ⟪v 1, v 2⟫_ℝ = R ^ 2 - (dist (s.points 1) (s.points 2)) ^ 2 / 2 := by
    simp only [hv, hR]; exact v_inner_pair s 1 2
  have h10 : ⟪v 1, v 0⟫_ℝ = R ^ 2 - (dist (s.points 0) (s.points 1)) ^ 2 / 2 := by
    have h := v_inner_pair s 1 0
    simp only [hv, hR] at h ⊢
    rw [dist_comm (s.points 1) (s.points 0)] at h
    exact h
  have h20 : ⟪v 2, v 0⟫_ℝ = R ^ 2 - (dist (s.points 0) (s.points 2)) ^ 2 / 2 := by
    have h := v_inner_pair s 2 0
    simp only [hv, hR] at h ⊢
    rw [dist_comm (s.points 2) (s.points 0)] at h
    exact h
  have h21 : ⟪v 2, v 1⟫_ℝ = R ^ 2 - (dist (s.points 1) (s.points 2)) ^ 2 / 2 := by
    have h := v_inner_pair s 2 1
    simp only [hv, hR] at h ⊢
    rw [dist_comm (s.points 2) (s.points 1)] at h
    exact h
  rw [h00, h11, h22, h01, h02, h12, h10, h20, h21]
  simp only [hc]
  linear_combination R ^ 2 * (c 0 + c 1 + c 2 + 1 / 2) * hsum

private lemma incenter_weights (s : Triangle ℝ P)
    (a b c K ss : ℝ)
    (hK : K = a * s.height 0)
    (hss : ss = (a + b + c) / 2)
    (ha_pos : 0 < a) (hb_pos : 0 < b) (hc_pos : 0 < c)
    (hK_pos : 0 < K)
    (heq1 : b * s.height 1 = K)
    (heq2 : c * s.height 2 = K) :
    (s.excenterWeights ∅ 0 = a / (2 * ss) ∧
     s.excenterWeights ∅ 1 = b / (2 * ss) ∧
     s.excenterWeights ∅ 2 = c / (2 * ss) ∧
     s.inradius = K / (2 * ss) ∧
     0 < ss) := by
  have hh0 : 0 < s.height 0 := s.height_pos 0
  have hh1 : 0 < s.height 1 := s.height_pos 1
  have hh2 : 0 < s.height 2 := s.height_pos 2
  have hK_ne : K ≠ 0 := ne_of_gt hK_pos
  have hh0_ne : s.height 0 ≠ 0 := ne_of_gt hh0
  have hh1_ne : s.height 1 ≠ 0 := ne_of_gt hh1
  have hh2_ne : s.height 2 ≠ 0 := ne_of_gt hh2
  have hss_pos : 0 < ss := by rw [hss]; linarith
  have hinv0 : (s.height 0)⁻¹ = a / K := by
    rw [hK]
    field_simp
  have hinv1 : (s.height 1)⁻¹ = b / K := by
    have h : K = b * s.height 1 := heq1.symm
    rw [h]
    field_simp
  have hinv2 : (s.height 2)⁻¹ = c / K := by
    have h : K = c * s.height 2 := heq2.symm
    rw [h]
    field_simp
  have hsum : (∑ i, s.excenterWeightsUnnorm ∅ i) = (2 * ss) / K := by
    rw [Fin.sum_univ_three]
    simp only [excenterWeightsUnnorm_empty_apply, hinv0, hinv1, hinv2]
    rw [hss]
    field_simp
  have hinv_sum : (∑ i, s.excenterWeightsUnnorm ∅ i)⁻¹ = K / (2 * ss) := by
    rw [hsum]
    field_simp
  have hw0 : s.excenterWeights ∅ 0 = a / (2 * ss) := by
    simp only [excenterWeights, Pi.smul_apply, smul_eq_mul]
    rw [hinv_sum, excenterWeightsUnnorm_empty_apply, hinv0]
    field_simp
  have hw1 : s.excenterWeights ∅ 1 = b / (2 * ss) := by
    simp only [excenterWeights, Pi.smul_apply, smul_eq_mul]
    rw [hinv_sum, excenterWeightsUnnorm_empty_apply, hinv1]
    field_simp
  have hw2 : s.excenterWeights ∅ 2 = c / (2 * ss) := by
    simp only [excenterWeights, Pi.smul_apply, smul_eq_mul]
    rw [hinv_sum, excenterWeightsUnnorm_empty_apply, hinv2]
    field_simp
  have hr : s.inradius = K / (2 * ss) := by
    rw [inradius_eq_abs_inv_sum, hinv_sum]
    rw [abs_of_pos]
    positivity
  exact ⟨hw0, hw1, hw2, hr, hss_pos⟩

private lemma ex0_weights (s : Triangle ℝ P)
    (a b c K : ℝ)
    (hK : K = a * s.height 0)
    (ha_pos : 0 < a) (hb_pos : 0 < b) (hc_pos : 0 < c)
    (hK_pos : 0 < K)
    (heq1 : b * s.height 1 = K)
    (heq2 : c * s.height 2 = K) :
    (s.excenterWeights {0} 0 = -a / (b + c - a) ∧
     s.excenterWeights {0} 1 = b / (b + c - a) ∧
     s.excenterWeights {0} 2 = c / (b + c - a) ∧
     s.exradius {0} = K / (b + c - a) ∧
     0 < b + c - a) := by
  have hh0 : 0 < s.height 0 := s.height_pos 0
  have hh1 : 0 < s.height 1 := s.height_pos 1
  have hh2 : 0 < s.height 2 := s.height_pos 2
  have hK_ne : K ≠ 0 := ne_of_gt hK_pos
  have hh0_ne : s.height 0 ≠ 0 := ne_of_gt hh0
  have hh1_ne : s.height 1 ≠ 0 := ne_of_gt hh1
  have hh2_ne : s.height 2 ≠ 0 := ne_of_gt hh2
  have hinv0 : (s.height 0)⁻¹ = a / K := by
    rw [hK]
    field_simp
  have hinv1 : (s.height 1)⁻¹ = b / K := by
    have h : K = b * s.height 1 := heq1.symm
    rw [h]
    field_simp
  have hinv2 : (s.height 2)⁻¹ = c / K := by
    have h : K = c * s.height 2 := heq2.symm
    rw [h]
    field_simp
  have hu0 : s.excenterWeightsUnnorm {0} 0 = -((s.height 0)⁻¹) := by
    simp [excenterWeightsUnnorm]
  have hu1 : s.excenterWeightsUnnorm {0} 1 = (s.height 1)⁻¹ := by
    simp [excenterWeightsUnnorm]
  have hu2 : s.excenterWeightsUnnorm {0} 2 = (s.height 2)⁻¹ := by
    simp [excenterWeightsUnnorm]
  have hsum : (∑ i, s.excenterWeightsUnnorm {0} i) = (b + c - a) / K := by
    rw [Fin.sum_univ_three, hu0, hu1, hu2, hinv0, hinv1, hinv2]
    field_simp
    ring
  have hsum_pos : 0 < (∑ i, s.excenterWeightsUnnorm {0} i) :=
    s.sum_excenterWeightsUnnorm_singleton_pos 0
  have hbca_pos : 0 < b + c - a := by
    have h : 0 < (b + c - a) / K := by rw [← hsum]; exact hsum_pos
    exact (div_pos_iff_of_pos_right hK_pos).mp h
  have hinv_sum : (∑ i, s.excenterWeightsUnnorm {0} i)⁻¹ = K / (b + c - a) := by
    rw [hsum]
    field_simp
  have hw0 : s.excenterWeights {0} 0 = -a / (b + c - a) := by
    simp only [excenterWeights, Pi.smul_apply, smul_eq_mul]
    rw [hinv_sum, hu0, hinv0]
    field_simp
  have hw1 : s.excenterWeights {0} 1 = b / (b + c - a) := by
    simp only [excenterWeights, Pi.smul_apply, smul_eq_mul]
    rw [hinv_sum, hu1, hinv1]
    field_simp
  have hw2 : s.excenterWeights {0} 2 = c / (b + c - a) := by
    simp only [excenterWeights, Pi.smul_apply, smul_eq_mul]
    rw [hinv_sum, hu2, hinv2]
    field_simp
  have hr : s.exradius {0} = K / (b + c - a) := by
    rw [exradius_eq_abs_inv_sum, hinv_sum]
    rw [abs_of_pos]
    positivity
  exact ⟨hw0, hw1, hw2, hr, hbca_pos⟩

private lemma ex1_weights (s : Triangle ℝ P)
    (a b c K : ℝ)
    (hK : K = a * s.height 0)
    (ha_pos : 0 < a) (hb_pos : 0 < b) (hc_pos : 0 < c)
    (hK_pos : 0 < K)
    (heq1 : b * s.height 1 = K)
    (heq2 : c * s.height 2 = K) :
    (s.excenterWeights {1} 0 = a / (c + a - b) ∧
     s.excenterWeights {1} 1 = -b / (c + a - b) ∧
     s.excenterWeights {1} 2 = c / (c + a - b) ∧
     s.exradius {1} = K / (c + a - b) ∧
     0 < c + a - b) := by
  have hh0 : 0 < s.height 0 := s.height_pos 0
  have hh1 : 0 < s.height 1 := s.height_pos 1
  have hh2 : 0 < s.height 2 := s.height_pos 2
  have hK_ne : K ≠ 0 := ne_of_gt hK_pos
  have hh0_ne : s.height 0 ≠ 0 := ne_of_gt hh0
  have hh1_ne : s.height 1 ≠ 0 := ne_of_gt hh1
  have hh2_ne : s.height 2 ≠ 0 := ne_of_gt hh2
  have hinv0 : (s.height 0)⁻¹ = a / K := by
    rw [hK]
    field_simp
  have hinv1 : (s.height 1)⁻¹ = b / K := by
    have h : K = b * s.height 1 := heq1.symm
    rw [h]
    field_simp
  have hinv2 : (s.height 2)⁻¹ = c / K := by
    have h : K = c * s.height 2 := heq2.symm
    rw [h]
    field_simp
  have hu0 : s.excenterWeightsUnnorm {1} 0 = (s.height 0)⁻¹ := by
    simp [excenterWeightsUnnorm]
  have hu1 : s.excenterWeightsUnnorm {1} 1 = -((s.height 1)⁻¹) := by
    simp [excenterWeightsUnnorm]
  have hu2 : s.excenterWeightsUnnorm {1} 2 = (s.height 2)⁻¹ := by
    simp [excenterWeightsUnnorm]
  have hsum : (∑ i, s.excenterWeightsUnnorm {1} i) = (c + a - b) / K := by
    rw [Fin.sum_univ_three, hu0, hu1, hu2, hinv0, hinv1, hinv2]
    field_simp
    ring
  have hsum_pos : 0 < (∑ i, s.excenterWeightsUnnorm {1} i) :=
    s.sum_excenterWeightsUnnorm_singleton_pos 1
  have hcab_pos : 0 < c + a - b := by
    have h : 0 < (c + a - b) / K := by rw [← hsum]; exact hsum_pos
    exact (div_pos_iff_of_pos_right hK_pos).mp h
  have hinv_sum : (∑ i, s.excenterWeightsUnnorm {1} i)⁻¹ = K / (c + a - b) := by
    rw [hsum]
    field_simp
  have hw0 : s.excenterWeights {1} 0 = a / (c + a - b) := by
    simp only [excenterWeights, Pi.smul_apply, smul_eq_mul]
    rw [hinv_sum, hu0, hinv0]
    field_simp
  have hw1 : s.excenterWeights {1} 1 = -b / (c + a - b) := by
    simp only [excenterWeights, Pi.smul_apply, smul_eq_mul]
    rw [hinv_sum, hu1, hinv1]
    field_simp
  have hw2 : s.excenterWeights {1} 2 = c / (c + a - b) := by
    simp only [excenterWeights, Pi.smul_apply, smul_eq_mul]
    rw [hinv_sum, hu2, hinv2]
    field_simp
  have hr : s.exradius {1} = K / (c + a - b) := by
    rw [exradius_eq_abs_inv_sum, hinv_sum]
    rw [abs_of_pos]
    positivity
  exact ⟨hw0, hw1, hw2, hr, hcab_pos⟩

private lemma ex2_weights (s : Triangle ℝ P)
    (a b c K : ℝ)
    (hK : K = a * s.height 0)
    (ha_pos : 0 < a) (hb_pos : 0 < b) (hc_pos : 0 < c)
    (hK_pos : 0 < K)
    (heq1 : b * s.height 1 = K)
    (heq2 : c * s.height 2 = K) :
    (s.excenterWeights {2} 0 = a / (a + b - c) ∧
     s.excenterWeights {2} 1 = b / (a + b - c) ∧
     s.excenterWeights {2} 2 = -c / (a + b - c) ∧
     s.exradius {2} = K / (a + b - c) ∧
     0 < a + b - c) := by
  have hh0 : 0 < s.height 0 := s.height_pos 0
  have hh1 : 0 < s.height 1 := s.height_pos 1
  have hh2 : 0 < s.height 2 := s.height_pos 2
  have hK_ne : K ≠ 0 := ne_of_gt hK_pos
  have hh0_ne : s.height 0 ≠ 0 := ne_of_gt hh0
  have hh1_ne : s.height 1 ≠ 0 := ne_of_gt hh1
  have hh2_ne : s.height 2 ≠ 0 := ne_of_gt hh2
  have hinv0 : (s.height 0)⁻¹ = a / K := by
    rw [hK]
    field_simp
  have hinv1 : (s.height 1)⁻¹ = b / K := by
    have h : K = b * s.height 1 := heq1.symm
    rw [h]
    field_simp
  have hinv2 : (s.height 2)⁻¹ = c / K := by
    have h : K = c * s.height 2 := heq2.symm
    rw [h]
    field_simp
  have hu0 : s.excenterWeightsUnnorm {2} 0 = (s.height 0)⁻¹ := by
    simp [excenterWeightsUnnorm]
  have hu1 : s.excenterWeightsUnnorm {2} 1 = (s.height 1)⁻¹ := by
    simp [excenterWeightsUnnorm]
  have hu2 : s.excenterWeightsUnnorm {2} 2 = -((s.height 2)⁻¹) := by
    simp [excenterWeightsUnnorm]
  have hsum : (∑ i, s.excenterWeightsUnnorm {2} i) = (a + b - c) / K := by
    rw [Fin.sum_univ_three, hu0, hu1, hu2, hinv0, hinv1, hinv2]
    field_simp
    ring
  have hsum_pos : 0 < (∑ i, s.excenterWeightsUnnorm {2} i) :=
    s.sum_excenterWeightsUnnorm_singleton_pos 2
  have habc_pos : 0 < a + b - c := by
    have h : 0 < (a + b - c) / K := by rw [← hsum]; exact hsum_pos
    exact (div_pos_iff_of_pos_right hK_pos).mp h
  have hinv_sum : (∑ i, s.excenterWeightsUnnorm {2} i)⁻¹ = K / (a + b - c) := by
    rw [hsum]
    field_simp
  have hw0 : s.excenterWeights {2} 0 = a / (a + b - c) := by
    simp only [excenterWeights, Pi.smul_apply, smul_eq_mul]
    rw [hinv_sum, hu0, hinv0]
    field_simp
  have hw1 : s.excenterWeights {2} 1 = b / (a + b - c) := by
    simp only [excenterWeights, Pi.smul_apply, smul_eq_mul]
    rw [hinv_sum, hu1, hinv1]
    field_simp
  have hw2 : s.excenterWeights {2} 2 = -c / (a + b - c) := by
    simp only [excenterWeights, Pi.smul_apply, smul_eq_mul]
    rw [hinv_sum, hu2, hinv2]
    field_simp
  have hr : s.exradius {2} = K / (a + b - c) := by
    rw [exradius_eq_abs_inv_sum, hinv_sum]
    rw [abs_of_pos]
    positivity
  exact ⟨hw0, hw1, hw2, hr, habc_pos⟩

end WantedAux

/-- **Feuerbach's theorem.** Let $T$ be a triangle in a two-dimensional Euclidean affine space,
with incircle $\omega$, nine-point circle $N$, and excircle $\omega_i$ opposite its $i$-th vertex
for each $i$. If $T$ is not equilateral, then there is a point $F$ at which $\omega$ is internally
tangent to $N$ (that is, $F$ lies on both circles and the center of $\omega$ lies on the segment
from the center of $N$ to $F$), and $F$ is the only common point of $\omega$ and $N$. For every
triangle $T$ and every $i$, the nine-point circle $N$ is externally tangent to $\omega_i$.

Proves `Wanted` entry `Feuerbach_theorem` (statement `feuerbach-s1`).

Source: K. W. Feuerbach, 1822; https://en.wikipedia.org/wiki/Feuerbach_point
-/
theorem Feuerbach_theorem {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    [Fact (Module.finrank ℝ V = 2)] (s : Affine.Triangle ℝ P) :
    (¬ (dist (s.points 0) (s.points 1) = dist (s.points 1) (s.points 2) ∧
      dist (s.points 1) (s.points 2) = dist (s.points 2) (s.points 0)) →
    (∃ F, s.insphere.IsIntTangentAt s.ninePointCircle F ∧
      ∀ G, G ∈ s.insphere → G ∈ s.ninePointCircle → G = F)) ∧
      ∀ i, s.ninePointCircle.IsExtTangent (s.exsphere {i}) := by
  set a := dist (s.points 1) (s.points 2) with ha
  set b := dist (s.points 0) (s.points 2) with hb
  set c := dist (s.points 0) (s.points 1) with hc
  set K := a * s.height 0 with hK
  set D := 2 * a ^ 2 * b ^ 2 + 2 * b ^ 2 * c ^ 2 + 2 * c ^ 2 * a ^ 2 - a ^ 4 - b ^ 4 - c ^ 4
    with hD
  set ss := (a + b + c) / 2 with hss
  set R := s.circumradius with hR
  have hinj := s.independent.injective
  have ha_pos : 0 < a := dist_pos.mpr (hinj.ne (by decide : (1 : Fin 3) ≠ 2))
  have hb_pos : 0 < b := dist_pos.mpr (hinj.ne (by decide : (0 : Fin 3) ≠ 2))
  have hc_pos : 0 < c := dist_pos.mpr (hinj.ne (by decide : (0 : Fin 3) ≠ 1))
  have hh0 : 0 < s.height 0 := s.height_pos 0
  have hh1 : 0 < s.height 1 := s.height_pos 1
  have hh2 : 0 < s.height 2 := s.height_pos 2
  have hK_pos : 0 < K := mul_pos ha_pos hh0
  have hR_pos : 0 < R := by rw [hR]; exact s.circumradius_pos
  have h0 := height_mul_side_sq s 0 1 2 (by decide) (by decide) (by decide)
  have h1 := height_mul_side_sq s 1 0 2 (by decide) (by decide) (by decide)
  have h2 := height_mul_side_sq s 2 0 1 (by decide) (by decide) (by decide)
  rw [dist_comm (s.points 1) (s.points 0)] at h1
  rw [dist_comm (s.points 2) (s.points 0), dist_comm (s.points 2) (s.points 1)] at h2
  have h0' : 4 * (a * s.height 0) ^ 2 = D := by
    rw [hD]
    rw [← ha, ← hb, ← hc] at h0
    linear_combination h0
  have h1' : 4 * (b * s.height 1) ^ 2 = D := by
    rw [hD]
    rw [← ha, ← hb, ← hc] at h1
    linear_combination h1
  have h2' : 4 * (c * s.height 2) ^ 2 = D := by
    rw [hD]
    rw [← ha, ← hb, ← hc] at h2
    linear_combination h2
  have h4K2 : 4 * K ^ 2 = D := by
    rw [hK]
    exact h0'
  have heq1 : b * s.height 1 = K := by
    have hsq1 : (b * s.height 1) ^ 2 = (a * s.height 0) ^ 2 := by linarith [h0', h1']
    have hsq : (b * s.height 1) ^ 2 = K ^ 2 := by rw [hK]; exact hsq1
    have hbK : 0 ≤ b * s.height 1 := by positivity
    have hKK : 0 ≤ K := le_of_lt hK_pos
    exact (sq_eq_sq₀ hbK hKK).mp hsq
  have heq2 : c * s.height 2 = K := by
    have hsq2 : (c * s.height 2) ^ 2 = (a * s.height 0) ^ 2 := by linarith [h0', h2']
    have hsq : (c * s.height 2) ^ 2 = K ^ 2 := by rw [hK]; exact hsq2
    have hcK : 0 ≤ c * s.height 2 := by positivity
    have hKK : 0 ≤ K := le_of_lt hK_pos
    exact (sq_eq_sq₀ hcK hKK).mp hsq
  have hRK : 2 * R * K = a * b * c :=
    circumradius_mul_K s a b c K D R ha hb hc hD hR ha_pos hb_pos hc_pos hK_pos h4K2
  obtain ⟨hw_in0, hw_in1, hw_in2, hr_in, hss_pos⟩ :=
    incenter_weights s a b c K ss hK hss ha_pos hb_pos hc_pos hK_pos heq1 heq2
  obtain ⟨hw_ex00, hw_ex01, hw_ex02, hr_ex0, hbca_pos⟩ :=
    ex0_weights s a b c K hK ha_pos hb_pos hc_pos hK_pos heq1 heq2
  obtain ⟨hw_ex10, hw_ex11, hw_ex12, hr_ex1, hcab_pos⟩ :=
    ex1_weights s a b c K hK ha_pos hb_pos hc_pos hK_pos heq1 heq2
  obtain ⟨hw_ex20, hw_ex21, hw_ex22, hr_ex2, habc_pos⟩ :=
    ex2_weights s a b c K hK ha_pos hb_pos hc_pos hK_pos heq1 heq2
  have h2ss : 2 * ss = a + b + c := by rw [hss]; ring
  have hS_ne : (a + b + c) ≠ 0 := by
    have hpos : 0 < a + b + c := by linarith
    exact ne_of_gt hpos
  rw [hD] at h4K2
  have hw_sum_in := s.excenterExists_empty.sum_excenterWeights_eq_one
  have hdist_in := ninePoint_dist_sq s _ hw_sum_in
  rw [← s.incenter_eq_affineCombination] at hdist_in
  rw [hw_in0, hw_in1, hw_in2, ← hc, ← hb, ← ha, ← hR] at hdist_in
  rw [h2ss] at hdist_in
  have hrS : s.inradius = K / (a + b + c) := by rw [hr_in, h2ss]
  have h_sq_in : (dist s.ninePointCircle.center s.incenter) ^ 2 =
      (R / 2 - s.inradius) ^ 2 := by
    rw [hrS]
    field_simp at hdist_in ⊢
    linear_combination (1 / 4) * hdist_in + 2 * (a + b + c) * hRK - h4K2
  have hw_sum_ex0 := (s.excenterExists_singleton 0).sum_excenterWeights_eq_one
  have hdist_ex0 := ninePoint_dist_sq s _ hw_sum_ex0
  rw [← s.excenter_eq_affineCombination {0}] at hdist_ex0
  rw [hw_ex00, hw_ex01, hw_ex02, ← hc, ← hb, ← ha, ← hR] at hdist_ex0
  have hT0_ne : (b + c - a) ≠ 0 := ne_of_gt hbca_pos
  have h_sq_ex0 : (dist s.ninePointCircle.center (s.excenter {0})) ^ 2 =
      (R / 2 + s.exradius {0}) ^ 2 := by
    rw [hr_ex0]
    field_simp at hdist_ex0 ⊢
    linear_combination (1 / 4) * hdist_ex0 - 2 * (b + c - a) * hRK - h4K2
  have hw_sum_ex1 := (s.excenterExists_singleton 1).sum_excenterWeights_eq_one
  have hdist_ex1 := ninePoint_dist_sq s _ hw_sum_ex1
  rw [← s.excenter_eq_affineCombination {1}] at hdist_ex1
  rw [hw_ex10, hw_ex11, hw_ex12, ← hc, ← hb, ← ha, ← hR] at hdist_ex1
  have hT1_ne : (c + a - b) ≠ 0 := ne_of_gt hcab_pos
  have h_sq_ex1 : (dist s.ninePointCircle.center (s.excenter {1})) ^ 2 =
      (R / 2 + s.exradius {1}) ^ 2 := by
    rw [hr_ex1]
    field_simp at hdist_ex1 ⊢
    linear_combination (1 / 4) * hdist_ex1 - 2 * (c + a - b) * hRK - h4K2
  have hw_sum_ex2 := (s.excenterExists_singleton 2).sum_excenterWeights_eq_one
  have hdist_ex2 := ninePoint_dist_sq s _ hw_sum_ex2
  rw [← s.excenter_eq_affineCombination {2}] at hdist_ex2
  rw [hw_ex20, hw_ex21, hw_ex22, ← hc, ← hb, ← ha, ← hR] at hdist_ex2
  have hT2_ne : (a + b - c) ≠ 0 := ne_of_gt habc_pos
  have h_sq_ex2 : (dist s.ninePointCircle.center (s.excenter {2})) ^ 2 =
      (R / 2 + s.exradius {2}) ^ 2 := by
    rw [hr_ex2]
    field_simp at hdist_ex2 ⊢
    linear_combination (1 / 4) * hdist_ex2 - 2 * (a + b - c) * hRK - h4K2
  have : Nontrivial V :=
    Module.nontrivial_of_finrank_eq_succ (n := 1) (Fact.out : Module.finrank ℝ V = 2)
  have hRn : s.ninePointCircle.radius = R / 2 := by
    rw [s.ninePointCircle_radius, ← hR]
    norm_num
  constructor
  · intro h_neq
    have hcomm : dist (s.points 2) (s.points 0) = b := by rw [dist_comm, ← hb]
    rw [hcomm] at h_neq
    have hK_ne : K ≠ 0 := ne_of_gt hK_pos
    have h_eq : R / 2 - s.inradius =
        ((b + c - a) / 2 * (((c + a - b) / 2 - (a + b - c) / 2) ^ 2) +
          (c + a - b) / 2 * (((a + b - c) / 2 - (b + c - a) / 2) ^ 2) +
          (a + b - c) / 2 * (((b + c - a) / 2 - (c + a - b) / 2) ^ 2)) / (4 * K) := by
      rw [hrS]
      field_simp
      linear_combination 8 * (a + b + c) * hRK - 8 * h4K2
    set x := (b + c - a) / 2 with hx_def
    set y := (c + a - b) / 2 with hy_def
    set z := (a + b - c) / 2 with hz_def
    have hx : 0 < x := by rw [hx_def]; linarith [hbca_pos]
    have hy : 0 < y := by rw [hy_def]; linarith [hcab_pos]
    have hz : 0 < z := by rw [hz_def]; linarith [habc_pos]
    have ha_def : a = y + z := by rw [hy_def, hz_def]; ring
    have hb_def : b = x + z := by rw [hx_def, hz_def]; ring
    have hc_def : c = x + y := by rw [hx_def, hy_def]; ring
    have h_sum_pos : 0 < x * (y - z) ^ 2 + y * (z - x) ^ 2 + z * (x - y) ^ 2 := by
      have t1_nonneg : 0 ≤ x * (y - z) ^ 2 := mul_nonneg (le_of_lt hx) (sq_nonneg _)
      have t2_nonneg : 0 ≤ y * (z - x) ^ 2 := mul_nonneg (le_of_lt hy) (sq_nonneg _)
      have t3_nonneg : 0 ≤ z * (x - y) ^ 2 := mul_nonneg (le_of_lt hz) (sq_nonneg _)
      have hsum_nonneg : 0 ≤ x * (y - z) ^ 2 + y * (z - x) ^ 2 + z * (x - y) ^ 2 := by
        positivity
      have hsum_ne : x * (y - z) ^ 2 + y * (z - x) ^ 2 + z * (x - y) ^ 2 ≠ 0 := by
        intro h0
        rw [add_assoc] at h0
        have h23_nonneg : 0 ≤ y * (z - x) ^ 2 + z * (x - y) ^ 2 :=
          add_nonneg t2_nonneg t3_nonneg
        have h1 : x * (y - z) ^ 2 = 0 ∧ y * (z - x) ^ 2 + z * (x - y) ^ 2 = 0 :=
          (add_eq_zero_iff_of_nonneg t1_nonneg h23_nonneg).mp h0
        have h2 : y * (z - x) ^ 2 = 0 ∧ z * (x - y) ^ 2 = 0 :=
          (add_eq_zero_iff_of_nonneg t2_nonneg t3_nonneg).mp h1.2
        have hyz : (y - z) ^ 2 = 0 := by
          have hx_ne : x ≠ 0 := ne_of_gt hx
          exact (mul_eq_zero.mp h1.1).resolve_left hx_ne
        have hzx : (z - x) ^ 2 = 0 := by
          have hy_ne : y ≠ 0 := ne_of_gt hy
          exact (mul_eq_zero.mp h2.1).resolve_left hy_ne
        have hyz_eq : y = z := by
          have h : y - z = 0 := sq_eq_zero_iff.mp hyz
          linarith
        have hzx_eq : z = x := by
          have h : z - x = 0 := sq_eq_zero_iff.mp hzx
          linarith
        have hxy_eq : x = y := by linarith
        have ha_eq : a = b := by rw [ha_def, hb_def, hxy_eq, hyz_eq]
        have hc_eq : c = a := by rw [hc_def, ha_def, hxy_eq, hyz_eq]
        exact h_neq ⟨hc_eq, ha_eq⟩
      exact lt_of_le_of_ne' hsum_nonneg hsum_ne
    have h_Rr_pos : 0 < R / 2 - s.inradius := by
      rw [h_eq]
      have h4K_pos : 0 < 4 * K := by positivity
      have hsum_pos' : 0 < (b + c - a) / 2 * (((c + a - b) / 2 - (a + b - c) / 2) ^ 2) +
          (c + a - b) / 2 * (((a + b - c) / 2 - (b + c - a) / 2) ^ 2) +
          (a + b - c) / 2 * (((b + c - a) / 2 - (c + a - b) / 2) ^ 2) := by
        simp only [← hx_def, ← hy_def, ← hz_def]
        exact h_sum_pos
      exact div_pos hsum_pos' h4K_pos
    have h_dist_in : dist s.incenter s.ninePointCircle.center =
        R / 2 - s.inradius := by
      have h1 : 0 ≤ dist s.incenter s.ninePointCircle.center := dist_nonneg
      have h2 : 0 ≤ R / 2 - s.inradius := le_of_lt h_Rr_pos
      have hsq : (dist s.incenter s.ninePointCircle.center) ^ 2 =
          (R / 2 - s.inradius) ^ 2 := by
        rw [dist_comm]
        exact h_sq_in
      exact (sq_eq_sq₀ h1 h2).mp hsq
    have h_tangent : s.insphere.IsIntTangent s.ninePointCircle := by
      rw [EuclideanGeometry.Sphere.isIntTangent_iff_dist_center]
      refine ⟨?_, ?_, ?_⟩
      · simp only [s.insphere_center, s.insphere_radius, hRn]
        exact h_dist_in
      · rw [s.insphere_radius]
        exact le_of_lt s.inradius_pos
      · rw [hRn]
        positivity
    obtain ⟨F, hF⟩ := h_tangent
    refine ⟨F, hF, ?_⟩
    intro G hG_in hG_np
    have hG_in_dist : dist s.incenter G = s.inradius := by
      have h := EuclideanGeometry.mem_sphere'.mp hG_in
      rw [s.insphere_center, s.insphere_radius] at h
      exact h
    have hG_np_dist : dist s.ninePointCircle.center G = R / 2 := by
      have h := EuclideanGeometry.mem_sphere'.mp hG_np
      rw [hRn] at h
      exact h
    have hF_in_dist : dist s.incenter F = s.inradius := by
      have h := EuclideanGeometry.mem_sphere'.mp hF.mem_left
      rw [s.insphere_center, s.insphere_radius] at h
      exact h
    have hF_np_dist : dist s.ninePointCircle.center F = R / 2 := by
      have h := EuclideanGeometry.mem_sphere'.mp hF.mem_right
      rw [hRn] at h
      exact h
    set t := (R / 2 - s.inradius) / (R / 2) with ht_def
    have hR2_pos : 0 < R / 2 := by positivity
    have hR2_ne : (R / 2) ≠ 0 := ne_of_gt hR2_pos
    have hR_ne : R ≠ 0 := ne_of_gt hR_pos
    have ht_pos : 0 < t := by rw [ht_def]; exact div_pos h_Rr_pos hR2_pos
    have ht_ne : t ≠ 0 := ne_of_gt ht_pos
    have h_NI : dist s.ninePointCircle.center s.incenter = R / 2 - s.inradius := by
      rw [dist_comm]
      exact h_dist_in
    have h1G : dist s.ninePointCircle.center s.incenter =
        t * dist s.ninePointCircle.center G := by
      rw [h_NI, hG_np_dist, ht_def]
      exact (div_mul_cancel₀ _ hR2_ne).symm
    have h2G : dist s.incenter G = (1 - t) * dist s.ninePointCircle.center G := by
      rw [hG_in_dist, hG_np_dist, ht_def]
      field_simp
      ring
    have h1F : dist s.ninePointCircle.center s.incenter =
        t * dist s.ninePointCircle.center F := by
      rw [h_NI, hF_np_dist, ht_def]
      exact (div_mul_cancel₀ _ hR2_ne).symm
    have h2F : dist s.incenter F = (1 - t) * dist s.ninePointCircle.center F := by
      rw [hF_in_dist, hF_np_dist, ht_def]
      field_simp
      ring
    have hIG : s.incenter = AffineMap.lineMap s.ninePointCircle.center G t :=
      eq_lineMap_of_dist_eq_mul_of_dist_eq_mul h1G h2G
    have hIF : s.incenter = AffineMap.lineMap s.ninePointCircle.center F t :=
      eq_lineMap_of_dist_eq_mul_of_dist_eq_mul h1F h2F
    have h_eq : AffineMap.lineMap s.ninePointCircle.center G t =
        AffineMap.lineMap s.ninePointCircle.center F t := hIG.symm.trans hIF
    rw [AffineMap.lineMap_apply, AffineMap.lineMap_apply] at h_eq
    have h_smul : t • (G -ᵥ s.ninePointCircle.center) =
        t • (F -ᵥ s.ninePointCircle.center) :=
      vadd_right_cancel _ h_eq
    have h_vsub : G -ᵥ s.ninePointCircle.center = F -ᵥ s.ninePointCircle.center :=
      (smul_right_injective V ht_ne) h_smul
    exact (vsub_left_injective _) h_vsub
  · intro i
    fin_cases i
    · have hex_pos : 0 < s.exradius {0} := s.exradius_singleton_pos 0
      have h_nonneg : 0 ≤ R / 2 + s.exradius {0} := by positivity
      have h_dist : dist s.ninePointCircle.center (s.excenter {0}) =
          R / 2 + s.exradius {0} :=
        (sq_eq_sq₀ dist_nonneg h_nonneg).mp h_sq_ex0
      rw [EuclideanGeometry.Sphere.isExtTangent_iff_dist_center]
      refine ⟨?_, ?_, ?_⟩
      · simp only [s.exsphere_center, s.exsphere_radius, hRn]
        exact h_dist
      · rw [hRn]
        positivity
      · rw [s.exsphere_radius]
        exact le_of_lt hex_pos
    · have hex_pos : 0 < s.exradius {1} := s.exradius_singleton_pos 1
      have h_nonneg : 0 ≤ R / 2 + s.exradius {1} := by positivity
      have h_dist : dist s.ninePointCircle.center (s.excenter {1}) =
          R / 2 + s.exradius {1} :=
        (sq_eq_sq₀ dist_nonneg h_nonneg).mp h_sq_ex1
      rw [EuclideanGeometry.Sphere.isExtTangent_iff_dist_center]
      refine ⟨?_, ?_, ?_⟩
      · simp only [s.exsphere_center, s.exsphere_radius, hRn]
        exact h_dist
      · rw [hRn]
        positivity
      · rw [s.exsphere_radius]
        exact le_of_lt hex_pos
    · have hex_pos : 0 < s.exradius {2} := s.exradius_singleton_pos 2
      have h_nonneg : 0 ≤ R / 2 + s.exradius {2} := by positivity
      have h_dist : dist s.ninePointCircle.center (s.excenter {2}) =
          R / 2 + s.exradius {2} :=
        (sq_eq_sq₀ dist_nonneg h_nonneg).mp h_sq_ex2
      rw [EuclideanGeometry.Sphere.isExtTangent_iff_dist_center]
      refine ⟨?_, ?_, ?_⟩
      · simp only [s.exsphere_center, s.exsphere_radius, hRn]
        exact h_dist
      · rw [hRn]
        positivity
      · rw [s.exsphere_radius]
        exact le_of_lt hex_pos

end MetaMathlibExt
end
