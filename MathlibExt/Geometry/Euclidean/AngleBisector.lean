/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.Geometry.Euclidean.Triangle

@[expose] public section

namespace MetaMathlibExt

/-- **Angle bisector theorem without distinctness hypotheses.** Let $A$, $B$, $C$, $D$ be points of
a Euclidean affine space (a metric affine space over a real inner product space) with $A$, $B$, $C$
affinely independent, so that $ABC$ is a nondegenerate triangle. If $D$ lies strictly between $B$
and $C$ and $\angle BAD = \angle DAC$ (unoriented angles), then $BD / DC = AB / AC$.

The hypotheses $A \ne B$, $A \ne C$ and $A \ne D$ of the usual statement are not needed: they
follow from the others. -/
theorem angle_bisector_theorem_general {V P : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P]
    (A B C D : P)
    (h_tri : AffineIndependent ℝ
      (fun i : Fin 3 => if i = 0 then A else if i = 1 then B else C))
    (h_bet : Sbtw ℝ B D C)
    (h_bis : EuclideanGeometry.angle B A D = EuclideanGeometry.angle D A C) :
    dist B D / dist D C = dist A B / dist A C := by
  have hAB : A ≠ B := by
    intro h
    have h01 : (0 : Fin 3) = 1 := h_tri.injective (by simpa using h)
    exact (by decide : (0 : Fin 3) ≠ 1) h01
  have hAC : A ≠ C := by
    intro h
    have h02 : (0 : Fin 3) = 2 := h_tri.injective (by simpa using h)
    exact (by decide : (0 : Fin 3) ≠ 2) h02
  have himg2 : (fun i : Fin 3 => if i = 0 then A else if i = 1 then B else C) ''
      (Set.univ \ {(2 : Fin 3)}) = {A, B} := by
    ext x
    simp only [Set.mem_image, Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩
      fin_cases i <;> simp_all
    · rintro (rfl | rfl)
      · exact ⟨0, by decide, by simp⟩
      · exact ⟨1, by decide, by simp⟩
  have himg1 : (fun i : Fin 3 => if i = 0 then A else if i = 1 then B else C) ''
      (Set.univ \ {(1 : Fin 3)}) = {A, C} := by
    ext x
    simp only [Set.mem_image, Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩
      fin_cases i <;> simp_all
    · rintro (rfl | rfl)
      · exact ⟨0, by decide, by simp⟩
      · exact ⟨2, by decide, by simp⟩
  have hC_notmem : C ∉ affineSpan ℝ ({A, B} : Set P) := by
    have h := h_tri.notMem_affineSpan_sdiff (2 : Fin 3) Set.univ
    rw [himg2] at h
    simpa using h
  have hB_notmem : B ∉ affineSpan ℝ ({A, C} : Set P) := by
    have h := h_tri.notMem_affineSpan_sdiff (1 : Fin 3) Set.univ
    rw [himg1] at h
    simpa using h
  have hBD : B ≠ D := fun h => h_bet.ne_left h.symm
  have hDC : D ≠ C := h_bet.ne_right
  have hCD : C ≠ D := fun h => h_bet.ne_right h.symm
  have hBC : B ≠ C := by
    intro h
    have hinj := h_tri.injective
    have h12 : (1 : Fin 3) = 2 := hinj (by simpa using h)
    exact (by decide : (1 : Fin 3) ≠ 2) h12
  have hcolBDC : Collinear ℝ ({B, D, C} : Set P) := h_bet.wbtw.collinear
  have hABC : ¬ Collinear ℝ ({A, B, C} : Set P) := by
    intro hcol
    have hCmem : C ∈ affineSpan ℝ ({A, B} : Set P) :=
      hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hAB
    exact hC_notmem hCmem
  have hABD : ¬ Collinear ℝ ({A, B, D} : Set P) := by
    intro hcol
    have hDmem : D ∈ affineSpan ℝ ({A, B} : Set P) :=
      hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hAB
    have hCmemBD : C ∈ affineSpan ℝ ({B, D} : Set P) :=
      hcolBDC.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hBD
    have hsub : ({B, D} : Set P) ⊆ affineSpan ℝ ({A, B} : Set P) := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact mem_affineSpan ℝ (by simp)
      · exact hDmem
    have hCmem : C ∈ affineSpan ℝ ({A, B} : Set P) := affineSpan_le.mpr hsub hCmemBD
    exact hC_notmem hCmem
  have hACD : ¬ Collinear ℝ ({A, C, D} : Set P) := by
    intro hcol
    have hDmem : D ∈ affineSpan ℝ ({A, C} : Set P) :=
      hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hAC
    have hBmemCD : B ∈ affineSpan ℝ ({C, D} : Set P) :=
      hcolBDC.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hCD
    have hsub : ({C, D} : Set P) ⊆ affineSpan ℝ ({A, C} : Set P) := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact mem_affineSpan ℝ (by simp)
      · exact hDmem
    have hBmem : B ∈ affineSpan ℝ ({A, C} : Set P) := affineSpan_le.mpr hsub hBmemCD
    exact hB_notmem hBmem
  have setCAB : ({C, A, B} : Set P) = {A, B, C} := by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have setACB : ({A, C, B} : Set P) = {A, B, C} := by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have hCAB : ¬ Collinear ℝ ({C, A, B} : Set P) := setCAB.symm ▸ hABC
  have hACB : ¬ Collinear ℝ ({A, C, B} : Set P) := setACB.symm ▸ hABC
  have h1 : EuclideanGeometry.angle A B D = EuclideanGeometry.angle A B C :=
    Sbtw.angle_eq_right A h_bet
  have h2 : EuclideanGeometry.angle A C D = EuclideanGeometry.angle A C B :=
    Sbtw.angle_eq_right A h_bet.symm
  have e1 := EuclideanGeometry.law_sin (V := V) (P := P) A B D
  have e2 := EuclideanGeometry.law_sin (V := V) (P := P) A C D
  have e3 := EuclideanGeometry.law_sin (V := V) (P := P) C A B
  have e4 := EuclideanGeometry.law_sin (V := V) (P := P) B A C
  have sB_ne : Real.sin (EuclideanGeometry.angle A B C) ≠ 0 :=
    EuclideanGeometry.sin_ne_zero_of_not_collinear hABC
  have sC_ne : Real.sin (EuclideanGeometry.angle A C B) ≠ 0 :=
    EuclideanGeometry.sin_ne_zero_of_not_collinear hACB
  have sCAB_ne : Real.sin (EuclideanGeometry.angle C A B) ≠ 0 :=
    EuclideanGeometry.sin_ne_zero_of_not_collinear hCAB
  have hBDne : dist B D ≠ 0 := dist_ne_zero.mpr hBD
  have hDCne : dist D C ≠ 0 := dist_ne_zero.mpr hDC
  have hABne : dist A B ≠ 0 := dist_ne_zero.mpr hAB
  have hACne : dist A C ≠ 0 := dist_ne_zero.mpr hAC
  have hBCne : dist B C ≠ 0 := dist_ne_zero.mpr hBC
  have hsABD : Real.sin (EuclideanGeometry.angle A B D) =
      Real.sin (EuclideanGeometry.angle A B C) := by
    rw [h1]
  have hsACD : Real.sin (EuclideanGeometry.angle A C D) =
      Real.sin (EuclideanGeometry.angle A C B) := by
    rw [h2]
  have hbis_sin : Real.sin (EuclideanGeometry.angle D A B) =
      Real.sin (EuclideanGeometry.angle D A C) := by
    rw [EuclideanGeometry.angle_comm D A B, h_bis]
  have hsCAB_BAC : Real.sin (EuclideanGeometry.angle C A B) =
      Real.sin (EuclideanGeometry.angle B A C) := by
    rw [EuclideanGeometry.angle_comm C A B]
  have hsBCA : Real.sin (EuclideanGeometry.angle B C A) =
      Real.sin (EuclideanGeometry.angle A C B) := by
    rw [EuclideanGeometry.angle_comm B C A]
  have hsCBA : Real.sin (EuclideanGeometry.angle C B A) =
      Real.sin (EuclideanGeometry.angle A B C) := by
    rw [EuclideanGeometry.angle_comm C B A]
  have hBCcomm : dist B C = dist C B := dist_comm B C
  have hCDcomm : dist C D = dist D C := dist_comm C D
  have hX : Real.sin (EuclideanGeometry.angle A B C) * dist B D =
      Real.sin (EuclideanGeometry.angle A C B) * dist D C := by
    have g1 : Real.sin (EuclideanGeometry.angle A B C) * dist B D =
        Real.sin (EuclideanGeometry.angle D A B) * dist D A := by
      rw [← hsABD]; exact e1
    have g2 : Real.sin (EuclideanGeometry.angle A C B) * dist D C =
        Real.sin (EuclideanGeometry.angle D A C) * dist D A := by
      rw [← hsACD, ← hCDcomm]; exact e2
    rw [g1, g2, hbis_sin]
  have hY : dist A B / dist A C =
      Real.sin (EuclideanGeometry.angle A C B) / Real.sin (EuclideanGeometry.angle A B C) := by
    have g3 : Real.sin (EuclideanGeometry.angle C A B) * dist A B =
        Real.sin (EuclideanGeometry.angle A C B) * dist B C := by
      rw [← hsBCA]; exact e3
    have g4 : Real.sin (EuclideanGeometry.angle B A C) * dist A C =
        Real.sin (EuclideanGeometry.angle A B C) * dist C B := by
      rw [← hsCBA]; exact e4
    have key : dist A B * Real.sin (EuclideanGeometry.angle A B C) =
        dist A C * Real.sin (EuclideanGeometry.angle A C B) := by
      have r1 : Real.sin (EuclideanGeometry.angle C A B) *
          (dist A B * Real.sin (EuclideanGeometry.angle A B C)) =
          Real.sin (EuclideanGeometry.angle C A B) *
          (dist A C * Real.sin (EuclideanGeometry.angle A C B)) := by
        calc Real.sin (EuclideanGeometry.angle C A B) *
                (dist A B * Real.sin (EuclideanGeometry.angle A B C))
            = (Real.sin (EuclideanGeometry.angle C A B) * dist A B) *
                Real.sin (EuclideanGeometry.angle A B C) := by ring
          _ = (Real.sin (EuclideanGeometry.angle A C B) * dist B C) *
                Real.sin (EuclideanGeometry.angle A B C) := by rw [g3]
          _ = (Real.sin (EuclideanGeometry.angle A C B)) *
                (Real.sin (EuclideanGeometry.angle A B C) * dist B C) := by ring
          _ = (Real.sin (EuclideanGeometry.angle A C B)) *
                (Real.sin (EuclideanGeometry.angle A B C) * dist C B) := by rw [hBCcomm]
          _ = (Real.sin (EuclideanGeometry.angle A C B)) *
                (Real.sin (EuclideanGeometry.angle B A C) * dist A C) := by rw [← g4]
          _ = Real.sin (EuclideanGeometry.angle C A B) *
                (dist A C * Real.sin (EuclideanGeometry.angle A C B)) := by
                rw [hsCAB_BAC]; ring
      exact mul_left_cancel₀ sCAB_ne r1
    rw [div_eq_div_iff hACne sB_ne]
    linarith [key]
  rw [hY]
  rw [div_eq_div_iff hDCne sB_ne]
  linarith [hX]

set_option linter.unusedVariables false in
/-- **Angle bisector theorem.** Let $A$, $B$, $C$, $D$ be points of a Euclidean affine space (a
metric affine space over a real inner product space) with $A$, $B$, $C$ affinely independent, so
that $ABC$ is a nondegenerate triangle, and with $A \ne B$, $A \ne C$ and $A \ne D$. If $D$ lies
strictly between $B$ and $C$ and $\angle BAD = \angle DAC$ (unoriented angles), then
$BD / DC = AB / AC$.

Source: https://en.wikipedia.org/wiki/Angle_bisector_theorem
(statement_id `angle-bisector-theorem`, required clause 1).
It follows from `angle_bisector_theorem_general`; the hypotheses `hAB`, `hAC` and `hAD` are
unused and keep the source's shape.
Proves `Wanted` entry `angle_bisector_theorem`. -/
@[nolint unusedArguments]
theorem angle_bisector_theorem {V P : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P]
    (A B C D : P)
    (h_tri : AffineIndependent ℝ
      (fun i : Fin 3 => if i = 0 then A else if i = 1 then B else C))
    (hAB : A ≠ B) (hAC : A ≠ C) (hAD : A ≠ D)
    (h_bet : Sbtw ℝ B D C)
    (h_bis : EuclideanGeometry.angle B A D = EuclideanGeometry.angle D A C) :
    dist B D / dist D C = dist A B / dist A C :=
  angle_bisector_theorem_general A B C D h_tri h_bet h_bis

/-- **Converse of the angle bisector theorem without distinctness hypotheses.** Let $A$, $B$, $C$,
$D$ be points of a Euclidean affine space (a metric affine space over a real inner product space)
with $A$, $B$, $C$ affinely independent, so that $ABC$ is a nondegenerate triangle. If $D$ lies on
the closed segment $BC$ and $BD / DC = AB / AC$, then $\angle BAD = \angle DAC$ (unoriented
angles), that is, $D$ lies on the internal bisector of the angle at $A$.

The hypotheses $A \ne B$, $A \ne C$ and $A \ne D$ of the usual statement are not needed: they
follow from the others. -/
theorem angle_bisector_converse_general {V P : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P]
    (A B C D : P)
    (h_tri : AffineIndependent ℝ
      (fun i : Fin 3 => if i = 0 then A else if i = 1 then B else C))
    (h_bet : Wbtw ℝ B D C)
    (h_ratio : dist B D / dist D C = dist A B / dist A C) :
    EuclideanGeometry.angle B A D = EuclideanGeometry.angle D A C := by
  have hAB : A ≠ B := by
    intro h
    have h01 : (0 : Fin 3) = 1 := h_tri.injective (by simpa using h)
    exact (by decide : (0 : Fin 3) ≠ 1) h01
  have hAC : A ≠ C := by
    intro h
    have h02 : (0 : Fin 3) = 2 := h_tri.injective (by simpa using h)
    exact (by decide : (0 : Fin 3) ≠ 2) h02
  have hAD : A ≠ D := by
    have himg0 : (fun i : Fin 3 => if i = 0 then A else if i = 1 then B else C) ''
        (Set.univ \ {(0 : Fin 3)}) = {B, C} := by
      ext x
      simp only [Set.mem_image, Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and]
      constructor
      · rintro ⟨i, hi, rfl⟩
        fin_cases i <;> simp_all
      · rintro (rfl | rfl)
        · exact ⟨1, by decide, by simp⟩
        · exact ⟨2, by decide, by simp⟩
    have hA_notmem : A ∉ affineSpan ℝ ({B, C} : Set P) := by
      have h := h_tri.notMem_affineSpan_sdiff (0 : Fin 3) Set.univ
      rw [himg0] at h
      simpa using h
    rintro rfl
    exact hA_notmem h_bet.mem_affineSpan
  have hBC : B ≠ C := by
    have h12 : (1 : Fin 3) ≠ 2 := by decide
    have h := h_tri.injective.ne h12
    simp only [ne_eq] at h
    exact h
  have hbB : B -ᵥ A ≠ 0 := fun h => hAB ((vsub_eq_zero_iff_eq.mp h).symm)
  have hcC : C -ᵥ A ≠ 0 := fun h => hAC ((vsub_eq_zero_iff_eq.mp h).symm)
  have hdD : D -ᵥ A ≠ 0 := fun h => hAD ((vsub_eq_zero_iff_eq.mp h).symm)
  have hCB : C -ᵥ B ≠ 0 := fun h => hBC.symm (vsub_eq_zero_iff_eq.mp h)
  have hnB : 0 < ‖B -ᵥ A‖ := norm_pos_iff.mpr hbB
  have hnC : 0 < ‖C -ᵥ A‖ := norm_pos_iff.mpr hcC
  have hW : 0 < ‖C -ᵥ B‖ := norm_pos_iff.mpr hCB
  obtain ⟨t, ht, hDt⟩ := h_bet
  rw [Set.mem_Icc] at ht
  obtain ⟨ht0, ht1⟩ := ht
  have hDB : D -ᵥ B = t • (C -ᵥ B) := by
    rw [← hDt]
    exact AffineMap.lineMap_vsub_left B C t
  have hCD : C -ᵥ D = (1 - t) • (C -ᵥ B) := by
    rw [← hDt]
    exact AffineMap.right_vsub_lineMap B C t
  have eBD : dist B D = t * ‖C -ᵥ B‖ := by
    rw [dist_eq_norm_vsub', hDB, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht0]
  have eDC : dist D C = (1 - t) * ‖C -ᵥ B‖ := by
    rw [dist_eq_norm_vsub', hCD, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr ht1)]
  have hposn : 0 < ‖B -ᵥ A‖ / ‖C -ᵥ A‖ := div_pos hnB hnC
  rw [eBD, eDC, dist_eq_norm_vsub', dist_eq_norm_vsub'] at h_ratio
  have ht0' : t ≠ 0 := by
    intro h
    subst h
    simp only [sub_zero, zero_mul, zero_div] at h_ratio
    rw [h_ratio] at hposn
    exact lt_irrefl _ hposn
  have ht1' : t ≠ 1 := by
    intro h
    subst h
    simp only [sub_self, zero_mul, div_zero] at h_ratio
    rw [h_ratio] at hposn
    exact lt_irrefl _ hposn
  have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht0')
  have htlt1 : t < 1 := lt_of_le_of_ne ht1 ht1'
  have h1t : 0 < 1 - t := sub_pos.mpr htlt1
  have hWne : ‖C -ᵥ B‖ ≠ 0 := ne_of_gt hW
  have hnBne : ‖B -ᵥ A‖ ≠ 0 := ne_of_gt hnB
  have hnCne : ‖C -ᵥ A‖ ≠ 0 := ne_of_gt hnC
  have h1tne : (1 - t) ≠ 0 := ne_of_gt h1t
  have hratio : t / (1 - t) = ‖B -ᵥ A‖ / ‖C -ᵥ A‖ := by
    have h := h_ratio
    rwa [mul_div_mul_right _ _ hWne] at h
  have hsum : (‖B -ᵥ A‖ + ‖C -ᵥ A‖) ≠ 0 :=
    ne_of_gt (add_pos hnB hnC)
  have ht_eq : t = ‖B -ᵥ A‖ / (‖B -ᵥ A‖ + ‖C -ᵥ A‖) := by
    rw [div_eq_div_iff h1tne hnCne] at hratio
    rw [eq_div_iff hsum]
    linear_combination hratio
  have hDA : D -ᵥ A = (1 - t) • (B -ᵥ A) + t • (C -ᵥ A) := by
    have h := AffineMap.lineMap_vsub_lineMap B C A A t
    rw [AffineMap.lineMap_same_apply A t, hDt] at h
    rw [h]
    exact AffineMap.lineMap_apply_module _ _ _
  set S := ‖C -ᵥ A‖ • (B -ᵥ A) + ‖B -ᵥ A‖ • (C -ᵥ A) with hSdef
  have hsum_pos : 0 < ‖B -ᵥ A‖ + ‖C -ᵥ A‖ := add_pos hnB hnC
  have hDβ : D -ᵥ A = (‖B -ᵥ A‖ + ‖C -ᵥ A‖)⁻¹ • S := by
    rw [hDA, ht_eq, hSdef]
    have h1 : 1 - ‖B -ᵥ A‖ / (‖B -ᵥ A‖ + ‖C -ᵥ A‖)
        = ‖C -ᵥ A‖ / (‖B -ᵥ A‖ + ‖C -ᵥ A‖) := by
      field_simp
      ring
    rw [h1, div_eq_inv_mul, div_eq_inv_mul, smul_add, ← mul_smul, ← mul_smul,
      mul_comm ((‖B -ᵥ A‖ + ‖C -ᵥ A‖)⁻¹), mul_comm ((‖B -ᵥ A‖ + ‖C -ᵥ A‖)⁻¹)]
  have hβ : 0 < (‖B -ᵥ A‖ + ‖C -ᵥ A‖)⁻¹ := inv_pos.mpr hsum_pos
  have hSne : S ≠ 0 := by
    intro h
    rw [h, smul_zero] at hDβ
    exact hdD hDβ
  have hnS : ‖S‖ ≠ 0 := fun h => hSne (norm_eq_zero.mp h)
  have e_left : InnerProductGeometry.angle (B -ᵥ A) (D -ᵥ A)
      = InnerProductGeometry.angle (B -ᵥ A) S := by
    rw [hDβ]
    exact InnerProductGeometry.angle_smul_right_of_pos _ _ hβ
  have e_right : InnerProductGeometry.angle (D -ᵥ A) (C -ᵥ A)
      = InnerProductGeometry.angle S (C -ᵥ A) := by
    rw [hDβ]
    exact InnerProductGeometry.angle_smul_left_of_pos _ _ hβ
  have key : inner ℝ (B -ᵥ A) S * ‖C -ᵥ A‖
      = inner ℝ S (C -ᵥ A) * ‖B -ᵥ A‖ := by
    simp only [hSdef, inner_add_left, inner_add_right, real_inner_smul_left,
      inner_smul_right, real_inner_self_eq_norm_mul_norm,
      real_inner_comm (C -ᵥ A) (B -ᵥ A)]
    ring
  have hcos : inner ℝ (B -ᵥ A) S / (‖B -ᵥ A‖ * ‖S‖)
      = inner ℝ S (C -ᵥ A) / (‖S‖ * ‖C -ᵥ A‖) := by
    rw [div_eq_div_iff (mul_ne_zero hnBne hnS) (mul_ne_zero hnS hnCne)]
    linear_combination key * ‖S‖
  simp only [EuclideanGeometry.angle]
  rw [e_left, e_right]
  unfold InnerProductGeometry.angle
  rw [hcos]

set_option linter.unusedVariables false in
/-- **Converse of the angle bisector theorem.** Let $A$, $B$, $C$, $D$ be points of a Euclidean
affine space (a metric affine space over a real inner product space) with $A$, $B$, $C$ affinely
independent, so that $ABC$ is a nondegenerate triangle, and with $A \ne B$, $A \ne C$ and
$A \ne D$. If $D$ lies on the closed segment $BC$ and $BD / DC = AB / AC$, then
$\angle BAD = \angle DAC$ (unoriented angles), that is, $D$ lies on the internal bisector of the
angle at $A$.

Source: https://en.wikipedia.org/wiki/Angle_bisector_theorem
(statement_id `angle-bisector-theorem`, required clause 2).
It follows from `angle_bisector_converse_general`; the hypotheses `hAB`, `hAC` and `hAD` are
unused and keep the source's shape.
Proves `Wanted` entry `angle_bisector_converse`. -/
@[nolint unusedArguments]
theorem angle_bisector_converse {V P : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P]
    (A B C D : P)
    (h_tri : AffineIndependent ℝ
      (fun i : Fin 3 => if i = 0 then A else if i = 1 then B else C))
    (hAB : A ≠ B) (hAC : A ≠ C) (hAD : A ≠ D)
    (h_bet : Wbtw ℝ B D C)
    (h_ratio : dist B D / dist D C = dist A B / dist A C) :
    EuclideanGeometry.angle B A D = EuclideanGeometry.angle D A C :=
  angle_bisector_converse_general A B C D h_tri h_bet h_ratio

end MetaMathlibExt
