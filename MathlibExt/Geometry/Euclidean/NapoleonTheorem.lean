/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal

namespace MetaMathlibExt

@[expose] public section

private lemma dist_sq_coord (P Q : EuclideanSpace ℝ (Fin 2)) :
    dist P Q ^ 2 = (P.ofLp 0 - Q.ofLp 0) ^ 2 + (P.ofLp 1 - Q.ofLp 1) ^ 2 := by
  have h : ∀ i, ‖(P - Q).ofLp i‖ ^ 2 = (P.ofLp i - Q.ofLp i) ^ 2 := fun i => by
    rw [WithLp.ofLp_sub 2 P Q, Pi.sub_apply, Real.norm_eq_abs, sq_abs]
  rw [dist_eq_norm, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, h 0, h 1]

private lemma centroid_coord (B C D : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
    (((1 / 3 : ℝ) • (B + C + D)).ofLp i) = ((B.ofLp i + C.ofLp i + D.ofLp i) / 3) := by
  rw [WithLp.ofLp_smul 2, WithLp.ofLp_add 2, WithLp.ofLp_add 2]
  simp [Pi.smul_apply, Pi.add_apply]
  ring

private lemma apex_formula (bx byy cx cyy ax ay : ℝ)
    (h1 : (ax - bx) ^ 2 + (ay - byy) ^ 2 = (bx - cx) ^ 2 + (byy - cyy) ^ 2)
    (h2 : (ax - cx) ^ 2 + (ay - cyy) ^ 2 = (bx - cx) ^ 2 + (byy - cyy) ^ 2)
    (hS : (cx - bx) ^ 2 + (cyy - byy) ^ 2 ≠ 0) :
    ∃ s : ℝ, s ^ 2 = 1 ∧
      ax = (bx + cx) / 2 - s * (Real.sqrt 3 / 2) * (cyy - byy) ∧
      ay = (byy + cyy) / 2 + s * (Real.sqrt 3 / 2) * (cx - bx) := by
  have orth : (ax - (bx + cx) / 2) * (cx - bx) + (ay - (byy + cyy) / 2) * (cyy - byy) = 0 := by
    linear_combination (h1 - h2) / 2
  have normu : (ax - (bx + cx) / 2) ^ 2 + (ay - (byy + cyy) / 2) ^ 2
      = 3 * ((cx - bx) ^ 2 + (cyy - byy) ^ 2) / 4 := by
    linear_combination h1 - orth
  set S := (cx - bx) ^ 2 + (cyy - byy) ^ 2 with hSdef
  set N := (ax - (bx + cx) / 2) * (-(cyy - byy)) + (ay - (byy + cyy) / 2) * (cx - bx) with hNdef
  set t := N / S with htdef
  have htS : t * S = N := by rw [htdef]; exact div_mul_cancel₀ N hS
  have hNx : N * (-(cyy - byy)) - (ax - (bx + cx) / 2) * S
      = -(cx - bx) *
        ((ax - (bx + cx) / 2) * (cx - bx) + (ay - (byy + cyy) / 2) * (cyy - byy)) := by ring
  have htx : t * (-(cyy - byy)) = ax - (bx + cx) / 2 := by
    have h0 : (t * (-(cyy - byy)) - (ax - (bx + cx) / 2)) * S = 0 := by
      linear_combination (-(cyy - byy)) * htS - (cx - bx) * orth
    have hz := (mul_eq_zero.mp h0).resolve_right hS
    linear_combination hz
  have hNy : N * (cx - bx) - (ay - (byy + cyy) / 2) * S
      = -(cyy - byy) *
        ((ax - (bx + cx) / 2) * (cx - bx) + (ay - (byy + cyy) / 2) * (cyy - byy)) := by ring
  have huy : t * (cx - bx) = ay - (byy + cyy) / 2 := by
    have h0 : (t * (cx - bx) - (ay - (byy + cyy) / 2)) * S = 0 := by
      linear_combination (cx - bx) * htS - (cyy - byy) * orth
    have hz := (mul_eq_zero.mp h0).resolve_right hS
    linear_combination hz
  have hsub : (t * (-(cyy - byy))) ^ 2 + (t * (cx - bx)) ^ 2 = 3 * S / 4 := by
    rw [htx, huy]; exact normu
  have ht2 : t ^ 2 * S = 3 * S / 4 := by linear_combination hsub
  have ht2' : t ^ 2 = 3 / 4 := by
    have h0 : S * (t ^ 2 - 3 / 4) = 0 := by linear_combination ht2
    have hz := (mul_eq_zero.mp h0).resolve_left hS
    linear_combination hz
  set r := Real.sqrt 3 with hrdef
  have hr2 : r ^ 2 = 3 := by rw [hrdef]; exact Real.sq_sqrt (by norm_num)
  have hr0 : r ≠ 0 := by rw [hrdef]; exact (Real.sqrt_pos.mpr (by norm_num)).ne'
  have e : (t * 2 / r) ^ 2 * r ^ 2 = 4 * t ^ 2 := by
    rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero 2 hr0)]; ring
  have hs2 : (t * 2 / r) ^ 2 = 1 := by
    have h1 : (t * 2 / r) ^ 2 * r ^ 2 = 1 * r ^ 2 := by
      linear_combination e + 4 * ht2' - hr2
    exact mul_right_cancel₀ (pow_ne_zero 2 hr0) h1
  have hts : (t * 2 / r) * (r / 2) = t := by field_simp
  refine ⟨t * 2 / r, hs2, ?_, ?_⟩
  · have hax : ax - (bx + cx) / 2 = -((t * 2 / r) * (r / 2) * (cyy - byy)) := by
      linear_combination htx.symm + (cyy - byy) * hts
    linear_combination hax
  · have huy' : ay - (byy + cyy) / 2 = t * (cx - bx) := huy.symm
    have hay : ay - (byy + cyy) / 2 = (t * 2 / r) * (r / 2) * (cx - bx) := by
      linear_combination huy' - (cx - bx) * hts
    linear_combination hay

private lemma signs_equal (s1 s2 W : ℝ) (hs1 : s1 ^ 2 = 1) (hs2 : s2 ^ 2 = 1)
    (h1 : s1 * W < 0) (h2 : s2 * W < 0) : s1 = s2 := by
  have hWW : (s1 * W) * (s2 * W) > 0 := mul_pos_of_neg_of_neg h1 h2
  have e : (s1 * W) * (s2 * W) = W ^ 2 * (s1 * s2) := by ring
  rw [e] at hWW
  have hprod : s1 * s2 > 0 := pos_of_mul_pos_right hWW (sq_nonneg W)
  have hsq : (s1 * s2 - 1) * (s1 * s2 + 1) = 0 := by
    linear_combination s2 ^ 2 * hs1 + hs2
  have hne : s1 * s2 + 1 ≠ 0 := by
    have hgt : s1 * s2 + 1 > 0 := by linarith
    linarith
  have hz := (mul_eq_zero.mp hsq).resolve_right hne
  have hz1 : s1 * s2 = 1 := by linear_combination hz
  calc s1 = s1 * (s1 * s2) := by rw [hz1, mul_one]
    _ = s2 := by linear_combination s2 * hs1

private lemma napoleon_final
    (ax ay bx byy cx cyy a2x a2y b2x b2y c2x c2y g1x g1y g2x g2y g3x g3y s r : ℝ)
    (hs : s ^ 2 = 1) (hr : r ^ 2 = 3)
    (hA2x : a2x = (bx + cx) / 2 - s * (r / 2) * (cyy - byy))
    (hA2y : a2y = (byy + cyy) / 2 + s * (r / 2) * (cx - bx))
    (hB2x : b2x = (cx + ax) / 2 - s * (r / 2) * (ay - cyy))
    (hB2y : b2y = (cyy + ay) / 2 + s * (r / 2) * (ax - cx))
    (hC2x : c2x = (ax + bx) / 2 - s * (r / 2) * (byy - ay))
    (hC2y : c2y = (ay + byy) / 2 + s * (r / 2) * (bx - ax))
    (hG1x : g1x = (bx + cx + a2x) / 3) (hG1y : g1y = (byy + cyy + a2y) / 3)
    (hG2x : g2x = (cx + ax + b2x) / 3) (hG2y : g2y = (cyy + ay + b2y) / 3)
    (hG3x : g3x = (ax + bx + c2x) / 3) (hG3y : g3y = (ay + byy + c2y) / 3) :
    (g1x - g2x) ^ 2 + (g1y - g2y) ^ 2 = (g2x - g3x) ^ 2 + (g2y - g3y) ^ 2 ∧
    (g2x - g3x) ^ 2 + (g2y - g3y) ^ 2 = (g3x - g1x) ^ 2 + (g3y - g1y) ^ 2 := by
  simp only [hA2x, hA2y, hB2x, hB2y, hC2x, hC2y, hG1x, hG1y, hG2x, hG2y, hG3x, hG3y]
  set K := 2 * ((bx - ax) * (cx - ax) + (byy - ay) * (cyy - ay)) -
    ((cx - ax) ^ 2 + (cyy - ay) ^ 2) with hK
  set M := 2 * ((bx - ax) * (cx - ax) + (byy - ay) * (cyy - ay)) -
    ((bx - ax) ^ 2 + (byy - ay) ^ 2) with hM
  constructor
  · linear_combination (K * (-(r ^ 2) / 12)) * hs + (K * (-1 / 12)) * hr
  · linear_combination (M * (r ^ 2 / 12)) * hs + (M * (1 / 12)) * hr

private lemma napoleon_side_sq (ax ay bx byy cx cyy a2x a2y b2x b2y g1x g1y g2x g2y s r : ℝ)
    (hs : s ^ 2 = 1) (hr : r ^ 2 = 3)
    (hA2x : a2x = (bx + cx) / 2 - s * (r / 2) * (cyy - byy))
    (hA2y : a2y = (byy + cyy) / 2 + s * (r / 2) * (cx - bx))
    (hB2x : b2x = (cx + ax) / 2 - s * (r / 2) * (ay - cyy))
    (hB2y : b2y = (cyy + ay) / 2 + s * (r / 2) * (ax - cx))
    (hG1x : g1x = (bx + cx + a2x) / 3) (hG1y : g1y = (byy + cyy + a2y) / 3)
    (hG2x : g2x = (cx + ax + b2x) / 3) (hG2y : g2y = (cyy + ay + b2y) / 3) :
    (g1x - g2x) ^ 2 + (g1y - g2y) ^ 2 =
      ((bx - ax) ^ 2 + (byy - ay) ^ 2 + (cx - ax) ^ 2 + (cyy - ay) ^ 2
        - ((bx - ax) * (cx - ax) + (byy - ay) * (cyy - ay))) / 3
      - s * r * ((bx - ax) * (cyy - ay) - (byy - ay) * (cx - ax)) / 3 := by
  subst hG1x hG1y hG2x hG2y hA2x hA2y hB2x hB2y
  linear_combination (r ^ 2 * ((2 * cx - ax - bx) ^ 2 + (2 * cyy - ay - byy) ^ 2) / 36) * hs
    + (((2 * cx - ax - bx) ^ 2 + (2 * cyy - ay - byy) ^ 2) / 36) * hr

/-- **Napoleon's theorem, general form.** Let $A$, $B$, $C$, $A_2$, $B_2$, $C_2$ be points of the
Euclidean plane $\mathbb{R}^2$ with $|BA_2| = |CA_2| = |BC|$, $|CB_2| = |AB_2| = |CA|$ and
$|AC_2| = |BC_2| = |AB|$, such that $A_2$ and $A$ lie strictly on opposite sides of the line
$BC$, $B_2$ and $B$ lie strictly on opposite sides of the line $CA$, and $C_2$ and $C$ lie
strictly on opposite sides of the line $AB$. Let $G_1 = \frac{1}{3}(B + C + A_2)$,
$G_2 = \frac{1}{3}(C + A + B_2)$ and $G_3 = \frac{1}{3}(A + B + C_2)$. Then
$|G_1G_2| = |G_2G_3| = |G_3G_1| > 0$.

Thus the centroids $G_1$, $G_2$, $G_3$ of the equilateral triangles erected outward on the sides
of $ABC$ form a nondegenerate equilateral triangle; the hypotheses force $A$, $B$, $C$ to be
non-collinear. Opposite sides are expressed by signed areas, for instance
$((C - B) \times (A - B)) \, ((C - B) \times (A_2 - B)) < 0$, where
$(x, y) \times (x', y') = x y' - y x'$. -/
theorem napoleon_theorem_general (A B C A2 B2 C2 G1 G2 G3 : EuclideanSpace ℝ (Fin 2))
    (hBA2 : dist B A2 = dist B C) (hCA2 : dist C A2 = dist B C)
    (hCB2 : dist C B2 = dist C A) (hAB2 : dist A B2 = dist C A)
    (hAC2 : dist A C2 = dist A B) (hBC2 : dist B C2 = dist A B)
    (hout1 : ((C.ofLp 0 - B.ofLp 0) * (A.ofLp 1 - B.ofLp 1) -
          (C.ofLp 1 - B.ofLp 1) * (A.ofLp 0 - B.ofLp 0)) *
        ((C.ofLp 0 - B.ofLp 0) * (A2.ofLp 1 - B.ofLp 1) -
          (C.ofLp 1 - B.ofLp 1) * (A2.ofLp 0 - B.ofLp 0)) < 0)
    (hout2 : ((A.ofLp 0 - C.ofLp 0) * (B.ofLp 1 - C.ofLp 1) -
          (A.ofLp 1 - C.ofLp 1) * (B.ofLp 0 - C.ofLp 0)) *
        ((A.ofLp 0 - C.ofLp 0) * (B2.ofLp 1 - C.ofLp 1) -
          (A.ofLp 1 - C.ofLp 1) * (B2.ofLp 0 - C.ofLp 0)) < 0)
    (hout3 : ((B.ofLp 0 - A.ofLp 0) * (C.ofLp 1 - A.ofLp 1) -
          (B.ofLp 1 - A.ofLp 1) * (C.ofLp 0 - A.ofLp 0)) *
        ((B.ofLp 0 - A.ofLp 0) * (C2.ofLp 1 - A.ofLp 1) -
          (B.ofLp 1 - A.ofLp 1) * (C2.ofLp 0 - A.ofLp 0)) < 0)
    (hG1 : G1 = (1 / 3 : ℝ) • (B + C + A2))
    (hG2 : G2 = (1 / 3 : ℝ) • (C + A + B2))
    (hG3 : G3 = (1 / 3 : ℝ) • (A + B + C2)) :
    dist G1 G2 = dist G2 G3 ∧ dist G2 G3 = dist G3 G1 ∧ 0 < dist G1 G2 := by
  have hW := left_ne_zero_of_mul hout3.ne
  have hAB : A ≠ B := by rintro rfl; exact hW (by ring)
  have hBC : B ≠ C := by rintro rfl; exact hW (by ring)
  have hCA : C ≠ A := by rintro rfl; exact hW (by ring)
  set Ax := A.ofLp 0
  set Ay := A.ofLp 1
  set Bx := B.ofLp 0
  set Byy := B.ofLp 1
  set Cx := C.ofLp 0
  set Cyy := C.ofLp 1
  set A2x := A2.ofLp 0
  set A2y := A2.ofLp 1
  set B2x := B2.ofLp 0
  set B2y := B2.ofLp 1
  set C2x := C2.ofLp 0
  set C2y := C2.ofLp 1
  set G1x := G1.ofLp 0
  set G1y := G1.ofLp 1
  set G2x := G2.ofLp 0
  set G2y := G2.ofLp 1
  set G3x := G3.ofLp 0
  set G3y := G3.ofLp 1
  set W := (Bx - Ax) * (Cyy - Ay) - (Byy - Ay) * (Cx - Ax) with hWdef
  have eBC : dist B C ^ 2 = (Bx - Cx) ^ 2 + (Byy - Cyy) ^ 2 := dist_sq_coord B C
  have eCA : dist C A ^ 2 = (Cx - Ax) ^ 2 + (Cyy - Ay) ^ 2 := dist_sq_coord C A
  have eAB : dist A B ^ 2 = (Ax - Bx) ^ 2 + (Ay - Byy) ^ 2 := dist_sq_coord A B
  have hBCpos : 0 < (Bx - Cx) ^ 2 + (Byy - Cyy) ^ 2 := by
    rw [← eBC]; exact pow_pos (dist_pos.mpr hBC) 2
  have hCApos : 0 < (Cx - Ax) ^ 2 + (Cyy - Ay) ^ 2 := by
    rw [← eCA]; exact pow_pos (dist_pos.mpr hCA) 2
  have hABpos : 0 < (Ax - Bx) ^ 2 + (Ay - Byy) ^ 2 := by
    rw [← eAB]; exact pow_pos (dist_pos.mpr hAB) 2
  have hS1 : (Cx - Bx) ^ 2 + (Cyy - Byy) ^ 2 ≠ 0 := by
    have h : (Cx - Bx) ^ 2 + (Cyy - Byy) ^ 2 = (Bx - Cx) ^ 2 + (Byy - Cyy) ^ 2 := by ring
    rw [h]; exact ne_of_gt hBCpos
  have hS2 : (Ax - Cx) ^ 2 + (Ay - Cyy) ^ 2 ≠ 0 := by
    have h : (Ax - Cx) ^ 2 + (Ay - Cyy) ^ 2 = (Cx - Ax) ^ 2 + (Cyy - Ay) ^ 2 := by ring
    rw [h]; exact ne_of_gt hCApos
  have hS3 : (Bx - Ax) ^ 2 + (Byy - Ay) ^ 2 ≠ 0 := by
    have h : (Bx - Ax) ^ 2 + (Byy - Ay) ^ 2 = (Ax - Bx) ^ 2 + (Ay - Byy) ^ 2 := by ring
    rw [h]; exact ne_of_gt hABpos
  have eBA2 : dist B A2 ^ 2 = (Bx - A2x) ^ 2 + (Byy - A2y) ^ 2 := dist_sq_coord B A2
  have eCA2 : dist C A2 ^ 2 = (Cx - A2x) ^ 2 + (Cyy - A2y) ^ 2 := dist_sq_coord C A2
  have eCB2 : dist C B2 ^ 2 = (Cx - B2x) ^ 2 + (Cyy - B2y) ^ 2 := dist_sq_coord C B2
  have eAB2 : dist A B2 ^ 2 = (Ax - B2x) ^ 2 + (Ay - B2y) ^ 2 := dist_sq_coord A B2
  have eAC2 : dist A C2 ^ 2 = (Ax - C2x) ^ 2 + (Ay - C2y) ^ 2 := dist_sq_coord A C2
  have eBC2 : dist B C2 ^ 2 = (Bx - C2x) ^ 2 + (Byy - C2y) ^ 2 := dist_sq_coord B C2
  have qA1 : (A2x - Bx) ^ 2 + (A2y - Byy) ^ 2 = (Bx - Cx) ^ 2 + (Byy - Cyy) ^ 2 := by
    have h : dist B A2 ^ 2 = dist B C ^ 2 := by rw [hBA2]
    rw [eBA2, eBC] at h
    linear_combination h
  have qA2 : (A2x - Cx) ^ 2 + (A2y - Cyy) ^ 2 = (Bx - Cx) ^ 2 + (Byy - Cyy) ^ 2 := by
    have h : dist C A2 ^ 2 = dist B C ^ 2 := by rw [hCA2]
    rw [eCA2, eBC] at h
    linear_combination h
  have qB1 : (B2x - Cx) ^ 2 + (B2y - Cyy) ^ 2 = (Cx - Ax) ^ 2 + (Cyy - Ay) ^ 2 := by
    have h : dist C B2 ^ 2 = dist C A ^ 2 := by rw [hCB2]
    rw [eCB2, eCA] at h
    linear_combination h
  have qB2 : (B2x - Ax) ^ 2 + (B2y - Ay) ^ 2 = (Cx - Ax) ^ 2 + (Cyy - Ay) ^ 2 := by
    have h : dist A B2 ^ 2 = dist C A ^ 2 := by rw [hAB2]
    rw [eAB2, eCA] at h
    linear_combination h
  have qC1 : (C2x - Ax) ^ 2 + (C2y - Ay) ^ 2 = (Ax - Bx) ^ 2 + (Ay - Byy) ^ 2 := by
    have h : dist A C2 ^ 2 = dist A B ^ 2 := by rw [hAC2]
    rw [eAC2, eAB] at h
    linear_combination h
  have qC2 : (C2x - Bx) ^ 2 + (C2y - Byy) ^ 2 = (Ax - Bx) ^ 2 + (Ay - Byy) ^ 2 := by
    have h : dist B C2 ^ 2 = dist A B ^ 2 := by rw [hBC2]
    rw [eBC2, eAB] at h
    linear_combination h
  obtain ⟨s1, hs1, ha2x, ha2y⟩ := apex_formula Bx Byy Cx Cyy A2x A2y qA1 qA2 hS1
  obtain ⟨s2, hs2, hB2x, hB2y⟩ := apex_formula Cx Cyy Ax Ay B2x B2y qB1 qB2 hS2
  obtain ⟨s3, hs3, hC2x, hC2y⟩ := apex_formula Ax Ay Bx Byy C2x C2y qC1 qC2 hS3
  have hsqrt : 0 < Real.sqrt 3 / 2 :=
    div_pos (Real.sqrt_pos.mpr (show (0:ℝ) < 3 by norm_num)) (show (0:ℝ) < 2 by norm_num)
  have hS1pos : 0 < (Cx - Bx) ^ 2 + (Cyy - Byy) ^ 2 := by
    have h : (Cx - Bx) ^ 2 + (Cyy - Byy) ^ 2 = (Bx - Cx) ^ 2 + (Byy - Cyy) ^ 2 := by ring
    rw [h]; exact hBCpos
  have hS2pos : 0 < (Ax - Cx) ^ 2 + (Ay - Cyy) ^ 2 := by
    have h : (Ax - Cx) ^ 2 + (Ay - Cyy) ^ 2 = (Cx - Ax) ^ 2 + (Cyy - Ay) ^ 2 := by ring
    rw [h]; exact hCApos
  have hS3pos : 0 < (Bx - Ax) ^ 2 + (Byy - Ay) ^ 2 := by
    have h : (Bx - Ax) ^ 2 + (Byy - Ay) ^ 2 = (Ax - Bx) ^ 2 + (Ay - Byy) ^ 2 := by ring
    rw [h]; exact hABpos
  have eW1 : (Cx - Bx) * (Ay - Byy) - (Cyy - Byy) * (Ax - Bx) = W := by rw [hWdef]; ring
  have eW2 : (Ax - Cx) * (Byy - Cyy) - (Ay - Cyy) * (Bx - Cx) = W := by rw [hWdef]; ring
  have ecross1 : (Cx - Bx) * (A2y - Byy) - (Cyy - Byy) * (A2x - Bx)
      = s1 * (Real.sqrt 3 / 2) * ((Cx - Bx) ^ 2 + (Cyy - Byy) ^ 2) := by
    linear_combination (Cx - Bx) * ha2y - (Cyy - Byy) * ha2x
  have ecross2 : (Ax - Cx) * (B2y - Cyy) - (Ay - Cyy) * (B2x - Cx)
      = s2 * (Real.sqrt 3 / 2) * ((Ax - Cx) ^ 2 + (Ay - Cyy) ^ 2) := by
    linear_combination (Ax - Cx) * hB2y - (Ay - Cyy) * hB2x
  have ecross3 : (Bx - Ax) * (C2y - Ay) - (Byy - Ay) * (C2x - Ax)
      = s3 * (Real.sqrt 3 / 2) * ((Bx - Ax) ^ 2 + (Byy - Ay) ^ 2) := by
    linear_combination (Bx - Ax) * hC2y - (Byy - Ay) * hC2x
  rw [eW1, ecross1] at hout1
  rw [eW2, ecross2] at hout2
  rw [ecross3] at hout3
  have hsW1 : s1 * W < 0 := by
    by_contra hcon
    have hcon' : 0 ≤ s1 * W := not_lt.mp hcon
    have hnn : 0 ≤ (s1 * W) * ((Real.sqrt 3 / 2) * ((Cx - Bx) ^ 2 + (Cyy - Byy) ^ 2)) :=
      mul_nonneg hcon' (le_of_lt (mul_pos hsqrt hS1pos))
    have hneg : (s1 * W) * ((Real.sqrt 3 / 2) * ((Cx - Bx) ^ 2 + (Cyy - Byy) ^ 2)) < 0 := by
      linear_combination hout1
    linarith
  have hsW2 : s2 * W < 0 := by
    by_contra hcon
    have hcon' : 0 ≤ s2 * W := not_lt.mp hcon
    have hnn : 0 ≤ (s2 * W) * ((Real.sqrt 3 / 2) * ((Ax - Cx) ^ 2 + (Ay - Cyy) ^ 2)) :=
      mul_nonneg hcon' (le_of_lt (mul_pos hsqrt hS2pos))
    have hneg : (s2 * W) * ((Real.sqrt 3 / 2) * ((Ax - Cx) ^ 2 + (Ay - Cyy) ^ 2)) < 0 := by
      linear_combination hout2
    linarith
  have hsW3 : s3 * W < 0 := by
    by_contra hcon
    have hcon' : 0 ≤ s3 * W := not_lt.mp hcon
    have hnn : 0 ≤ (s3 * W) * ((Real.sqrt 3 / 2) * ((Bx - Ax) ^ 2 + (Byy - Ay) ^ 2)) :=
      mul_nonneg hcon' (le_of_lt (mul_pos hsqrt hS3pos))
    have hneg : (s3 * W) * ((Real.sqrt 3 / 2) * ((Bx - Ax) ^ 2 + (Byy - Ay) ^ 2)) < 0 := by
      linear_combination hout3
    linarith
  have hs12 : s1 = s2 := signs_equal s1 s2 W hs1 hs2 hsW1 hsW2
  have hs23 : s2 = s3 := signs_equal s2 s3 W hs2 hs3 hsW2 hsW3
  rw [← hs12] at hB2x hB2y
  rw [← hs23, ← hs12] at hC2x hC2y
  have hg1x : G1x = (Bx + Cx + A2x) / 3 := by
    have h := centroid_coord B C A2 (0 : Fin 2)
    rw [← hG1] at h
    exact h
  have hg1y : G1y = (Byy + Cyy + A2y) / 3 := by
    have h := centroid_coord B C A2 (1 : Fin 2)
    rw [← hG1] at h
    exact h
  have hg2x : G2x = (Cx + Ax + B2x) / 3 := by
    have h := centroid_coord C A B2 (0 : Fin 2)
    rw [← hG2] at h
    exact h
  have hg2y : G2y = (Cyy + Ay + B2y) / 3 := by
    have h := centroid_coord C A B2 (1 : Fin 2)
    rw [← hG2] at h
    exact h
  have hg3x : G3x = (Ax + Bx + C2x) / 3 := by
    have h := centroid_coord A B C2 (0 : Fin 2)
    rw [← hG3] at h
    exact h
  have hg3y : G3y = (Ay + Byy + C2y) / 3 := by
    have h := centroid_coord A B C2 (1 : Fin 2)
    rw [← hG3] at h
    exact h
  obtain ⟨hD12, hD23⟩ := napoleon_final Ax Ay Bx Byy Cx Cyy A2x A2y B2x B2y C2x C2y
    G1x G1y G2x G2y G3x G3y s1 (Real.sqrt 3) hs1 (Real.sq_sqrt (by norm_num))
    ha2x ha2y hB2x hB2y hC2x hC2y hg1x hg1y hg2x hg2y hg3x hg3y
  have eG12 : dist G1 G2 ^ 2 = (G1x - G2x) ^ 2 + (G1y - G2y) ^ 2 := dist_sq_coord G1 G2
  have eG23 : dist G2 G3 ^ 2 = (G2x - G3x) ^ 2 + (G2y - G3y) ^ 2 := dist_sq_coord G2 G3
  have eG31 : dist G3 G1 ^ 2 = (G3x - G1x) ^ 2 + (G3y - G1y) ^ 2 := dist_sq_coord G3 G1
  have q12 : dist G1 G2 ^ 2 = dist G2 G3 ^ 2 := by
    rw [eG12, eG23]; exact hD12
  have q23 : dist G2 G3 ^ 2 = dist G3 G1 ^ 2 := by
    rw [eG23, eG31]; exact hD23
  refine ⟨?_, ?_, ?_⟩
  · rcases sq_eq_sq_iff_eq_or_eq_neg.mp q12 with h | h'
    · exact h
    · have n1 : 0 ≤ dist G1 G2 := dist_nonneg
      have n2 : 0 ≤ dist G2 G3 := dist_nonneg
      linarith
  · rcases sq_eq_sq_iff_eq_or_eq_neg.mp q23 with h | h'
    · exact h
    · have n2 : 0 ≤ dist G2 G3 := dist_nonneg
      have n3 : 0 ≤ dist G3 G1 := dist_nonneg
      linarith
  · have hside := napoleon_side_sq Ax Ay Bx Byy Cx Cyy A2x A2y B2x B2y G1x G1y G2x G2y s1
      (Real.sqrt 3) hs1 (Real.sq_sqrt (by norm_num)) ha2x ha2y hB2x hB2y hg1x hg1y hg2x hg2y
    rw [← hWdef] at hside
    have hq : 0 ≤ (Bx - Ax) ^ 2 + (Byy - Ay) ^ 2 + (Cx - Ax) ^ 2 + (Cyy - Ay) ^ 2
        - ((Bx - Ax) * (Cx - Ax) + (Byy - Ay) * (Cyy - Ay)) := by
      have e : (Bx - Ax) ^ 2 + (Byy - Ay) ^ 2 + (Cx - Ax) ^ 2 + (Cyy - Ay) ^ 2
          - ((Bx - Ax) * (Cx - Ax) + (Byy - Ay) * (Cyy - Ay))
          = ((Bx - Ax) ^ 2 + (Cx - Ax) ^ 2 + (Bx - Cx) ^ 2 +
            (Byy - Ay) ^ 2 + (Cyy - Ay) ^ 2 + (Byy - Cyy) ^ 2) / 2 := by ring
      rw [e]; positivity
    have hm : 0 < -(s1 * W) * Real.sqrt 3 :=
      mul_pos (neg_pos.mpr hsW1) (Real.sqrt_pos.mpr (by norm_num))
    have h2 : 0 < dist G1 G2 ^ 2 := by
      rw [eG12, hside]
      linarith only [hq, hm]
    exact lt_of_le_of_ne dist_nonneg (fun h => by rw [← h] at h2; norm_num at h2)

/-- **Napoleon's theorem.** Let $A$, $B$, $C$ be pairwise distinct, non-collinear points of the
Euclidean plane $\mathbb{R}^2$, and let $A_2$, $B_2$, $C_2$ be points with
$|BA_2| = |CA_2| = |BC|$, $|CB_2| = |AB_2| = |CA|$ and $|AC_2| = |BC_2| = |AB|$, such that $A_2$
and $A$ lie strictly on opposite sides of the line $BC$, $B_2$ and $B$ lie strictly on opposite
sides of the line $CA$, and $C_2$ and $C$ lie strictly on opposite sides of the line $AB$. Let
$G_1 = \frac{1}{3}(B + C + A_2)$, $G_2 = \frac{1}{3}(C + A + B_2)$ and
$G_3 = \frac{1}{3}(A + B + C_2)$. Then $|G_1G_2| = |G_2G_3| = |G_3G_1|$.

That is, the centroids of the equilateral triangles erected outward on the sides of $ABC$ are
pairwise equidistant. Non-collinearity is stated as $(B - A) \times (C - A) \ne 0$ and opposite
sides by signed areas, for instance $((C - B) \times (A - B)) \, ((C - B) \times (A_2 - B)) < 0$,
where $(x, y) \times (x', y') = x y' - y x'$.

Source: https://en.wikipedia.org/wiki/Napoleon%27s_theorem (statement id `napoleon-s1`;
raw: "Outer equilateral-triangle centers on any triangle form an equilateral triangle.").
It follows from `napoleon_theorem_general`, which also shows the common distance is positive;
the hypotheses `A ≠ B`, `B ≠ C`, `C ≠ A` and nondegeneracy are unused and keep the source's
shape.
Proves `Wanted` entry `napoleon_theorem`.
-/
theorem napoleon_theorem :
    ∀ (A B C A2 B2 C2 G1 G2 G3 : EuclideanSpace ℝ (Fin 2)),
      A ≠ B → B ≠ C → C ≠ A →
      ((B.ofLp 0 - A.ofLp 0) * (C.ofLp 1 - A.ofLp 1) -
          (B.ofLp 1 - A.ofLp 1) * (C.ofLp 0 - A.ofLp 0) ≠ 0) →
      dist B A2 = dist B C → dist C A2 = dist B C →
      dist C B2 = dist C A → dist A B2 = dist C A →
      dist A C2 = dist A B → dist B C2 = dist A B →
      (((C.ofLp 0 - B.ofLp 0) * (A.ofLp 1 - B.ofLp 1) -
            (C.ofLp 1 - B.ofLp 1) * (A.ofLp 0 - B.ofLp 0)) *
          ((C.ofLp 0 - B.ofLp 0) * (A2.ofLp 1 - B.ofLp 1) -
            (C.ofLp 1 - B.ofLp 1) * (A2.ofLp 0 - B.ofLp 0)) < 0) →
      (((A.ofLp 0 - C.ofLp 0) * (B.ofLp 1 - C.ofLp 1) -
            (A.ofLp 1 - C.ofLp 1) * (B.ofLp 0 - C.ofLp 0)) *
          ((A.ofLp 0 - C.ofLp 0) * (B2.ofLp 1 - C.ofLp 1) -
            (A.ofLp 1 - C.ofLp 1) * (B2.ofLp 0 - C.ofLp 0)) < 0) →
      (((B.ofLp 0 - A.ofLp 0) * (C.ofLp 1 - A.ofLp 1) -
            (B.ofLp 1 - A.ofLp 1) * (C.ofLp 0 - A.ofLp 0)) *
          ((B.ofLp 0 - A.ofLp 0) * (C2.ofLp 1 - A.ofLp 1) -
            (B.ofLp 1 - A.ofLp 1) * (C2.ofLp 0 - A.ofLp 0)) < 0) →
      G1 = (1 / 3 : ℝ) • (B + C + A2) →
      G2 = (1 / 3 : ℝ) • (C + A + B2) →
      G3 = (1 / 3 : ℝ) • (A + B + C2) →
      dist G1 G2 = dist G2 G3 ∧ dist G2 G3 = dist G3 G1 := by
  intro A B C A2 B2 C2 G1 G2 G3 _ _ _ _ hBA2 hCA2 hCB2 hAB2 hAC2 hBC2 hout1 hout2 hout3
    hG1 hG2 hG3
  obtain ⟨h12, h23, -⟩ := napoleon_theorem_general A B C A2 B2 C2 G1 G2 G3 hBA2 hCA2 hCB2
    hAB2 hAC2 hBC2 hout1 hout2 hout3 hG1 hG2 hG3
  exact ⟨h12, h23⟩

end

end MetaMathlibExt
