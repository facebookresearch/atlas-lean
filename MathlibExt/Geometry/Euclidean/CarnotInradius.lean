/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

section
namespace MetaMathlibExt

private theorem orth_eq_aux
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [Fact (Module.finrank ℝ V = 2)]
    (u n : V) (hu : u ≠ 0) (hn : ‖n‖ = 1) (hun : inner (𝕜 := ℝ) u n = 0)
    (w : V) (hw : inner (𝕜 := ℝ) u w = 0) :
    w = (inner (𝕜 := ℝ) w n) • n := by
  have h2 : Module.finrank ℝ V = 1 + 1 := by have h : Module.finrank ℝ V = 2 := Fact.out; omega
  have : Fact (Module.finrank ℝ V = 1 + 1) := Fact.mk h2
  have hfr := Submodule.finrank_orthogonal_span_singleton (𝕜 := ℝ) (E := V) (n := 1) (v := u) hu
  have hfin : Module.finrank ℝ ((ℝ ∙ u)ᗮ) = 1 := hfr
  rw [finrank_eq_one_iff'] at hfin
  obtain ⟨g, hg0, hg⟩ := hfin
  have hnmem : n ∈ (ℝ ∙ u)ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]; exact hun
  have hwmem : w ∈ (ℝ ∙ u)ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]; exact hw
  have hn0 : n ≠ 0 := by intro h0; rw [h0, norm_zero] at hn; norm_num at hn
  obtain ⟨c, hc⟩ := hg ⟨n, hnmem⟩
  obtain ⟨d, hd⟩ := hg ⟨w, hwmem⟩
  have hnc : c • (g : V) = n := by have := congrArg Subtype.val hc; simpa using this
  have hwd : d • (g : V) = w := by have := congrArg Subtype.val hd; simpa using this
  have hc0 : c ≠ 0 := by intro h0; rw [h0, zero_smul] at hnc; exact hn0 hnc.symm
  have hnn : inner (𝕜 := ℝ) n n = 1 := by rw [real_inner_self_eq_norm_sq, hn, one_pow]
  have hgw : (g : V) = c⁻¹ • n := by
    have h1 : (c⁻¹ * c) • (g : V) = (g : V) := by rw [inv_mul_cancel₀ hc0, one_smul]
    rw [mul_smul, hnc] at h1; exact h1.symm
  have hw2 : w = (d * c⁻¹) • n := by
    have h1 : (d * c⁻¹) • n = d • (c⁻¹ • n) := by rw [mul_smul]
    rw [h1, ← hgw, ← hwd]
  have hcoeff : d * c⁻¹ = inner (𝕜 := ℝ) w n := by
    rw [hw2, inner_smul_left, hnn]; simp
  rw [← hcoeff]; exact hw2

private theorem gram_aux
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [Fact (Module.finrank ℝ V = 2)]
    (u n : V) (hu : u ≠ 0) (hn : ‖n‖ = 1) (hun : inner (𝕜 := ℝ) u n = 0)
    (w : V) :
    ‖u‖^2 * ‖w‖^2 = (inner (𝕜 := ℝ) u w)^2 + ‖u‖^2 * (inner (𝕜 := ℝ) w n)^2 := by
  have hunorm : ‖u‖ ≠ 0 := by intro h0; apply hu; rw [← norm_eq_zero]; exact h0
  have hs : (‖u‖^2 : ℝ) ≠ 0 := by positivity
  set s := ‖u‖^2 with hsdef
  set c := (inner (𝕜 := ℝ) u w) / s with hcdef
  set w1 := w - c • u with hw1def
  have huw1 : inner (𝕜 := ℝ) u w1 = 0 := by
    rw [hw1def, inner_sub_right, inner_smul_right]
    rw [real_inner_self_eq_norm_sq]
    rw [hcdef]
    field_simp
    ring
  have hw1eq0 := orth_eq_aux u n hu hn hun w1 huw1
  have hwn1 : inner (𝕜 := ℝ) w1 n = inner (𝕜 := ℝ) w n := by
    rw [hw1def, inner_sub_left, inner_smul_left]
    simp [hun]
  rw [hwn1] at hw1eq0
  have hwdecomp : w = c • u + (inner (𝕜 := ℝ) w n) • n := by
    have hww1 : w = c • u + w1 := by rw [hw1def]; abel
    conv_lhs => rw [hww1, hw1eq0]
  have horth : inner (𝕜 := ℝ) (c • u) ((inner (𝕜 := ℝ) w n) • n) = 0 := by
    rw [inner_smul_left, inner_smul_right, hun]
    simp
  have hnorm : ‖w‖^2 = ‖c • u‖^2 + ‖(inner (𝕜 := ℝ) w n) • n‖^2 := by
    conv_lhs => rw [hwdecomp]
    rw [norm_add_sq_real, horth]
    ring
  have e1 : ‖c • u‖^2 = c^2 * s := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hsdef]
  have e2 : ‖(inner (𝕜 := ℝ) w n) • n‖^2 = (inner (𝕜 := ℝ) w n)^2 := by
    rw [norm_smul, hn, mul_one, Real.norm_eq_abs, sq_abs]
  rw [hnorm, e1, e2]
  rw [hcdef, hsdef]
  field_simp

private theorem yz_of_cos (LL MM NN hh kk jj y z R x : ℝ)
    (hYK : 4 * y * kk = LL ^ 2 + NN ^ 2 - MM ^ 2)
    (hZJ : 4 * z * jj = LL ^ 2 + MM ^ 2 - NN ^ 2)
    (hA1 : MM * kk = LL * hh) (hA2 : NN * jj = LL * hh)
    (hMN : MM * NN = 2 * R * hh)
    (hMMNN : MM ^ 2 + NN ^ 2 - LL ^ 2 = 4 * x * hh)
    (hh_ne : hh ≠ 0) :
    LL * (y + z) = (R - x) * (MM + NN) := by
  have hGoal3 : 4 * LL * hh * (y + z) - 4 * hh * (R - x) * (MM + NN) = 0 := by
    linear_combination MM * hYK - 4 * y * hA1 + NN * hZJ - 4 * z * hA2
      - (MM + NN) * hMMNN + 2 * (MM + NN) * hMN
  have hfac : (4 * hh) * (LL * (y + z) - (R - x) * (MM + NN)) = 0 := by
    linear_combination hGoal3
  have h4hh : (4 : ℝ) * hh ≠ 0 := by
    simp [hh_ne]
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd h h4hh
  · linarith

private theorem final_of_data (LL MM NN R r x y z hh : ℝ)
    (hLLpos : 0 < LL) (hMMpos : 0 < MM) (hNNpos : 0 < NN)
    (_hh_pos : 0 < hh)
    (hL2 : LL ^ 2 = 4 * (R ^ 2 - x ^ 2))
    (hInrad : r * (LL + MM + NN) = LL * hh)
    (hYZ : LL * (y + z) = (R - x) * (MM + NN))
    (hMMNN : MM ^ 2 + NN ^ 2 - LL ^ 2 = 4 * x * hh)
    (hMN : MM * NN = 2 * R * hh) :
    x + y + z = R + r := by
  have hSpos : 0 < LL + MM + NN := by linarith
  have hSne : LL + MM + NN ≠ 0 := ne_of_gt hSpos
  have hPerim : (MM + NN - LL) * (LL + MM + NN) = 4 * (R + x) * hh := by
    linear_combination hMMNN + 2 * hMN
  have hKey : (R - x) * (MM + NN - LL) = LL * r := by
    have hS : LL + MM + NN = MM + NN + LL := by ring
    have h1 : (R - x) * (MM + NN - LL) * (LL + MM + NN)
      = LL * r * (LL + MM + NN) := by
      linear_combination (R - x) * hPerim - LL * hInrad - hh * hL2
    have h2 : ((R - x) * (MM + NN - LL)) * (LL + MM + NN)
      = (LL * r) * (LL + MM + NN) := by
      linear_combination h1
    exact mul_right_cancel₀ hSne h2
  have hEq : LL * (y + z) = LL * (r + R - x) := by
    linear_combination hYZ + hKey
  have hEq2 : y + z = r + R - x := by
    apply mul_left_cancel₀ (ne_of_gt hLLpos) hEq
  linarith

/-- **Carnot's theorem (inradius and circumradius), general form.** Let $A, B, C$ be non-collinear
points of a Euclidean affine plane lying on the circle with center $O$ and radius $R > 0$. Take
unit vectors $n_a$, $n_b$, $n_c$ normal to the sides and pointing toward the opposite vertices:
$n_a \perp C - B$ with $\langle A - B, n_a \rangle > 0$, $n_b \perp A - C$ with
$\langle B - C, n_b \rangle > 0$, and $n_c \perp B - A$ with $\langle C - A, n_c \rangle > 0$.
Let $x = \langle O - B, n_a \rangle$, $y = \langle O - C, n_b \rangle$ and
$z = \langle O - A, n_c \rangle$ be the signed distances from $O$ to the lines $BC$, $CA$, $AB$.
If a point $I$ and a real number $r$ satisfy
$\langle I - B, n_a \rangle = \langle I - C, n_b \rangle = \langle I - A, n_c \rangle = r$
(so $I$ is the incenter and $r$ the inradius), then $x + y + z = R + r$.

This form does not assume $r > 0$ or that $O$ lies in the affine span of $A, B, C$.

Source: https://en.wikipedia.org/wiki/Carnot%27s_theorem_(inradius,_circumradius).
Statement ID: carnot-inradius-s1.
-/
theorem carnot_inradius_circumradius_general
    {V : Type*} {P : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P]
    [Fact (Module.finrank ℝ V = 2)]
    (A B C O I : P) (R r x y z : ℝ)
    (nBC nCA nAB : V)
    (hTri : ¬ Collinear ℝ ({A, B, C} : Set P))
    (hRpos : 0 < R)
    (hA : A ∈ Metric.sphere O R)
    (hB : B ∈ Metric.sphere O R)
    (hC : C ∈ Metric.sphere O R)
    (hnBC_unit : ‖nBC‖ = 1)
    (hnBC_perp : inner (𝕜 := ℝ) (C -ᵥ B) nBC = 0)
    (hnBC_in : 0 < inner (𝕜 := ℝ) (A -ᵥ B) nBC)
    (hnCA_unit : ‖nCA‖ = 1)
    (hnCA_perp : inner (𝕜 := ℝ) (A -ᵥ C) nCA = 0)
    (hnCA_in : 0 < inner (𝕜 := ℝ) (B -ᵥ C) nCA)
    (hnAB_unit : ‖nAB‖ = 1)
    (hnAB_perp : inner (𝕜 := ℝ) (B -ᵥ A) nAB = 0)
    (hnAB_in : 0 < inner (𝕜 := ℝ) (C -ᵥ A) nAB)
    (hx : x = inner (𝕜 := ℝ) (O -ᵥ B) nBC)
    (hy : y = inner (𝕜 := ℝ) (O -ᵥ C) nCA)
    (hz : z = inner (𝕜 := ℝ) (O -ᵥ A) nAB)
    (hIr1 : inner (𝕜 := ℝ) (I -ᵥ B) nBC = r)
    (hIr2 : inner (𝕜 := ℝ) (I -ᵥ C) nCA = r)
    (hIr3 : inner (𝕜 := ℝ) (I -ᵥ A) nAB = r) :
    x + y + z = R + r := by
  set a : V := A -ᵥ O with ha
  set b : V := B -ᵥ O with hb
  set c : V := C -ᵥ O with hc
  set d : V := I -ᵥ O with hd
  set u : V := c - b with hu_def
  set v : V := a - b with hv_def
  set LL : ℝ := ‖u‖ with hLL
  set MM : ℝ := ‖v - u‖ with hMM
  set NN : ℝ := ‖v‖ with hNN
  set hh : ℝ := inner (𝕜 := ℝ) v nBC with hhh
  set kk : ℝ := inner (𝕜 := ℝ) (b - c) nCA with hkk
  set jj : ℝ := inner (𝕜 := ℝ) (c - a) nAB with hjj
  set pp : ℝ := inner (𝕜 := ℝ) u v with hpp
  have h12 : A ≠ B := ne₁₂_of_not_collinear hTri
  have h13 : A ≠ C := ne₁₃_of_not_collinear hTri
  have h23 : B ≠ C := ne₂₃_of_not_collinear hTri
  have hCB : C -ᵥ B = u := by rw [hu_def, hc, hb, vsub_sub_vsub_cancel_right]
  have hABv : A -ᵥ B = v := by rw [hv_def, ha, hb, vsub_sub_vsub_cancel_right]
  have hvu_ac : v - u = a - c := by rw [hv_def, hu_def]; abel
  have hACa : a - c = A -ᵥ C := by rw [ha, hc, vsub_sub_vsub_cancel_right]
  have hACvu : A -ᵥ C = v - u := by rw [hvu_ac, hACa]
  have hbc_bc : b - c = B -ᵥ C := by
    have h1 : (B -ᵥ O) - (C -ᵥ O) = B -ᵥ C := vsub_sub_vsub_cancel_right B C O
    rw [← h1, hb, hc]
  have hba_ba : b - a = B -ᵥ A := by
    have h1 : (B -ᵥ O) - (A -ᵥ O) = B -ᵥ A := vsub_sub_vsub_cancel_right B A O
    rw [← h1, hb, ha]
  have hca_ca : c - a = C -ᵥ A := by
    have h1 : (C -ᵥ O) - (A -ᵥ O) = C -ᵥ A := vsub_sub_vsub_cancel_right C A O
    rw [← h1, hc, ha]
  have hOB : O -ᵥ B = -b := by
    have h1 : -(B -ᵥ O) = O -ᵥ B := neg_vsub_eq_vsub_rev B O
    rw [← h1, hb]
  have hOC : O -ᵥ C = -c := by
    have h1 : -(C -ᵥ O) = O -ᵥ C := neg_vsub_eq_vsub_rev C O
    rw [← h1, hc]
  have hOA : O -ᵥ A = -a := by
    have h1 : -(A -ᵥ O) = O -ᵥ A := neg_vsub_eq_vsub_rev A O
    rw [← h1, ha]
  have hIBdb : I -ᵥ B = d - b := by
    have h1 : (I -ᵥ O) - (B -ᵥ O) = I -ᵥ B := vsub_sub_vsub_cancel_right I B O
    rw [← h1, hd, hb]
  have hICdc : I -ᵥ C = d - c := by
    have h1 : (I -ᵥ O) - (C -ᵥ O) = I -ᵥ C := vsub_sub_vsub_cancel_right I C O
    rw [← h1, hd, hc]
  have hIAda : I -ᵥ A = d - a := by
    have h1 : (I -ᵥ O) - (A -ᵥ O) = I -ᵥ A := vsub_sub_vsub_cancel_right I A O
    rw [← h1, hd, ha]
  have haR : ‖a‖ = R := by
    have hmem := Metric.mem_sphere.mp hA
    rw [dist_eq_norm_vsub] at hmem
    rw [← ha] at hmem
    exact hmem
  have hbR : ‖b‖ = R := by
    have hmem := Metric.mem_sphere.mp hB
    rw [dist_eq_norm_vsub] at hmem
    rw [← hb] at hmem
    exact hmem
  have hcR : ‖c‖ = R := by
    have hmem := Metric.mem_sphere.mp hC
    rw [dist_eq_norm_vsub] at hmem
    rw [← hc] at hmem
    exact hmem
  have hu_ne : u ≠ 0 := by
    have hCneB : C ≠ B := Ne.symm h23
    have hne : C -ᵥ B ≠ 0 := vsub_ne_zero.mpr hCneB
    rw [hCB] at hne; exact hne
  have hv_ne : v ≠ 0 := by
    have hAneB : A ≠ B := h12
    have hne : A -ᵥ B ≠ 0 := vsub_ne_zero.mpr hAneB
    rw [hABv] at hne; exact hne
  have hvu_ne : v - u ≠ 0 := by
    have hAneC : A ≠ C := h13
    have hne : A -ᵥ C ≠ 0 := vsub_ne_zero.mpr hAneC
    rw [hACvu] at hne; exact hne
  have hubc : inner (𝕜 := ℝ) u nBC = 0 := hCB ▸ hnBC_perp
  have hh_pos : 0 < hh := by rw [hhh, ← hABv]; exact hnBC_in
  have hvCA : inner (𝕜 := ℝ) (v - u) nCA = 0 := hACvu ▸ hnCA_perp
  have kk_pos : 0 < kk := by rw [hkk, hbc_bc]; exact hnCA_in
  have hvAB0 : inner (𝕜 := ℝ) v nAB = 0 := by
    have h0 : inner (𝕜 := ℝ) (b - a) nAB = 0 := hba_ba ▸ hnAB_perp
    have h1 : v = -(b - a) := by rw [hv_def]; abel
    rw [h1, inner_neg_left, h0, neg_zero]
  have jj_pos : 0 < jj := by rw [hjj, hca_ca]; exact hnAB_in
  have hb_nBC : inner (𝕜 := ℝ) b nBC = -x := by
    have h1 : x = -inner (𝕜 := ℝ) b nBC := by rw [hx, hOB, inner_neg_left]
    linarith
  have hc_nBC : inner (𝕜 := ℝ) c nBC = -x := by
    have h1 : inner (𝕜 := ℝ) (c - b) nBC = 0 := hu_def ▸ hubc
    rw [inner_sub_left] at h1
    rw [hb_nBC] at h1
    linarith
  have hbc_nBC : inner (𝕜 := ℝ) (b + c) nBC = -2 * x := by
    rw [inner_add_left, hb_nBC, hc_nBC]; ring
  have chord1 : b + c = (-2 * x) • nBC := by
    have hwc : inner (𝕜 := ℝ) u (b + c) = 0 := by
      rw [hu_def, inner_sub_left, inner_add_right, inner_add_right]
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
      rw [real_inner_comm c b, real_inner_comm b c]
      rw [hcR, hbR]; ring
    have hdecomp := orth_eq_aux u nBC hu_ne hnBC_unit hubc (b + c) hwc
    rw [show inner (𝕜 := ℝ) (b + c) nBC = -2 * x from hbc_nBC] at hdecomp
    exact hdecomp
  have hca_nCA : inner (𝕜 := ℝ) a nCA = -y := by
    have h0 : inner (𝕜 := ℝ) (a - c) nCA = 0 := by
      have h1 : a - c = A -ᵥ C := hACa
      rw [h1]; exact hnCA_perp
    have h1 : y = -inner (𝕜 := ℝ) c nCA := by rw [hy, hOC, inner_neg_left]
    have h2 : inner (𝕜 := ℝ) (a - c) nCA = inner (𝕜 := ℝ) a nCA - inner (𝕜 := ℝ) c nCA :=
        inner_sub_left _ _ _
    rw [h0] at h2
    linarith
  have hc_nCA : inner (𝕜 := ℝ) c nCA = -y := by
    have h1 : y = -inner (𝕜 := ℝ) c nCA := by rw [hy, hOC, inner_neg_left]
    linarith
  have hca2_nCA : inner (𝕜 := ℝ) (c + a) nCA = -2 * y := by
    rw [inner_add_left, hc_nCA, hca_nCA]; ring
  have chord2 : c + a = (-2 * y) • nCA := by
    have hwc : inner (𝕜 := ℝ) (v - u) (c + a) = 0 := by
      have h1 : v - u = a - c := hvu_ac
      rw [h1, inner_sub_left, inner_add_right, inner_add_right]
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
      rw [real_inner_comm a c, real_inner_comm c a]
      rw [haR, hcR]; ring
    have hperp : inner (𝕜 := ℝ) (v - u) nCA = 0 := hvCA
    have hdecomp := orth_eq_aux (v - u) nCA hvu_ne hnCA_unit hperp (c + a) hwc
    rw [show inner (𝕜 := ℝ) (c + a) nCA = -2 * y from hca2_nCA] at hdecomp
    exact hdecomp
  have hab_nAB : inner (𝕜 := ℝ) a nAB = -z := by
    have h1 : z = -inner (𝕜 := ℝ) a nAB := by rw [hz, hOA, inner_neg_left]
    linarith
  have hb_nAB : inner (𝕜 := ℝ) b nAB = -z := by
    have h0 : inner (𝕜 := ℝ) (b - a) nAB = 0 := hba_ba ▸ hnAB_perp
    rw [inner_sub_left] at h0
    rw [hab_nAB] at h0
    linarith
  have hab2_nAB : inner (𝕜 := ℝ) (a + b) nAB = -2 * z := by
    rw [inner_add_left, hab_nAB, hb_nAB]; ring
  have chord3 : a + b = (-2 * z) • nAB := by
    have hwc : inner (𝕜 := ℝ) v (a + b) = 0 := by
      rw [hv_def, inner_sub_left, inner_add_right, inner_add_right]
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
      rw [real_inner_comm a b, real_inner_comm b a]
      rw [haR, hbR]; ring
    have hdecomp := orth_eq_aux v nAB hv_ne hnAB_unit hvAB0 (a + b) hwc
    rw [show inner (𝕜 := ℝ) (a + b) nAB = -2 * z from hab2_nAB] at hdecomp
    exact hdecomp
  have hbc_norm : ‖b + c‖ ^ 2 = 4 * x ^ 2 := by
    rw [chord1, norm_smul, hnBC_unit, mul_one, Real.norm_eq_abs, sq_abs]
    ring
  have eSub : ‖c - b‖ ^ 2 = ‖c‖ ^ 2 - 2 * inner (𝕜 := ℝ) c b + ‖b‖ ^ 2 :=
    norm_sub_sq_real c b
  have eAdd : ‖b + c‖ ^ 2 = ‖b‖ ^ 2 + 2 * inner (𝕜 := ℝ) b c + ‖c‖ ^ 2 :=
    norm_add_sq_real b c
  have hcR2 : ‖c‖ ^ 2 = R ^ 2 := by rw [hcR]
  have hbR2 : ‖b‖ ^ 2 = R ^ 2 := by rw [hbR]
  have hcomm : inner (𝕜 := ℝ) c b = inner (𝕜 := ℝ) b c :=
    (real_inner_comm c b).symm ▸ (real_inner_comm b c)
  have hLLcb : LL = ‖c - b‖ := by rw [hLL, hu_def]
  have hL2 : LL ^ 2 = 4 * (R ^ 2 - x ^ 2) := by
    rw [hLLcb]
    linear_combination eSub + eAdd + 2 * hcR2 + 2 * hbR2 - hbc_norm - 2 * hcomm
  have g1raw := gram_aux u nBC hu_ne hnBC_unit hubc v
  have g1 : LL ^ 2 * NN ^ 2 = pp ^ 2 + LL ^ 2 * hh ^ 2 := by
    rw [hLL, hNN, hpp, hhh]; exact g1raw
  have hbc_neg : b - c = -u := by rw [hu_def]; abel
  have hunCA : inner (𝕜 := ℝ) u nCA = -kk := by
    have h1 : kk = -inner (𝕜 := ℝ) u nCA := by
      rw [hkk, hbc_neg, inner_neg_left]
    linarith
  have hpu : inner (𝕜 := ℝ) (v - u) u = pp - LL ^ 2 := by
    rw [inner_sub_left, real_inner_self_eq_norm_sq, hLL]
    have h1 : inner (𝕜 := ℝ) v u = pp := by
      rw [hpp]; exact (real_inner_comm u v)
    rw [h1]
  have g2raw := gram_aux (v - u) nCA hvu_ne hnCA_unit hvCA u
  have g2 : MM ^ 2 * LL ^ 2 = (pp - LL ^ 2) ^ 2 + MM ^ 2 * kk ^ 2 := by
    have h1 : inner (𝕜 := ℝ) u nCA ^ 2 = kk ^ 2 := by
      rw [hunCA, neg_sq]
    have h2 : inner (𝕜 := ℝ) (v - u) u ^ 2 = (pp - LL ^ 2) ^ 2 := by rw [hpu]
    rw [hMM, hLL]
    have h3 := g2raw
    rw [hpu, hunCA, neg_sq] at h3
    exact h3
  have hca_neg : c - a = -(v - u) := by rw [hvu_ac]; abel
  have hvu_nAB : inner (𝕜 := ℝ) (v - u) nAB = -jj := by
    have h1 : jj = -inner (𝕜 := ℝ) (v - u) nAB := by
      rw [hjj, hca_neg, inner_neg_left]
    linarith
  have hvv : inner (𝕜 := ℝ) v (v - u) = NN ^ 2 - pp := by
    rw [inner_sub_right, real_inner_self_eq_norm_sq, hNN]
    have h1 : inner (𝕜 := ℝ) v u = pp := by
      rw [hpp]; exact (real_inner_comm u v)
    rw [h1]
  have g3raw := gram_aux v nAB hv_ne hnAB_unit hvAB0 (v - u)
  have g3 : NN ^ 2 * MM ^ 2 = (NN ^ 2 - pp) ^ 2 + NN ^ 2 * jj ^ 2 := by
    have h3 := g3raw
    rw [hvv, hvu_nAB, neg_sq] at h3
    rw [← hNN, ← hMM] at h3
    exact h3
  have elaw : ‖v - u‖ ^ 2 = ‖v‖ ^ 2 - 2 * inner (𝕜 := ℝ) v u + ‖u‖ ^ 2 :=
    norm_sub_sq_real v u
  have hvu_comm : inner (𝕜 := ℝ) v u = pp := by
    rw [hpp]; exact (real_inner_comm u v)
  have hlaw : MM ^ 2 = NN ^ 2 + LL ^ 2 - 2 * pp := by
    rw [hMM, hNN, hLL]
    linear_combination elaw - 2 * hvu_comm
  have hLLpos : 0 < LL := by rw [hLL]; exact norm_pos_iff.mpr hu_ne
  have hMMpos : 0 < MM := by rw [hMM]; exact norm_pos_iff.mpr hvu_ne
  have hNNpos : 0 < NN := by rw [hNN]; exact norm_pos_iff.mpr hv_ne
  have hsq1 : LL ^ 2 * hh ^ 2 = MM ^ 2 * kk ^ 2 := by
    linear_combination -g1 + g2 - LL ^ 2 * hlaw
  have hArea1 : MM * kk = LL * hh := by
    have hpos1 : 0 < MM * kk := mul_pos hMMpos kk_pos
    have hpos2 : 0 < LL * hh := mul_pos hLLpos hh_pos
    have hsq : (MM * kk) ^ 2 = (LL * hh) ^ 2 := by
      have e1 : (MM * kk) ^ 2 = MM ^ 2 * kk ^ 2 := by ring
      have e2 : (LL * hh) ^ 2 = LL ^ 2 * hh ^ 2 := by ring
      rw [e1, e2, hsq1]
    have hfac : (MM * kk - LL * hh) * (MM * kk + LL * hh) = 0 := by
      have e : (MM * kk - LL * hh) * (MM * kk + LL * hh)
        = (MM * kk) ^ 2 - (LL * hh) ^ 2 := by ring
      rw [e, hsq, sub_self]
    rcases mul_eq_zero.mp hfac with h | h
    · linarith
    · have hsum : 0 < MM * kk + LL * hh := by linarith
      linarith
  have hsq2 : LL ^ 2 * hh ^ 2 = NN ^ 2 * jj ^ 2 := by
    linear_combination -g1 + g3 - NN ^ 2 * hlaw
  have hArea2 : NN * jj = LL * hh := by
    have hpos1 : 0 < NN * jj := mul_pos hNNpos jj_pos
    have hpos2 : 0 < LL * hh := mul_pos hLLpos hh_pos
    have hsq : (NN * jj) ^ 2 = (LL * hh) ^ 2 := by
      have e1 : (NN * jj) ^ 2 = NN ^ 2 * jj ^ 2 := by ring
      have e2 : (LL * hh) ^ 2 = LL ^ 2 * hh ^ 2 := by ring
      rw [e1, e2, hsq2]
    have hfac : (NN * jj - LL * hh) * (NN * jj + LL * hh) = 0 := by
      have e : (NN * jj - LL * hh) * (NN * jj + LL * hh)
        = (NN * jj) ^ 2 - (LL * hh) ^ 2 := by ring
      rw [e, hsq, sub_self]
    rcases mul_eq_zero.mp hfac with h | h
    · linarith
    · have hsum : 0 < NN * jj + LL * hh := by linarith
      linarith
  have hvec : (v - u) + (b + c) = a + b := by rw [hv_def, hu_def]; abel
  have hN2p : NN ^ 2 - pp = 2 * x * hh := by
    have h1 : inner (𝕜 := ℝ) ((v - u) + (b + c)) v = inner (𝕜 := ℝ) (a + b) v := by
      rw [hvec]
    have h2 : inner (𝕜 := ℝ) ((v - u) + (b + c)) v
      = inner (𝕜 := ℝ) (v - u) v + inner (𝕜 := ℝ) (b + c) v :=
      inner_add_left _ _ _
    have h3 : inner (𝕜 := ℝ) (v - u) v = NN ^ 2 - pp := by
      rw [inner_sub_left, real_inner_self_eq_norm_sq, ← hNN, ← hpp]
    have h4 : inner (𝕜 := ℝ) (b + c) v = -2 * x * hh := by
      have e1 : inner (𝕜 := ℝ) (b + c) v = (-2 * x) * inner (𝕜 := ℝ) nBC v := by
        rw [chord1, real_inner_smul_left]
      have e2 : inner (𝕜 := ℝ) nBC v = hh := by
        rw [hhh]; exact (real_inner_comm v nBC)
      rw [e1, e2]
    have h5 : inner (𝕜 := ℝ) (a + b) v = 0 := by
      rw [hv_def, inner_add_left, inner_sub_right, inner_sub_right]
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
      rw [haR, hbR]
      have hc1 : inner (𝕜 := ℝ) a b = inner (𝕜 := ℝ) b a := real_inner_comm b a
      linarith [hc1]
    linear_combination h1 - h2 - h3 - h4 + h5
  have hsqN : (NN ^ 2 - pp) ^ 2 = (2 * x * hh) ^ 2 := by rw [hN2p]
  have hMNsq : MM ^ 2 * NN ^ 2 = (2 * R * hh) ^ 2 := by
    linear_combination NN ^ 2 * hlaw + g1 + hsqN + hh ^ 2 * hL2
  have hMN : MM * NN = 2 * R * hh := by
    have hpos1 : 0 < MM * NN := mul_pos hMMpos hNNpos
    have hpos2 : 0 < 2 * R * hh := by positivity
    have hsq : (MM * NN) ^ 2 = (2 * R * hh) ^ 2 := by
      have e1 : (MM * NN) ^ 2 = MM ^ 2 * NN ^ 2 := by ring
      rw [e1, hMNsq]
    have hfac : (MM * NN - 2 * R * hh) * (MM * NN + 2 * R * hh) = 0 := by
      have e : (MM * NN - 2 * R * hh) * (MM * NN + 2 * R * hh)
        = (MM * NN) ^ 2 - (2 * R * hh) ^ 2 := by ring
      rw [e, hsq, sub_self]
    rcases mul_eq_zero.mp hfac with h | h
    · linarith
    · have hsum : 0 < MM * NN + 2 * R * hh := by linarith
      linarith
  set wcomb : V := LL • nBC + MM • nCA + NN • nAB with hwcomb
  have hnBCv : inner (𝕜 := ℝ) nBC v = hh := by
    rw [real_inner_comm v nBC, ← hhh]
  have hv_nCA : inner (𝕜 := ℝ) v nCA = -kk := by
    have hv_eq : v = (v - u) + u := by abel
    rw [hv_eq, inner_add_left, hvCA, hunCA]; ring
  have hnCAv : inner (𝕜 := ℝ) nCA v = -kk := by
    rw [real_inner_comm v nCA, hv_nCA]
  have hnABv : inner (𝕜 := ℝ) nAB v = 0 := by
    rw [real_inner_comm v nAB, hvAB0]
  have hnBCu : inner (𝕜 := ℝ) nBC u = 0 := by
    rw [real_inner_comm u nBC, hubc]
  have hnCAu : inner (𝕜 := ℝ) nCA u = -kk := by
    rw [real_inner_comm u nCA, hunCA]
  have hu_nAB : inner (𝕜 := ℝ) u nAB = jj := by
    have h1 : u = v - (v - u) := by abel
    rw [h1, inner_sub_left, hvAB0, hvu_nAB]; ring
  have hnABu : inner (𝕜 := ℝ) nAB u = jj := by
    rw [real_inner_comm u nAB, hu_nAB]
  have hwv : inner (𝕜 := ℝ) wcomb v = 0 := by
    rw [hwcomb, inner_add_left, inner_add_left]
    rw [real_inner_smul_left, real_inner_smul_left, real_inner_smul_left]
    simp [hnBCv, hnCAv, hnABv]
    linarith [hArea1]
  have hwu : inner (𝕜 := ℝ) wcomb u = 0 := by
    rw [hwcomb, inner_add_left, inner_add_left]
    rw [real_inner_smul_left, real_inner_smul_left, real_inner_smul_left]
    simp [hnBCu, hnCAu, hnABu]
    linarith [hArea1, hArea2]
  have hwcomb0 : wcomb = 0 := by
    have huw : inner (𝕜 := ℝ) u wcomb = 0 := by
      rw [real_inner_comm wcomb u]; exact hwu
    have hdecomp := orth_eq_aux u nBC hu_ne hnBC_unit hubc wcomb huw
    have hinner : inner (𝕜 := ℝ) wcomb nBC = 0 := by
      have e1 : inner (𝕜 := ℝ) wcomb v
        = inner (𝕜 := ℝ) wcomb nBC * hh := by
        conv_lhs => rw [hdecomp, real_inner_smul_left, hnBCv]
      rw [hwv] at e1
      have hhh_ne : hh ≠ 0 := ne_of_gt hh_pos
      have h0 : inner (𝕜 := ℝ) wcomb nBC * hh = 0 := e1.symm
      rcases mul_eq_zero.mp h0 with h | h
      · exact h
      · exact absurd h hhh_ne
    rw [hinner, zero_smul] at hdecomp
    exact hdecomp
  have hb_nCA : inner (𝕜 := ℝ) b nCA = kk - y := by
    have h1 : inner (𝕜 := ℝ) (b - c) nCA = kk := by rw [hkk]
    rw [inner_sub_left] at h1
    rw [hc_nCA] at h1
    linarith
  have hd_nBC : inner (𝕜 := ℝ) d nBC = r - x := by
    have h1 : inner (𝕜 := ℝ) (d - b) nBC = r := hIBdb ▸ hIr1
    rw [inner_sub_left] at h1
    rw [hb_nBC] at h1
    linarith
  have hd_nCA : inner (𝕜 := ℝ) d nCA = r - y := by
    have h1 : inner (𝕜 := ℝ) (d - c) nCA = r := hICdc ▸ hIr2
    rw [inner_sub_left] at h1
    rw [hc_nCA] at h1
    linarith
  have hd_nAB : inner (𝕜 := ℝ) d nAB = r - z := by
    have h1 : inner (𝕜 := ℝ) (d - a) nAB = r := hIAda ▸ hIr3
    rw [inner_sub_left] at h1
    rw [hab_nAB] at h1
    linarith
  have hwcomb_b : inner (𝕜 := ℝ) wcomb b = 0 := by
    rw [hwcomb0, inner_zero_left]
  have hwcomb_d : inner (𝕜 := ℝ) wcomb d = 0 := by
    rw [hwcomb0, inner_zero_left]
  have hnBCb : inner (𝕜 := ℝ) nBC b = -x := by
    rw [real_inner_comm b nBC, hb_nBC]
  have hnCAb : inner (𝕜 := ℝ) nCA b = kk - y := by
    rw [real_inner_comm b nCA, hb_nCA]
  have hnABb : inner (𝕜 := ℝ) nAB b = -z := by
    rw [real_inner_comm b nAB, hb_nAB]
  have hLx : LL * x + MM * y + NN * z = LL * hh := by
    have e1 : inner (𝕜 := ℝ) wcomb b
      = LL * inner (𝕜 := ℝ) nBC b + MM * inner (𝕜 := ℝ) nCA b
        + NN * inner (𝕜 := ℝ) nAB b := by
      rw [hwcomb, inner_add_left, inner_add_left]
      rw [real_inner_smul_left, real_inner_smul_left, real_inner_smul_left]
    rw [hwcomb_b, hnBCb, hnCAb, hnABb] at e1
    linear_combination e1 + hArea1
  have hnBCd : inner (𝕜 := ℝ) nBC d = r - x := by
    rw [real_inner_comm d nBC, hd_nBC]
  have hnCAd : inner (𝕜 := ℝ) nCA d = r - y := by
    rw [real_inner_comm d nCA, hd_nCA]
  have hnABd : inner (𝕜 := ℝ) nAB d = r - z := by
    rw [real_inner_comm d nAB, hd_nAB]
  have hInrad : r * (LL + MM + NN) = LL * hh := by
    have e1 : inner (𝕜 := ℝ) wcomb d
      = LL * inner (𝕜 := ℝ) nBC d + MM * inner (𝕜 := ℝ) nCA d
        + NN * inner (𝕜 := ℝ) nAB d := by
      rw [hwcomb, inner_add_left, inner_add_left]
      rw [real_inner_smul_left, real_inner_smul_left, real_inner_smul_left]
    rw [hwcomb_d, hnBCd, hnCAd, hnABd] at e1
    linear_combination -e1 + hLx
  have hYK : 4 * y * kk = LL ^ 2 + NN ^ 2 - MM ^ 2 := by
    have e_dot : inner (𝕜 := ℝ) (c + a) u = 2 * y * kk := by
      have h1 : inner (𝕜 := ℝ) (c + a) (-u) = (-2 * y) * inner (𝕜 := ℝ) nCA (-u) := by
        rw [chord2, real_inner_smul_left]
      have h2 : inner (𝕜 := ℝ) nCA (-u) = kk := by
        rw [inner_neg_right, hnCAu]; ring
      have h3 : inner (𝕜 := ℝ) (c + a) (-u) = -inner (𝕜 := ℝ) (c + a) u :=
        inner_neg_right _ _
      rw [h2] at h1
      rw [h3] at h1
      linarith
    have e2 : 2 * inner (𝕜 := ℝ) (c + a) u - LL ^ 2 - NN ^ 2 + MM ^ 2 = 0 := by
      have eL : ‖c - b‖ ^ 2 = ‖c‖ ^ 2 - 2 * inner (𝕜 := ℝ) c b + ‖b‖ ^ 2 :=
        norm_sub_sq_real c b
      have eN : ‖a - b‖ ^ 2 = ‖a‖ ^ 2 - 2 * inner (𝕜 := ℝ) a b + ‖b‖ ^ 2 :=
        norm_sub_sq_real a b
      have eM : ‖a - c‖ ^ 2 = ‖a‖ ^ 2 - 2 * inner (𝕜 := ℝ) a c + ‖c‖ ^ 2 :=
        norm_sub_sq_real a c
      have hLL2 : LL ^ 2 = ‖c - b‖ ^ 2 := by rw [hLLcb]
      have hNN2 : NN ^ 2 = ‖a - b‖ ^ 2 := by
        have h1 : ‖a - b‖ = NN := by rw [hNN, hv_def]
        rw [h1]
      have hMM2 : MM ^ 2 = ‖a - c‖ ^ 2 := by
        have h1 : ‖a - c‖ = MM := by rw [hMM, hvu_ac]
        rw [h1]
      have hcu : inner (𝕜 := ℝ) c u = ‖c‖ ^ 2 - inner (𝕜 := ℝ) c b := by
        rw [hu_def, inner_sub_right, real_inner_self_eq_norm_sq]
      have hau : inner (𝕜 := ℝ) a u = inner (𝕜 := ℝ) a c - inner (𝕜 := ℝ) a b := by
        rw [hu_def, inner_sub_right]
      have hadd : inner (𝕜 := ℝ) (c + a) u
        = inner (𝕜 := ℝ) c u + inner (𝕜 := ℝ) a u :=
        inner_add_left _ _ _
      have hcR2 : ‖c‖ ^ 2 = R ^ 2 := by rw [hcR]
      have hbR2 : ‖b‖ ^ 2 = R ^ 2 := by rw [hbR]
      linear_combination 2 * hadd + 2 * hcu + 2 * hau
        - eL - eN + eM - hLL2 - hNN2 + hMM2 + 2 * hcR2 - 2 * hbR2
    linarith [e_dot, e2]
  have hZJ : 4 * z * jj = LL ^ 2 + MM ^ 2 - NN ^ 2 := by
    have e_dot : inner (𝕜 := ℝ) (a + b) (u - v) = -2 * z * jj := by
      have h1 : inner (𝕜 := ℝ) (a + b) (u - v)
        = inner (𝕜 := ℝ) ((-2 * z) • nAB) (u - v) := by rw [chord3]
      rw [h1, real_inner_smul_left]
      have h2 : inner (𝕜 := ℝ) nAB (u - v) = jj := by
        have h3 : inner (𝕜 := ℝ) (u - v) nAB = jj := by
          have h4 : u - v = c - a := by rw [hu_def, hv_def]; abel
          rw [h4, hjj]
        rw [real_inner_comm (u - v) nAB, h3]
      rw [h2]
    have e2 : 2 * inner (𝕜 := ℝ) (a + b) (u - v)
      + LL ^ 2 + MM ^ 2 - NN ^ 2 = 0 := by
      have eL : ‖c - b‖ ^ 2 = ‖c‖ ^ 2 - 2 * inner (𝕜 := ℝ) c b + ‖b‖ ^ 2 :=
        norm_sub_sq_real c b
      have eM : ‖a - c‖ ^ 2 = ‖a‖ ^ 2 - 2 * inner (𝕜 := ℝ) a c + ‖c‖ ^ 2 :=
        norm_sub_sq_real a c
      have eN : ‖a - b‖ ^ 2 = ‖a‖ ^ 2 - 2 * inner (𝕜 := ℝ) a b + ‖b‖ ^ 2 :=
        norm_sub_sq_real a b
      have hLL2 : LL ^ 2 = ‖c - b‖ ^ 2 := by rw [hLLcb]
      have hMM2 : MM ^ 2 = ‖a - c‖ ^ 2 := by
        have h1 : ‖a - c‖ = MM := by rw [hMM, hvu_ac]
        rw [h1]
      have hNN2 : NN ^ 2 = ‖a - b‖ ^ 2 := by
        have h1 : ‖a - b‖ = NN := by rw [hNN, hv_def]
        rw [h1]
      have hau2 : inner (𝕜 := ℝ) a (u - v)
        = inner (𝕜 := ℝ) a c - ‖a‖ ^ 2 := by
        have h1 : u - v = c - a := by rw [hu_def, hv_def]; abel
        rw [h1, inner_sub_right, real_inner_self_eq_norm_sq]
      have hbu : inner (𝕜 := ℝ) b (u - v)
        = inner (𝕜 := ℝ) b c - inner (𝕜 := ℝ) b a := by
        have h1 : u - v = c - a := by rw [hu_def, hv_def]; abel
        rw [h1, inner_sub_right]
      have hadd : inner (𝕜 := ℝ) (a + b) (u - v)
        = inner (𝕜 := ℝ) a (u - v) + inner (𝕜 := ℝ) b (u - v) :=
        inner_add_left _ _ _
      have hcR2 : ‖c‖ ^ 2 = R ^ 2 := by rw [hcR]
      have haR2 : ‖a‖ ^ 2 = R ^ 2 := by rw [haR]
      have hcomm1 : inner (𝕜 := ℝ) b c = inner (𝕜 := ℝ) c b :=
        real_inner_comm c b
      have hcomm2 : inner (𝕜 := ℝ) b a = inner (𝕜 := ℝ) a b :=
        real_inner_comm a b
      linear_combination 2 * hadd + 2 * hau2 + 2 * hbu
        + eL + eM - eN + hLL2 + hMM2 - hNN2 + 2 * hcR2 - 2 * haR2
        + 2 * hcomm1 - 2 * hcomm2
    linarith [e_dot, e2]
  have hMMNN : MM ^ 2 + NN ^ 2 - LL ^ 2 = 4 * x * hh := by
    linear_combination hlaw + 2 * hN2p
  have hYZ : LL * (y + z) = (R - x) * (MM + NN) :=
    yz_of_cos LL MM NN hh kk jj y z R x hYK hZJ hArea1 hArea2 hMN hMMNN
      (ne_of_gt hh_pos)
  exact final_of_data LL MM NN R r x y z hh hLLpos hMMpos hNNpos hh_pos
    hL2 hInrad hYZ hMMNN hMN

set_option linter.unusedVariables false in
/-- **Carnot's theorem (inradius and circumradius).** Let $A, B, C$ be non-collinear points of a
Euclidean affine plane lying on the circle with center $O$ and radius $R > 0$, and suppose $O$
lies in the affine span of $A, B, C$. Take unit vectors $n_a$, $n_b$, $n_c$ normal to the sides
and pointing toward the opposite vertices: $n_a \perp C - B$ with $\langle A - B, n_a \rangle > 0$,
$n_b \perp A - C$ with $\langle B - C, n_b \rangle > 0$, and $n_c \perp B - A$ with
$\langle C - A, n_c \rangle > 0$. Let $x = \langle O - B, n_a \rangle$,
$y = \langle O - C, n_b \rangle$ and $z = \langle O - A, n_c \rangle$ be the signed distances
from $O$ to the lines $BC$, $CA$, $AB$. If a point $I$ and a real number $r > 0$ satisfy
$\langle I - B, n_a \rangle = \langle I - C, n_b \rangle = \langle I - A, n_c \rangle = r$
(so $I$ is the incenter and $r$ the inradius), then $x + y + z = R + r$.

The hypotheses $r > 0$ and that $O$ lies in the affine span of $A, B, C$ are not used; the
general form of the theorem drops them.

Proves `Wanted` entry `carnot_inradius_circumradius`.

Source: https://en.wikipedia.org/wiki/Carnot%27s_theorem_(inradius,_circumradius).
Statement ID: carnot-inradius-s1.
-/
theorem carnot_inradius_circumradius
    {V : Type*} {P : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P]
    [Fact (Module.finrank ℝ V = 2)]
    (A B C O I : P) (R r x y z : ℝ)
    (nBC nCA nAB : V)
    (hTri : ¬ Collinear ℝ ({A, B, C} : Set P))
    (hRpos : 0 < R)
    (hOplane : O ∈ affineSpan ℝ {A, B, C})
    (hA : A ∈ Metric.sphere O R)
    (hB : B ∈ Metric.sphere O R)
    (hC : C ∈ Metric.sphere O R)
    (hnBC_unit : ‖nBC‖ = 1)
    (hnBC_perp : inner (𝕜 := ℝ) (C -ᵥ B) nBC = 0)
    (hnBC_in : 0 < inner (𝕜 := ℝ) (A -ᵥ B) nBC)
    (hnCA_unit : ‖nCA‖ = 1)
    (hnCA_perp : inner (𝕜 := ℝ) (A -ᵥ C) nCA = 0)
    (hnCA_in : 0 < inner (𝕜 := ℝ) (B -ᵥ C) nCA)
    (hnAB_unit : ‖nAB‖ = 1)
    (hnAB_perp : inner (𝕜 := ℝ) (B -ᵥ A) nAB = 0)
    (hnAB_in : 0 < inner (𝕜 := ℝ) (C -ᵥ A) nAB)
    (hx : x = inner (𝕜 := ℝ) (O -ᵥ B) nBC)
    (hy : y = inner (𝕜 := ℝ) (O -ᵥ C) nCA)
    (hz : z = inner (𝕜 := ℝ) (O -ᵥ A) nAB)
    (hrpos : 0 < r)
    (hIr1 : inner (𝕜 := ℝ) (I -ᵥ B) nBC = r)
    (hIr2 : inner (𝕜 := ℝ) (I -ᵥ C) nCA = r)
    (hIr3 : inner (𝕜 := ℝ) (I -ᵥ A) nAB = r) :
    x + y + z = R + r :=
  carnot_inradius_circumradius_general A B C O I R r x y z nBC nCA nAB hTri hRpos hA hB hC
    hnBC_unit hnBC_perp hnBC_in hnCA_unit hnCA_perp hnCA_in
    hnAB_unit hnAB_perp hnAB_in hx hy hz hIr1 hIr2 hIr3

end MetaMathlibExt
end
