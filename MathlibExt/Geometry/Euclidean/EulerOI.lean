/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

open scoped InnerProductSpace

section
namespace MetaMathlibExt

private theorem lag_aux1 (a b cc bb ef : ℝ) :
    (a ^ 2 * cc + 2 * a * b * ef + b ^ 2 * bb) * cc - (a * cc + b * ef) ^ 2
      = b ^ 2 * (cc * bb - ef ^ 2) := by ring

private theorem lag_aux2 (a b cc bb ef : ℝ) :
    (a ^ 2 * cc + 2 * a * b * ef + b ^ 2 * bb) * (cc + bb - 2 * ef)
      - (a * (ef - cc) + b * (bb - ef)) ^ 2
      = (a + b) ^ 2 * (cc * bb - ef ^ 2) := by ring

private theorem lag_aux3 (a b cc bb ef : ℝ) :
    (a ^ 2 * cc + 2 * a * b * ef + b ^ 2 * bb) * bb - (a * ef + b * bb) ^ 2
      = a ^ 2 * (cc * bb - ef ^ 2) := by ring

private theorem gram3_ring (u0 u1 e0 e1 f0 f1 : ℝ) :
    (u0 ^ 2 + u1 ^ 2) * ((e0 ^ 2 + e1 ^ 2) * (f0 ^ 2 + f1 ^ 2) - (e0 * f0 + e1 * f1) ^ 2)
      - (u0 * e0 + u1 * e1) * ((u0 * e0 + u1 * e1) * (f0 ^ 2 + f1 ^ 2)
        - (e0 * f0 + e1 * f1) * (u0 * f0 + u1 * f1))
      + (u0 * f0 + u1 * f1) * ((u0 * e0 + u1 * e1) * (e0 * f0 + e1 * f1)
        - (e0 ^ 2 + e1 ^ 2) * (u0 * f0 + u1 * f1)) = 0 := by ring

private theorem sqrt_eq_of_sq_eq (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x ^ 2 = y ^ 2) :
    x = y := by
  have hx2 : √(x ^ 2) = x := Real.sqrt_sq hx
  have hy2 : √(y ^ 2) = y := Real.sqrt_sq hy
  have hrr : √(x ^ 2) = √(y ^ 2) := by rw [h]
  rw [hx2] at hrr
  rw [hy2] at hrr
  exact hrr

/-- **Euler's theorem on the circumcenter–incenter distance.** Let $P_0, P_1, P_2$ be affinely
independent points of the Euclidean plane, $d$ the Euclidean distance and $\langle x, y \rangle$
the inner product. Let $O$ be a point and $R \ge 0$ with $d(O, P_i) = R$ for each $i$, so that
$O$ is the circumcenter and $R$ the circumradius. Let $I = w_0 P_0 + w_1 P_1 + w_2 P_2$ with
$w_0, w_1, w_2 > 0$ and $w_0 + w_1 + w_2 = 1$, and let $r \ge 0$. Suppose there are points $F_0$
on the line $P_0 P_1$, $F_1$ on the line $P_1 P_2$ and $F_2$ on the line $P_2 P_0$ with
$d(I, F_k) = r$ for each $k$ and
$\langle F_0 - I, P_1 - P_0 \rangle = \langle F_1 - I, P_2 - P_1 \rangle =
\langle F_2 - I, P_0 - P_2 \rangle = 0$, so that $I$ is an interior point at distance $r$ from
all three side lines, that is, the incenter, and $r$ is the inradius. Then
$d(O, I)^2 = R(R - 2r)$ and $R \ge 2r$.

Proves `Wanted` entry `euler_oi` (statement `euler-oi-s1`).

Source: https://en.wikipedia.org/wiki/Euler%27s_theorem_in_geometry
-/
theorem euler_oi :
    ∀ (P : Fin 3 → EuclideanSpace ℝ (Fin 2)) (O I F0 F1 F2 : EuclideanSpace ℝ (Fin 2))
      (R r w0 w1 w2 : ℝ),
      AffineIndependent ℝ P →
      (∀ i, dist O (P i) = R) →
      0 ≤ R →
      0 ≤ r →
      F0 ∈ affineSpan ℝ {P 0, P 1} →
      F1 ∈ affineSpan ℝ {P 1, P 2} →
      F2 ∈ affineSpan ℝ {P 2, P 0} →
      dist I F0 = r →
      dist I F1 = r →
      dist I F2 = r →
      ⟪F0 - I, P 1 - P 0⟫_ℝ = 0 →
      ⟪F1 - I, P 2 - P 1⟫_ℝ = 0 →
      ⟪F2 - I, P 0 - P 2⟫_ℝ = 0 →
      0 < w0 → 0 < w1 → 0 < w2 →
      w0 + w1 + w2 = 1 →
      w0 • P 0 + w1 • P 1 + w2 • P 2 = I →
      (dist O I) ^ 2 = R * (R - 2 * r) ∧ R ≥ 2 * r := by
  intro P O I F0 F1 F2 R r w0 w1 w2 hAff hO hR0 hr0 hF0 hF1 hF2 hd0 hd1 hd2
    hperp0 hperp1 hperp2 hw0 hw1 hw2 hsum hI
  set e := P 1 - P 0 with he
  set f := P 2 - P 0 with hf
  set u := O - P 0 with hu
  clear_value e f u
  have pair_indep : ∀ s t : ℝ, s • e + t • f = 0 → s = 0 ∧ t = 0 := by
    intro s t hst
    have hAI := (affineIndependent_iff (p := P)).mp hAff
    let w : Fin 3 → ℝ := ![- (s + t), s, t]
    have hsumw : ∑ i, w i = 0 := by simp [w, Fin.sum_univ_three]
    have hws : ∑ e_ ∈ Finset.univ, w e_ • P e_ = 0 := by
      have heq : (∑ e_ ∈ Finset.univ, w e_ • P e_) = s • (P 1 - P 0) + t • (P 2 - P 0) := by
        simp [w, Fin.sum_univ_three]
        module
      rw [heq, ← he, ← hf, hst]
    have h1 := hAI Finset.univ w hsumw hws 1 (Finset.mem_univ 1)
    have h2 := hAI Finset.univ w hsumw hws 2 (Finset.mem_univ 2)
    simp only [neg_add_rev, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val,
        w] at h1 h2
    exact ⟨h1, h2⟩
  have he_ne : e ≠ 0 := by
    intro hcon
    have h := pair_indep 1 0 (by simp [hcon])
    exact one_ne_zero h.1
  have hf_ne : f ≠ 0 := by
    intro hcon
    have h := pair_indep 0 1 (by simp [hcon])
    exact one_ne_zero h.2
  have hef_ne : e - f ≠ 0 := by
    intro hcon
    have heq : (1 : ℝ) • e + (-1 : ℝ) • f = e - f := by simp [sub_eq_add_neg]
    have h := pair_indep 1 (-1) (by rw [heq]; exact hcon)
    exact one_ne_zero h.1
  have hcc_pos : 0 < ⟪e, e⟫_ℝ := (real_inner_self_pos).mpr he_ne
  have hbb_pos : 0 < ⟪f, f⟫_ℝ := (real_inner_self_pos).mpr hf_ne
  have hS_pos : 0 < ⟪e - f, e - f⟫_ℝ := (real_inner_self_pos).mpr hef_ne
  have hcc_ne : ⟪e, e⟫_ℝ ≠ 0 := ne_of_gt hcc_pos
  have hbb_ne : ⟪f, f⟫_ℝ ≠ 0 := ne_of_gt hbb_pos
  have hz_ne : ⟪f, f⟫_ℝ • e - ⟪e, f⟫_ℝ • f ≠ 0 := by
    intro hcon
    have heq : ⟪f, f⟫_ℝ • e - ⟪e, f⟫_ℝ • f
        = ⟪f, f⟫_ℝ • e + (-⟪e, f⟫_ℝ) • f := by rw [neg_smul]; abel
    have h := pair_indep _ _ (by rw [← heq]; exact hcon)
    exact hbb_ne h.1
  have hz_sq : ⟪⟪f, f⟫_ℝ • e - ⟪e, f⟫_ℝ • f, ⟪f, f⟫_ℝ • e - ⟪e, f⟫_ℝ • f⟫_ℝ
      = ⟪f, f⟫_ℝ * (⟪e, e⟫_ℝ * ⟪f, f⟫_ℝ - ⟪e, f⟫_ℝ ^ 2) := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right,
      inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right,
      inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right]
    simp only [starRingEnd_apply, star_trivial]
    rw [real_inner_comm f e, real_inner_comm e f]
    ring
  have hz_pos : 0 < ⟪⟪f, f⟫_ℝ • e - ⟪e, f⟫_ℝ • f, ⟪f, f⟫_ℝ • e - ⟪e, f⟫_ℝ • f⟫_ℝ :=
    (real_inner_self_pos).mpr hz_ne
  have hG_pos : 0 < ⟪e, e⟫_ℝ * ⟪f, f⟫_ℝ - ⟪e, f⟫_ℝ ^ 2 := by
    have hmul : 0 < ⟪f, f⟫_ℝ * (⟪e, e⟫_ℝ * ⟪f, f⟫_ℝ - ⟪e, f⟫_ℝ ^ 2) := by
      rw [← hz_sq]; exact hz_pos
    exact (pos_of_mul_pos_right hmul (le_of_lt hbb_pos))
  have hG_ne : ⟪e, e⟫_ℝ * ⟪f, f⟫_ℝ - ⟪e, f⟫_ℝ ^ 2 ≠ 0 := ne_of_gt hG_pos
  -- circumcenter projections
  have huR : ‖u‖ = R := by rw [hu, ← dist_eq_norm]; exact hO 0
  have hRR : ⟪u, u⟫_ℝ = R ^ 2 := by rw [real_inner_self_eq_norm_sq, huR]
  have hO1 : O - P 1 = u - e := by rw [hu, he]; abel
  have hnorm1 : ‖u - e‖ = R := by rw [← hO1, ← dist_eq_norm]; exact hO 1
  have hexp1 : ‖u - e‖ ^ 2 = ‖u‖ ^ 2 - 2 * ⟪u, e⟫_ℝ + ‖e‖ ^ 2 := by
    have h := norm_sub_sq (𝕜 := ℝ) u e
    simpa using h
  have hUe : ⟪u, e⟫_ℝ = ⟪e, e⟫_ℝ / 2 := by
    rw [hnorm1, huR, ← real_inner_self_eq_norm_sq e] at hexp1
    linarith
  have hO2 : O - P 2 = u - f := by rw [hu, hf]; abel
  have hnorm2 : ‖u - f‖ = R := by rw [← hO2, ← dist_eq_norm]; exact hO 2
  have hexp2 : ‖u - f‖ ^ 2 = ‖u‖ ^ 2 - 2 * ⟪u, f⟫_ℝ + ‖f‖ ^ 2 := by
    have h := norm_sub_sq (𝕜 := ℝ) u f
    simpa using h
  have hUf : ⟪u, f⟫_ℝ = ⟪f, f⟫_ℝ / 2 := by
    rw [hnorm2, huR, ← real_inner_self_eq_norm_sq f] at hexp2
    linarith
  -- barycenter
  have hw0eq : w0 = 1 - w1 - w2 := by linarith
  have hI0 : I - P 0 = w1 • e + w2 • f := by
    rw [← hI, hw0eq, he, hf]; module
  -- OI expansion
  have hOI : O - I = u - (w1 • e + w2 • f) := by
    have hsub : O - I = (O - P 0) - (I - P 0) := by abel
    rw [hsub, ← hu, hI0]
  have huv : ⟪u, w1 • e + w2 • f⟫_ℝ
      = w1 * (⟪e, e⟫_ℝ / 2) + w2 * (⟪f, f⟫_ℝ / 2) := by
    rw [inner_add_right, inner_smul_right, inner_smul_right, hUe, hUf]
  have hOI2 : ‖O - I‖ ^ 2
      = R ^ 2 - (w1 * ⟪e, e⟫_ℝ + w2 * ⟪f, f⟫_ℝ) + ‖w1 • e + w2 • f‖ ^ 2 := by
    have hexp : ‖u - (w1 • e + w2 • f)‖ ^ 2
        = ‖u‖ ^ 2 - 2 * ⟪u, w1 • e + w2 • f⟫_ℝ + ‖w1 • e + w2 • f‖ ^ 2 := by
      have h := norm_sub_sq (𝕜 := ℝ) u (w1 • e + w2 • f)
      simpa using h
    rw [hOI, hexp, huR, huv]
    ring
  have hv_sq : ⟪w1 • e + w2 • f, w1 • e + w2 • f⟫_ℝ
      = w1 ^ 2 * ⟪e, e⟫_ℝ + 2 * w1 * w2 * ⟪e, f⟫_ℝ + w2 ^ 2 * ⟪f, f⟫_ℝ := by
    rw [inner_add_left, inner_add_right, inner_add_right,
      inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right,
      inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right]
    simp only [starRingEnd_apply, star_trivial]
    rw [real_inner_comm f e]
    ring
  have hv_norm : ‖w1 • e + w2 • f‖ ^ 2
      = w1 ^ 2 * ⟪e, e⟫_ℝ + 2 * w1 * w2 * ⟪e, f⟫_ℝ + w2 ^ 2 * ⟪f, f⟫_ℝ := by
    rw [← real_inner_self_eq_norm_sq]
    exact hv_sq
  have hS_expand : ⟪e - f, e - f⟫_ℝ
      = ⟪e, e⟫_ℝ + ⟪f, f⟫_ℝ - 2 * ⟪e, f⟫_ℝ := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right,
      real_inner_comm f e]
    ring
  -- coordinates for Gram determinant identity
  have coord : ∀ x y : EuclideanSpace ℝ (Fin 2),
      ⟪x, y⟫_ℝ = WithLp.ofLp x 0 * WithLp.ofLp y 0 + WithLp.ofLp x 1 * WithLp.ofLp y 1 := by
    intro x y
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [dotProduct, Fin.sum_univ_two, star_trivial]
    ring
  have hcirc : 4 * R ^ 2 * (⟪e, e⟫_ℝ * ⟪f, f⟫_ℝ - ⟪e, f⟫_ℝ ^ 2)
      = (⟪e, e⟫_ℝ + ⟪f, f⟫_ℝ - 2 * ⟪e, f⟫_ℝ) * ⟪f, f⟫_ℝ * ⟪e, e⟫_ℝ := by
    set u0 : ℝ := WithLp.ofLp u 0 with hu0
    set u1 : ℝ := WithLp.ofLp u 1 with hu1
    set e0 : ℝ := WithLp.ofLp e 0 with he0
    set e1 : ℝ := WithLp.ofLp e 1 with he1
    set f0 : ℝ := WithLp.ofLp f 0 with hf0
    set f1 : ℝ := WithLp.ofLp f 1 with hf1
    have hA : ⟪u, u⟫_ℝ = u0 ^ 2 + u1 ^ 2 := by
      rw [coord u u, ← hu0, ← hu1]; ring
    have hB : ⟪u, e⟫_ℝ = u0 * e0 + u1 * e1 := by
      rw [coord u e, ← hu0, ← hu1, ← he0, ← he1]
    have hC : ⟪u, f⟫_ℝ = u0 * f0 + u1 * f1 := by
      rw [coord u f, ← hu0, ← hu1, ← hf0, ← hf1]
    have hcc : ⟪e, e⟫_ℝ = e0 ^ 2 + e1 ^ 2 := by
      rw [coord e e, ← he0, ← he1]; ring
    have hef : ⟪e, f⟫_ℝ = e0 * f0 + e1 * f1 := by
      rw [coord e f, ← he0, ← he1, ← hf0, ← hf1]
    have hbb : ⟪f, f⟫_ℝ = f0 ^ 2 + f1 ^ 2 := by
      rw [coord f f, ← hf0, ← hf1]; ring
    have hdet := gram3_ring u0 u1 e0 e1 f0 f1
    rw [← hA, ← hB, ← hC, ← hcc, ← hef, ← hbb] at hdet
    rw [hRR, hUe, hUf] at hdet
    linear_combination 4 * hdet
  -- foot F0 on P0-P1
  have hmem0 : F0 ∈ line[ℝ, P 0, P 1] := by simpa using hF0
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hmem0
  obtain ⟨t0, ht0⟩ := hmem0
  have hF0eq : F0 = t0 • e + P 0 := by
    have h := AffineMap.lineMap_apply (P 0) (P 1) t0
    rw [ht0] at h
    simpa [vsub_eq_sub, vadd_eq_add, ← he] using h
  have hd0n : ‖F0 - I‖ = r := by
    have h := hd0
    rw [dist_eq_norm, norm_sub_rev] at h
    exact h
  have hF0sub : F0 - P 0 = t0 • e := by rw [hF0eq]; abel
  have hV0 : F0 - I = (t0 - w1) • e + (-w2) • f := by
    have hsub : F0 - I = (F0 - P 0) - (I - P 0) := by abel
    rw [hsub, hF0sub, hI0]
    module
  have hinner0 : (t0 - w1) * ⟪e, e⟫_ℝ + (-w2) * ⟪e, f⟫_ℝ = 0 := by
    have h := hperp0
    rw [hV0, inner_add_left, inner_smul_left, inner_smul_left] at h
    simp only [starRingEnd_apply, star_trivial] at h
    rw [real_inner_comm e f] at h
    exact h
  have hnorm0 : (t0 - w1) ^ 2 * ⟪e, e⟫_ℝ + 2 * (t0 - w1) * (-w2) * ⟪e, f⟫_ℝ
      + (-w2) ^ 2 * ⟪f, f⟫_ℝ = r ^ 2 := by
    have h : ‖F0 - I‖ ^ 2 = r ^ 2 := by rw [hd0n]
    rw [hV0, ← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
      inner_add_right, inner_smul_left, inner_smul_right, inner_smul_left,
      inner_smul_right, inner_smul_left, inner_smul_right, inner_smul_left,
      inner_smul_right] at h
    simp only [starRingEnd_apply, star_trivial] at h
    rw [real_inner_comm e f] at h
    linear_combination h
  have hfoot0 : r ^ 2 * ⟪e, e⟫_ℝ
      = w2 ^ 2 * (⟪e, e⟫_ℝ * ⟪f, f⟫_ℝ - ⟪e, f⟫_ℝ ^ 2) := by
    have hlag := lag_aux1 (t0 - w1) (-w2) ⟪e, e⟫_ℝ ⟪f, f⟫_ℝ ⟪e, f⟫_ℝ
    rw [hnorm0, hinner0] at hlag
    have hsq : (-w2) ^ 2 = w2 ^ 2 := by ring
    rw [hsq] at hlag
    simpa using hlag
  -- foot F2 on P2-P0
  have hdir2 : P 0 - P 2 = -f := by rw [hf]; abel
  have hperp2f : ⟪F2 - I, f⟫_ℝ = 0 := by
    have h := hperp2
    rw [hdir2, inner_neg_right] at h
    simpa using h
  have hmem2 : F2 ∈ line[ℝ, P 2, P 0] := by simpa using hF2
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hmem2
  obtain ⟨t2, ht2⟩ := hmem2
  have h2eq : F2 = t2 • (P 0 - P 2) + P 2 := by
    have h := AffineMap.lineMap_apply (P 2) (P 0) t2
    rw [ht2] at h
    simpa [vsub_eq_sub, vadd_eq_add] using h
  have hF2sub : F2 - P 0 = (1 - t2) • f := by
    have hP2sub : P 2 - P 0 = f := hf.symm
    have hsub : (t2 • (-f) + P 2) - P 0 = t2 • (-f) + (P 2 - P 0) := by abel
    rw [h2eq, hdir2, hsub, hP2sub]
    module
  have hd2n : ‖F2 - I‖ = r := by
    have h := hd2
    rw [dist_eq_norm, norm_sub_rev] at h
    exact h
  have hV2 : F2 - I = (-w1) • e + ((1 - t2) - w2) • f := by
    have hsub : F2 - I = (F2 - P 0) - (I - P 0) := by abel
    rw [hsub, hF2sub, hI0]
    module
  have hinner2 : (-w1) * ⟪e, f⟫_ℝ + ((1 - t2) - w2) * ⟪f, f⟫_ℝ = 0 := by
    have h := hperp2f
    rw [hV2, inner_add_left, inner_smul_left, inner_smul_left] at h
    simp only [starRingEnd_apply, star_trivial] at h
    exact h
  have hnorm2 : (-w1) ^ 2 * ⟪e, e⟫_ℝ + 2 * (-w1) * ((1 - t2) - w2) * ⟪e, f⟫_ℝ
      + ((1 - t2) - w2) ^ 2 * ⟪f, f⟫_ℝ = r ^ 2 := by
    have h : ‖F2 - I‖ ^ 2 = r ^ 2 := by rw [hd2n]
    rw [hV2, ← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
      inner_add_right, inner_smul_left, inner_smul_right, inner_smul_left,
      inner_smul_right, inner_smul_left, inner_smul_right, inner_smul_left,
      inner_smul_right] at h
    simp only [starRingEnd_apply, star_trivial] at h
    rw [real_inner_comm e f] at h
    linear_combination h
  have hfoot2 : r ^ 2 * ⟪f, f⟫_ℝ
      = w1 ^ 2 * (⟪e, e⟫_ℝ * ⟪f, f⟫_ℝ - ⟪e, f⟫_ℝ ^ 2) := by
    have hlag := lag_aux3 (-w1) ((1 - t2) - w2) ⟪e, e⟫_ℝ ⟪f, f⟫_ℝ ⟪e, f⟫_ℝ
    rw [hnorm2, hinner2] at hlag
    have hsq : (-w1) ^ 2 = w1 ^ 2 := by ring
    rw [hsq] at hlag
    simpa using hlag
  -- foot F1 on P1-P2
  have hdir1 : P 2 - P 1 = f - e := by rw [hf, he]; abel
  have hperp1d : ⟪F1 - I, f - e⟫_ℝ = 0 := by rw [← hdir1]; exact hperp1
  have hmem1 : F1 ∈ line[ℝ, P 1, P 2] := by simpa using hF1
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hmem1
  obtain ⟨s1, hs1⟩ := hmem1
  have h1eq : F1 = s1 • (P 2 - P 1) + P 1 := by
    have h := AffineMap.lineMap_apply (P 1) (P 2) s1
    rw [hs1] at h
    simpa [vsub_eq_sub, vadd_eq_add] using h
  have hF1sub : F1 - P 0 = (1 - s1) • e + s1 • f := by
    have hP1sub : P 1 - P 0 = e := he.symm
    have hsub : (s1 • (f - e) + P 1) - P 0 = s1 • (f - e) + (P 1 - P 0) := by abel
    rw [h1eq, hdir1, hsub, hP1sub]
    module
  have hd1n : ‖F1 - I‖ = r := by
    have h := hd1
    rw [dist_eq_norm, norm_sub_rev] at h
    exact h
  have hV1 : F1 - I = ((1 - s1) - w1) • e + (s1 - w2) • f := by
    have hsub : F1 - I = (F1 - P 0) - (I - P 0) := by abel
    rw [hsub, hF1sub, hI0]
    module
  have hab : ((1 - s1) - w1) + (s1 - w2) = w0 := by linarith
  have hinner1 : ((1 - s1) - w1) * (⟪e, f⟫_ℝ - ⟪e, e⟫_ℝ)
      + (s1 - w2) * (⟪f, f⟫_ℝ - ⟪e, f⟫_ℝ) = 0 := by
    have h := hperp1d
    rw [hV1] at h
    simp only [inner_add_left, inner_sub_right, inner_smul_left,
      starRingEnd_apply, star_trivial] at h
    rw [real_inner_comm e f] at h
    linear_combination h
  have hnorm1 : ((1 - s1) - w1) ^ 2 * ⟪e, e⟫_ℝ
      + 2 * ((1 - s1) - w1) * (s1 - w2) * ⟪e, f⟫_ℝ
      + (s1 - w2) ^ 2 * ⟪f, f⟫_ℝ = r ^ 2 := by
    have h : ‖F1 - I‖ ^ 2 = r ^ 2 := by rw [hd1n]
    rw [hV1, ← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
      inner_add_right, inner_smul_left, inner_smul_right, inner_smul_left,
      inner_smul_right, inner_smul_left, inner_smul_right, inner_smul_left,
      inner_smul_right] at h
    simp only [starRingEnd_apply, star_trivial] at h
    rw [real_inner_comm e f] at h
    linear_combination h
  have hfoot1 : r ^ 2 * (⟪e, e⟫_ℝ + ⟪f, f⟫_ℝ - 2 * ⟪e, f⟫_ℝ)
      = w0 ^ 2 * (⟪e, e⟫_ℝ * ⟪f, f⟫_ℝ - ⟪e, f⟫_ℝ ^ 2) := by
    have hlag := lag_aux2 ((1 - s1) - w1) (s1 - w2)
      ⟪e, e⟫_ℝ ⟪f, f⟫_ℝ ⟪e, f⟫_ℝ
    rw [hnorm1, hinner1, hab] at hlag
    simpa using hlag
  -- positivity of r and side lengths
  have hSexpr_pos : 0 < ⟪e, e⟫_ℝ + ⟪f, f⟫_ℝ - 2 * ⟪e, f⟫_ℝ := by
    rw [← hS_expand]; exact hS_pos
  have hr_pos : 0 < r := by
    by_contra hcon
    have hconle : r ≤ 0 := le_of_not_gt hcon
    have hr0eq : r = 0 := le_antisymm hconle hr0
    have hcon2 : w2 ^ 2 * (⟪e, e⟫_ℝ * ⟪f, f⟫_ℝ - ⟪e, f⟫_ℝ ^ 2) = 0 := by
      rw [← hfoot0, hr0eq]; ring
    have hpos : 0 < w2 ^ 2 * (⟪e, e⟫_ℝ * ⟪f, f⟫_ℝ - ⟪e, f⟫_ℝ ^ 2) :=
      mul_pos (pow_pos hw2 2) hG_pos
    linarith
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  -- side lengths and twice-area
  set a : ℝ := √(⟪e, e⟫_ℝ + ⟪f, f⟫_ℝ - 2 * ⟪e, f⟫_ℝ) with ha
  set b : ℝ := √(⟪f, f⟫_ℝ) with hb
  set cc_len : ℝ := √(⟪e, e⟫_ℝ) with hclen
  set sg : ℝ := √(⟪e, e⟫_ℝ * ⟪f, f⟫_ℝ - ⟪e, f⟫_ℝ ^ 2) with hsg
  have ha_pos : 0 < a := by rw [ha]; exact Real.sqrt_pos.mpr hSexpr_pos
  have hb_pos : 0 < b := by rw [hb]; exact Real.sqrt_pos.mpr hbb_pos
  have hc_pos : 0 < cc_len := by rw [hclen]; exact Real.sqrt_pos.mpr hcc_pos
  have hsg_pos : 0 < sg := by rw [hsg]; exact Real.sqrt_pos.mpr hG_pos
  have ha_nn : 0 ≤ a := le_of_lt ha_pos
  have hb_nn : 0 ≤ b := le_of_lt hb_pos
  have hc_nn : 0 ≤ cc_len := le_of_lt hc_pos
  have hsg_nn : 0 ≤ sg := le_of_lt hsg_pos
  have ha2 : a ^ 2 = ⟪e, e⟫_ℝ + ⟪f, f⟫_ℝ - 2 * ⟪e, f⟫_ℝ := by
    rw [ha]; exact Real.sq_sqrt (le_of_lt hSexpr_pos)
  have hb2 : b ^ 2 = ⟪f, f⟫_ℝ := by
    rw [hb]; exact Real.sq_sqrt (le_of_lt hbb_pos)
  have hc2 : cc_len ^ 2 = ⟪e, e⟫_ℝ := by
    rw [hclen]; exact Real.sq_sqrt (le_of_lt hcc_pos)
  have hsg2 : sg ^ 2 = ⟪e, e⟫_ℝ * ⟪f, f⟫_ℝ - ⟪e, f⟫_ℝ ^ 2 := by
    rw [hsg]; exact Real.sq_sqrt (le_of_lt hG_pos)
  have hw2sg : w2 * sg = r * cc_len := by
    apply sqrt_eq_of_sq_eq
    · exact mul_nonneg (le_of_lt hw2) hsg_nn
    · exact mul_nonneg (le_of_lt hr_pos) hc_nn
    · have e1 : (w2 * sg) ^ 2 = w2 ^ 2 * (⟪e, e⟫_ℝ * ⟪f, f⟫_ℝ - ⟪e, f⟫_ℝ ^ 2) := by
        rw [mul_pow, hsg2]
      have e2 : (r * cc_len) ^ 2 = r ^ 2 * ⟪e, e⟫_ℝ := by
        rw [mul_pow, hc2]
      rw [e1, e2]
      exact hfoot0.symm
  have hw1sg : w1 * sg = r * b := by
    apply sqrt_eq_of_sq_eq
    · exact mul_nonneg (le_of_lt hw1) hsg_nn
    · exact mul_nonneg (le_of_lt hr_pos) hb_nn
    · have e1 : (w1 * sg) ^ 2 = w1 ^ 2 * (⟪e, e⟫_ℝ * ⟪f, f⟫_ℝ - ⟪e, f⟫_ℝ ^ 2) := by
        rw [mul_pow, hsg2]
      have e2 : (r * b) ^ 2 = r ^ 2 * ⟪f, f⟫_ℝ := by
        rw [mul_pow, hb2]
      rw [e1, e2]
      exact hfoot2.symm
  have hw0sg : w0 * sg = r * a := by
    apply sqrt_eq_of_sq_eq
    · exact mul_nonneg (le_of_lt hw0) hsg_nn
    · exact mul_nonneg (le_of_lt hr_pos) ha_nn
    · have e1 : (w0 * sg) ^ 2 = w0 ^ 2 * (⟪e, e⟫_ℝ * ⟪f, f⟫_ℝ - ⟪e, f⟫_ℝ ^ 2) := by
        rw [mul_pow, hsg2]
      have e2 : (r * a) ^ 2 = r ^ 2 * (⟪e, e⟫_ℝ + ⟪f, f⟫_ℝ - 2 * ⟪e, f⟫_ℝ) := by
        rw [mul_pow, ha2]
      rw [e1, e2]
      exact hfoot1.symm
  have hsg_sum : sg = r * (a + b + cc_len) := by
    have hsumsg : (w0 + w1 + w2) * sg = r * a + r * b + r * cc_len := by
      rw [add_mul, add_mul, hw0sg, hw1sg, hw2sg]
    rw [hsum, one_mul] at hsumsg
    linear_combination hsumsg
  have habc : a * b * cc_len = 2 * R * sg := by
    apply sqrt_eq_of_sq_eq
    · exact mul_nonneg (mul_nonneg ha_nn hb_nn) hc_nn
    · have h2R : 0 ≤ 2 * R := by linarith
      exact mul_nonneg h2R hsg_nn
    · have e1 : (a * b * cc_len) ^ 2
          = (⟪e, e⟫_ℝ + ⟪f, f⟫_ℝ - 2 * ⟪e, f⟫_ℝ) * ⟪f, f⟫_ℝ * ⟪e, e⟫_ℝ := by
        have h1 : (a * b * cc_len) ^ 2 = (a ^ 2) * (b ^ 2) * (cc_len ^ 2) := by ring
        rw [h1, ha2, hb2, hc2]
      have e2 : (2 * R * sg) ^ 2 = 4 * R ^ 2 * (⟪e, e⟫_ℝ * ⟪f, f⟫_ℝ - ⟪e, f⟫_ℝ ^ 2) := by
        have h1 : (2 * R * sg) ^ 2 = 4 * R ^ 2 * (sg ^ 2) := by ring
        rw [h1, hsg2]
      rw [e1, e2]
      exact hcirc.symm
  have habc_pos : 0 < a * b * cc_len :=
    mul_pos (mul_pos ha_pos hb_pos) hc_pos
  have hR_pos : 0 < R := by
    have h2Rsg : 0 < 2 * R * sg := by rw [← habc]; exact habc_pos
    have h2R : 0 < 2 * R := pos_of_mul_pos_left h2Rsg (le_of_lt hsg_pos)
    linarith
  have hsg_ne : sg ≠ 0 := ne_of_gt hsg_pos
  have hkey : a ^ 2 * (w1 * w2) + b ^ 2 * (w2 * w0) + cc_len ^ 2 * (w0 * w1)
      = 2 * R * r := by
    have e1 : (a ^ 2 * (w1 * w2) + b ^ 2 * (w2 * w0) + cc_len ^ 2 * (w0 * w1)) * sg ^ 2
        = (2 * R * r) * sg ^ 2 := by
      have step1 : (a ^ 2 * (w1 * w2) + b ^ 2 * (w2 * w0) + cc_len ^ 2 * (w0 * w1)) * sg ^ 2
          = a ^ 2 * (w1 * sg) * (w2 * sg) + b ^ 2 * (w2 * sg) * (w0 * sg)
            + cc_len ^ 2 * (w0 * sg) * (w1 * sg) := by ring
      rw [step1, hw0sg, hw1sg, hw2sg]
      have step2 : a ^ 2 * (r * b) * (r * cc_len) + b ^ 2 * (r * cc_len) * (r * a)
          + cc_len ^ 2 * (r * a) * (r * b)
          = r ^ 2 * (a * b * cc_len) * (a + b + cc_len) := by ring
      rw [step2, habc]
      have step3 : r ^ 2 * (2 * R * sg) * (a + b + cc_len)
          = 2 * R * r * (r * (a + b + cc_len)) * sg := by ring
      rw [step3, ← hsg_sum]
      ring
    have hsg2_ne : sg ^ 2 ≠ 0 := pow_ne_zero 2 hsg_ne
    exact mul_right_cancel₀ hsg2_ne e1
  have hK : R ^ 2 - (w1 * ⟪e, e⟫_ℝ + w2 * ⟪f, f⟫_ℝ)
        + (w1 ^ 2 * ⟪e, e⟫_ℝ + 2 * w1 * w2 * ⟪e, f⟫_ℝ + w2 ^ 2 * ⟪f, f⟫_ℝ)
      = R ^ 2 - ((⟪e, e⟫_ℝ + ⟪f, f⟫_ℝ - 2 * ⟪e, f⟫_ℝ) * (w1 * w2)
        + ⟪f, f⟫_ℝ * (w2 * w0) + ⟪e, e⟫_ℝ * (w0 * w1)) := by
    rw [hw0eq]; ring
  have hK2 : (⟪e, e⟫_ℝ + ⟪f, f⟫_ℝ - 2 * ⟪e, f⟫_ℝ) * (w1 * w2)
        + ⟪f, f⟫_ℝ * (w2 * w0) + ⟪e, e⟫_ℝ * (w0 * w1) = 2 * R * r := by
    rw [← ha2, ← hb2, ← hc2]
    exact hkey
  have hfinal : ‖O - I‖ ^ 2 = R * (R - 2 * r) := by
    rw [hOI2, hv_norm, hK, hK2]
    ring
  have hdist : dist O I = ‖O - I‖ := dist_eq_norm O I
  have hmain : (dist O I) ^ 2 = R * (R - 2 * r) := by
    rw [hdist, hfinal]
  have hnn : 0 ≤ R * (R - 2 * r) := by
    rw [← hmain]
    exact sq_nonneg _
  have hR2r : 0 ≤ R - 2 * r := nonneg_of_mul_nonneg_right hnn hR_pos
  exact ⟨hmain, by linarith⟩

end MetaMathlibExt
