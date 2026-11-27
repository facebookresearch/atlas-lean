/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal

namespace MetaMathlibExt

@[expose] public section

private lemma inner_coord_eq (x y : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ x y = x.ofLp 0 * y.ofLp 0 + x.ofLp 1 * y.ofLp 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp [RCLike.inner_apply]
  ring

private lemma norm_sq_coord_eq (x : EuclideanSpace ℝ (Fin 2)) :
    ‖x‖ ^ 2 = (x.ofLp 0) ^ 2 + (x.ofLp 1) ^ 2 := by
  have h := inner_coord_eq x x
  rw [real_inner_self_eq_norm_sq] at h
  linear_combination h

private lemma rotated_inner_eq (p0 p1 a0 a1 c0 c1 r : ℝ) (hr : r ≠ 0)
    (hcc : c0 ^ 2 + c1 ^ 2 = r ^ 2) :
    ((p0 * c0 + p1 * c1) / r) * ((a0 * c0 + a1 * c1) / r)
      + ((-p0 * c1 + p1 * c0) / r) * ((-a0 * c1 + a1 * c0) / r)
      = p0 * a0 + p1 * a1 := by
  field_simp
  linear_combination (p0 * a0 + p1 * a1) * hcc

private lemma rotated_norm_eq (a0 a1 c0 c1 r : ℝ) (hr : r ≠ 0)
    (ha : a0 ^ 2 + a1 ^ 2 = r ^ 2) (hcc : c0 ^ 2 + c1 ^ 2 = r ^ 2) :
    ((a0 * c0 + a1 * c1) / r) ^ 2 + ((-a0 * c1 + a1 * c0) / r) ^ 2 = r ^ 2 := by
  field_simp
  linear_combination (a0 ^ 2 + a1 ^ 2) * hcc + r ^ 2 * ha

private lemma perp_eq_zero_of_norm_eq {w u v : EuclideanSpace ℝ (Fin 2)} {s : ℝ}
    (h1 : inner ℝ w u = 0) (h2 : inner ℝ w v = 0)
    (hu : ‖u‖ = s) (hv : ‖v‖ = s) (huv : ‖u + v‖ = s)
    (hs : 0 < s) : w = 0 := by
  have horth1 : w.ofLp 0 * u.ofLp 0 + w.ofLp 1 * u.ofLp 1 = 0 := by
    rw [← inner_coord_eq]; exact h1
  have horth2 : w.ofLp 0 * v.ofLp 0 + w.ofLp 1 * v.ofLp 1 = 0 := by
    rw [← inner_coord_eq]; exact h2
  have husq : (u.ofLp 0) ^ 2 + (u.ofLp 1) ^ 2 = s ^ 2 := by
    rw [← norm_sq_coord_eq u, hu]
  have hvsq : (v.ofLp 0) ^ 2 + (v.ofLp 1) ^ 2 = s ^ 2 := by
    rw [← norm_sq_coord_eq v, hv]
  have hadd0 : (u + v).ofLp 0 = u.ofLp 0 + v.ofLp 0 := by simp
  have hadd1 : (u + v).ofLp 1 = u.ofLp 1 + v.ofLp 1 := by simp
  have huvsq : ((u + v).ofLp 0) ^ 2 + ((u + v).ofLp 1) ^ 2 = s ^ 2 := by
    rw [← norm_sq_coord_eq (u + v), huv]
  rw [hadd0, hadd1] at huvsq
  have huv_inner : inner ℝ u v = -(s ^ 2) / 2 := by
    have h := norm_add_sq_real u v
    rw [hu, hv, huv] at h
    linarith
  have huvc : u.ofLp 0 * v.ofLp 0 + u.ofLp 1 * v.ofLp 1 = -(s ^ 2) / 2 := by
    rw [← inner_coord_eq]; exact huv_inner
  have hlag : (u.ofLp 0 * v.ofLp 1 - u.ofLp 1 * v.ofLp 0) ^ 2
      + (u.ofLp 0 * v.ofLp 0 + u.ofLp 1 * v.ofLp 1) ^ 2
      = ((u.ofLp 0) ^ 2 + (u.ofLp 1) ^ 2) * ((v.ofLp 0) ^ 2 + (v.ofLp 1) ^ 2) := by
    ring
  set det := u.ofLp 0 * v.ofLp 1 - u.ofLp 1 * v.ofLp 0 with hdet
  have hdet_sq : det ^ 2 = 3 * s ^ 4 / 4 := by
    rw [huvc, husq, hvsq] at hlag
    linear_combination hlag
  have hdet_ne : det ≠ 0 := by
    intro hzero
    rw [hzero] at hdet_sq
    have hs4 : (0 : ℝ) < s ^ 4 := pow_pos hs 4
    nlinarith
  have hSx : w.ofLp 0 = 0 := by
    have hmem : w.ofLp 0 * (u.ofLp 0 * v.ofLp 1 - u.ofLp 1 * v.ofLp 0) = 0 := by
      linear_combination (v.ofLp 1) * horth1 - (u.ofLp 1) * horth2
    rw [← hdet] at hmem
    rcases mul_eq_zero.mp hmem with h | h
    · exact h
    · exact absurd h hdet_ne
  have hSy : w.ofLp 1 = 0 := by
    have hmem : w.ofLp 1 * (u.ofLp 0 * v.ofLp 1 - u.ofLp 1 * v.ofLp 0) = 0 := by
      linear_combination (-(v.ofLp 0)) * horth1 + (u.ofLp 0) * horth2
    rw [← hdet] at hmem
    rcases mul_eq_zero.mp hmem with h | h
    · exact h
    · exact absurd h hdet_ne
  have h60 : ‖w‖ ^ 2 = 0 := by
    have h := norm_sq_coord_eq w
    rw [hSx, hSy] at h
    simpa using h
  have h70 : ‖w‖ = 0 := (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h60
  exact norm_eq_zero.mp h70

private lemma centroid_eq_zero {a b c : EuclideanSpace ℝ (Fin 2)} {r s : ℝ}
    (ha : ‖a‖ = r) (hb : ‖b‖ = r) (hc : ‖c‖ = r)
    (hab : ‖a - b‖ = s) (hbc : ‖b - c‖ = s) (hca : ‖c - a‖ = s)
    (hs : 0 < s) : a + b + c = 0 := by
  have tab : inner ℝ a b = inner ℝ b c := by
    have e : ‖a - b‖ ^ 2 = ‖b - c‖ ^ 2 := by rw [hab, hbc]
    rw [norm_sub_sq_real, ha, hb, norm_sub_sq_real, hb, hc] at e
    linarith
  have tbc : inner ℝ b c = inner ℝ c a := by
    have e : ‖b - c‖ ^ 2 = ‖c - a‖ ^ 2 := by rw [hbc, hca]
    rw [norm_sub_sq_real, hb, hc, norm_sub_sq_real, hc, ha] at e
    linarith
  have h1 : inner ℝ (a + b + c) (a - b) = 0 := by
    have c1 : inner ℝ b a = inner ℝ a b := real_inner_comm a b
    have c2 : inner ℝ c b = inner ℝ b c := real_inner_comm b c
    simp only [inner_add_left, inner_sub_right, real_inner_self_eq_norm_sq, ha, hb]
    linarith
  have h2 : inner ℝ (a + b + c) (b - c) = 0 := by
    have d1 : inner ℝ a c = inner ℝ c a := real_inner_comm c a
    have d2 : inner ℝ c b = inner ℝ b c := real_inner_comm b c
    simp only [inner_add_left, inner_sub_right, real_inner_self_eq_norm_sq, hb, hc]
    linarith
  have huv : ‖(a - b) + (b - c)‖ = s := by
    have e : (a - b) + (b - c) = a - c := by abel
    have e2 : a - c = -(c - a) := by abel
    rw [e, e2, norm_neg]
    exact hca
  exact perp_eq_zero_of_norm_eq h1 h2 hab hbc huv hs

/-- **Van Schooten's theorem.** Let $A$, $B$, $C$, $P$ and $O$ be points of the Euclidean plane
$\mathbb{R}^2$ and let $r > 0$. Suppose that $AB = BC = CA$, that $A$, $B$, $C$ and $P$ lie
on the circle of radius $r$ about $O$, and that $CP > AP$ and $CP > BP$. Then
$PA + PB = PC$.

No hypothesis that $P$ differs from $A$, $B$ or $C$ is needed. -/
theorem vanSchooten_general (A B C P O : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (hr : 0 < r)
    (he1 : dist A B = dist B C) (he2 : dist B C = dist C A)
    (hA : A ∈ Metric.sphere O r) (hB : B ∈ Metric.sphere O r)
    (hC : C ∈ Metric.sphere O r) (hP : P ∈ Metric.sphere O r)
    (h1 : dist C P > dist A P) (h2 : dist C P > dist B P) :
    dist P A + dist P B = dist P C := by
  have hAO : dist A O = r := Metric.mem_sphere.mp hA
  have hBO : dist B O = r := Metric.mem_sphere.mp hB
  have hCO : dist C O = r := Metric.mem_sphere.mp hC
  have hPO : dist P O = r := Metric.mem_sphere.mp hP
  have hrne : r ≠ 0 := ne_of_gt hr
  have hspos : 0 < dist A B := by
    by_contra hle
    have hle : dist A B ≤ 0 := not_lt.mp hle
    have hAB0 : dist A B = 0 := le_antisymm hle dist_nonneg
    have hAeqB : A = B := dist_eq_zero.mp hAB0
    have hBC0 : dist B C = 0 := by rw [← he1]; exact hAB0
    have hBeqC : B = C := dist_eq_zero.mp hBC0
    have hAeqC : A = C := hAeqB.trans hBeqC
    rw [hAeqC] at h1
    linarith
  set a : EuclideanSpace ℝ (Fin 2) := A - O with ha_def
  set b : EuclideanSpace ℝ (Fin 2) := B - O with hb_def
  set c : EuclideanSpace ℝ (Fin 2) := C - O with hc_def
  set p : EuclideanSpace ℝ (Fin 2) := P - O with hp_def
  have hanorm : ‖a‖ = r := by rw [ha_def, ← dist_eq_norm]; exact hAO
  have hbnorm : ‖b‖ = r := by rw [hb_def, ← dist_eq_norm]; exact hBO
  have hcnorm : ‖c‖ = r := by rw [hc_def, ← dist_eq_norm]; exact hCO
  have hpnorm : ‖p‖ = r := by rw [hp_def, ← dist_eq_norm]; exact hPO
  have hab : ‖a - b‖ = dist A B := by
    have e : a - b = A - B := by rw [ha_def, hb_def]; abel
    rw [e, ← dist_eq_norm]
  have hbc : ‖b - c‖ = dist A B := by
    have e : b - c = B - C := by rw [hb_def, hc_def]; abel
    rw [e, ← dist_eq_norm, he1]
  have hca : ‖c - a‖ = dist A B := by
    have e : c - a = C - A := by rw [hc_def, ha_def]; abel
    rw [e, ← dist_eq_norm, ← he2, ← he1]
  have gPA : dist P A = ‖p - a‖ := by
    have e : p - a = P - A := by rw [hp_def, ha_def]; abel
    rw [e, dist_eq_norm]
  have gPB : dist P B = ‖p - b‖ := by
    have e : p - b = P - B := by rw [hp_def, hb_def]; abel
    rw [e, dist_eq_norm]
  have gPC : dist P C = ‖p - c‖ := by
    have e : p - c = P - C := by rw [hp_def, hc_def]; abel
    rw [e, dist_eq_norm]
  rw [gPA, gPB, gPC]
  have h1n : ‖c - p‖ > ‖a - p‖ := by
    have e1 : c - p = C - P := by rw [hc_def, hp_def]; abel
    have e2 : a - p = A - P := by rw [ha_def, hp_def]; abel
    rw [e1, e2, ← dist_eq_norm, ← dist_eq_norm]
    exact h1
  have h2n : ‖c - p‖ > ‖b - p‖ := by
    have e1 : c - p = C - P := by rw [hc_def, hp_def]; abel
    have e2 : b - p = B - P := by rw [hb_def, hp_def]; abel
    rw [e1, e2, ← dist_eq_norm, ← dist_eq_norm]
    exact h2
  have hcent : a + b + c = 0 :=
    centroid_eq_zero hanorm hbnorm hcnorm hab hbc hca hspos
  -- coordinate setup
  have hcc : (c.ofLp 0) ^ 2 + (c.ofLp 1) ^ 2 = r ^ 2 := by
    rw [← norm_sq_coord_eq c, hcnorm]
  have han0 : (a.ofLp 0) ^ 2 + (a.ofLp 1) ^ 2 = r ^ 2 := by
    rw [← norm_sq_coord_eq a, hanorm]
  have hbn0 : (b.ofLp 0) ^ 2 + (b.ofLp 1) ^ 2 = r ^ 2 := by
    rw [← norm_sq_coord_eq b, hbnorm]
  have hpn0 : (p.ofLp 0) ^ 2 + (p.ofLp 1) ^ 2 = r ^ 2 := by
    rw [← norm_sq_coord_eq p, hpnorm]
  set px : ℝ := (p.ofLp 0 * c.ofLp 0 + p.ofLp 1 * c.ofLp 1) / r with hpx_def
  set py : ℝ := (-p.ofLp 0 * c.ofLp 1 + p.ofLp 1 * c.ofLp 0) / r with hpy_def
  set ax : ℝ := (a.ofLp 0 * c.ofLp 0 + a.ofLp 1 * c.ofLp 1) / r with hax_def
  set ay : ℝ := (-a.ofLp 0 * c.ofLp 1 + a.ofLp 1 * c.ofLp 0) / r with hay_def
  set bx : ℝ := (b.ofLp 0 * c.ofLp 0 + b.ofLp 1 * c.ofLp 1) / r with hbx_def
  set byy : ℝ := (-b.ofLp 0 * c.ofLp 1 + b.ofLp 1 * c.ofLp 0) / r with hby_def
  set cx : ℝ := (c.ofLp 0 * c.ofLp 0 + c.ofLp 1 * c.ofLp 1) / r with hcx_def
  set cy : ℝ := (-c.ofLp 0 * c.ofLp 1 + c.ofLp 1 * c.ofLp 0) / r with hcy_def
  have hcx : cx = r := by
    have e : c.ofLp 0 * c.ofLp 0 + c.ofLp 1 * c.ofLp 1 = r ^ 2 := by
      linear_combination hcc
    rw [hcx_def, e, div_eq_iff hrne]
    ring
  have hcy : cy = 0 := by
    have e : -c.ofLp 0 * c.ofLp 1 + c.ofLp 1 * c.ofLp 0 = 0 := by ring
    rw [hcy_def, e, zero_div]
  have hcent0 : a.ofLp 0 + b.ofLp 0 + c.ofLp 0 = 0 := by
    have h := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x.ofLp 0) hcent
    simpa using h
  have hcent1 : a.ofLp 1 + b.ofLp 1 + c.ofLp 1 = 0 := by
    have h := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x.ofLp 1) hcent
    simpa using h
  have hsumx : ax + bx + cx = 0 := by
    have e : ax + bx + cx
        = ((a.ofLp 0 + b.ofLp 0 + c.ofLp 0) * c.ofLp 0
          + (a.ofLp 1 + b.ofLp 1 + c.ofLp 1) * c.ofLp 1) / r := by
      rw [hax_def, hbx_def, hcx_def, ← add_div, ← add_div]
      congr 1
      ring
    rw [e, hcent0, hcent1]
    simp
  have hsumy : ay + byy + cy = 0 := by
    have e : ay + byy + cy
        = ((a.ofLp 0 + b.ofLp 0 + c.ofLp 0) * (-c.ofLp 1)
          + (a.ofLp 1 + b.ofLp 1 + c.ofLp 1) * (c.ofLp 0)) / r := by
      rw [hay_def, hby_def, hcy_def, ← add_div, ← add_div]
      congr 1
      ring
    rw [e, hcent0, hcent1]
    simp
  have hu_eq : inner ℝ p a = px * ax + py * ay := by
    rw [inner_coord_eq p a, hpx_def, hpy_def, hax_def, hay_def]
    exact (rotated_inner_eq _ _ _ _ _ _ _ hrne hcc).symm
  have hv_eq : inner ℝ p b = px * bx + py * byy := by
    rw [inner_coord_eq p b, hpx_def, hpy_def, hbx_def, hby_def]
    exact (rotated_inner_eq _ _ _ _ _ _ _ hrne hcc).symm
  have hw_eq : inner ℝ p c = px * cx + py * cy := by
    rw [inner_coord_eq p c, hpx_def, hpy_def, hcx_def, hcy_def]
    exact (rotated_inner_eq _ _ _ _ _ _ _ hrne hcc).symm
  have hw_eq' : inner ℝ p c = px * r := by
    rw [hw_eq, hcx, hcy, mul_zero, add_zero]
  have hC3 : px ^ 2 + py ^ 2 = r ^ 2 := by
    rw [hpx_def, hpy_def]
    exact rotated_norm_eq _ _ _ _ _ hrne hpn0 hcc
  have han0r : ax ^ 2 + ay ^ 2 = r ^ 2 := by
    rw [hax_def, hay_def]
    exact rotated_norm_eq _ _ _ _ _ hrne han0 hcc
  have hbn0r : bx ^ 2 + byy ^ 2 = r ^ 2 := by
    rw [hbx_def, hby_def]
    exact rotated_norm_eq _ _ _ _ _ hrne hbn0 hcc
  have hsumx2 : ax + bx = -r := by linarith [hsumx, hcx]
  have hsumy2 : ay + byy = 0 := by linarith [hsumy, hcy]
  have haxbx0 : (ax - bx) * r = 0 := by
    linear_combination -(han0r) + (hbn0r) + (ax - bx) * hsumx2 + (ay - byy) * hsumy2
  have haxeqbx : ax = bx := by
    rcases mul_eq_zero.mp haxbx0 with h | h
    · linarith
    · exact absurd h hrne
  have hax : ax = -r / 2 := by linarith [hsumx2, haxeqbx]
  have hbx : bx = ax := haxeqbx.symm
  have hby : byy = -ay := by linarith [hsumy2]
  rw [hax] at hu_eq
  rw [hbx, hby, hax] at hv_eq
  rw [hax] at han0r
  have hay2 : ay ^ 2 = 3 * r ^ 2 / 4 := by linarith [han0r]
  -- norm squared facts
  have hX2 : ‖p - a‖ ^ 2 = r ^ 2 - 2 * inner ℝ p a + r ^ 2 := by
    rw [norm_sub_sq_real, hpnorm, hanorm]
  have hY2 : ‖p - b‖ ^ 2 = r ^ 2 - 2 * inner ℝ p b + r ^ 2 := by
    rw [norm_sub_sq_real, hpnorm, hbnorm]
  have hZ2 : ‖p - c‖ ^ 2 = r ^ 2 - 2 * inner ℝ p c + r ^ 2 := by
    rw [norm_sub_sq_real, hpnorm, hcnorm]
  have hCa2 : ‖c - p‖ ^ 2 = r ^ 2 - 2 * inner ℝ c p + r ^ 2 := by
    rw [norm_sub_sq_real, hcnorm, hpnorm]
  have hAa2 : ‖a - p‖ ^ 2 = r ^ 2 - 2 * inner ℝ a p + r ^ 2 := by
    rw [norm_sub_sq_real, hanorm, hpnorm]
  have hBa2 : ‖b - p‖ ^ 2 = r ^ 2 - 2 * inner ℝ b p + r ^ 2 := by
    rw [norm_sub_sq_real, hbnorm, hpnorm]
  have hXpos : 0 < ‖c - p‖ := (norm_nonneg _).trans_lt h1n
  have hsq1 : ‖c - p‖ ^ 2 > ‖a - p‖ ^ 2 := by
    have hgt : 0 < ‖c - p‖ - ‖a - p‖ := by linarith [h1n]
    have hnn := norm_nonneg (a - p)
    have hsum : 0 < ‖c - p‖ + ‖a - p‖ := by linarith [hXpos]
    have hmul := mul_pos hgt hsum
    have e : (‖c - p‖ - ‖a - p‖) * (‖c - p‖ + ‖a - p‖)
        = ‖c - p‖ ^ 2 - ‖a - p‖ ^ 2 := by ring
    rw [e] at hmul
    linarith [hmul]
  have hsq2 : ‖c - p‖ ^ 2 > ‖b - p‖ ^ 2 := by
    have hgt : 0 < ‖c - p‖ - ‖b - p‖ := by linarith [h2n]
    have hnn := norm_nonneg (b - p)
    have hsum : 0 < ‖c - p‖ + ‖b - p‖ := by linarith [hXpos]
    have hmul := mul_pos hgt hsum
    have e : (‖c - p‖ - ‖b - p‖) * (‖c - p‖ + ‖b - p‖)
        = ‖c - p‖ ^ 2 - ‖b - p‖ ^ 2 := by ring
    rw [e] at hmul
    linarith [hmul]
  have hPU : inner ℝ p a > inner ℝ p c := by
    have cpu : inner ℝ c p = inner ℝ p c := real_inner_comm p c
    have apu : inner ℝ a p = inner ℝ p a := real_inner_comm p a
    linarith [hsq1, hCa2, hAa2]
  have hPV : inner ℝ p b > inner ℝ p c := by
    have cpu : inner ℝ c p = inner ℝ p c := real_inner_comm p c
    have bpu : inner ℝ b p = inner ℝ p b := real_inner_comm p b
    linarith [hsq2, hCa2, hBa2]
  have hsum : inner ℝ p a + inner ℝ p b + inner ℝ p c = 0 := by
    rw [← inner_add_right, ← inner_add_right, hcent]
    exact inner_zero_right p
  have hm1 : py * ay > 3 * px * r / 2 := by linarith [hPU, hu_eq, hw_eq']
  have hm2 : -(py * ay) > 3 * px * r / 2 := by linarith [hPV, hv_eq, hw_eq']
  have hpx0 : px < 0 := by
    by_contra hcon
    have hcon' : 0 ≤ px := not_lt.mp hcon
    have hle := mul_nonneg hcon' (le_of_lt hr)
    linarith [hm1, hm2, hle]
  have hmsq : (py * ay) ^ 2 < (3 * px * r / 2) ^ 2 := by
    have hA : 0 < py * ay - 3 * px * r / 2 := by linarith [hm1]
    have hB : 0 < -(py * ay) - 3 * px * r / 2 := by linarith [hm2]
    have hAB := mul_pos hA hB
    linarith [hAB]
  have hpy3 : py ^ 2 < 3 * px ^ 2 := by
    have e1 : (py * ay) ^ 2 = py ^ 2 * ay ^ 2 := by ring
    have e2 : (3 * px * r / 2) ^ 2 = 9 * (px ^ 2) * (r ^ 2) / 4 := by ring
    rw [e1, e2, hay2] at hmsq
    have hr2 : (0 : ℝ) < r ^ 2 := sq_pos_of_ne_zero hrne
    have hr24 : (0 : ℝ) < 3 * r ^ 2 / 4 := by linarith [hr2]
    have h3eq : (3 * px ^ 2) * (3 * r ^ 2 / 4) = 9 * px ^ 2 * r ^ 2 / 4 := by ring
    have h3 : py ^ 2 * (3 * r ^ 2 / 4) < (3 * px ^ 2) * (3 * r ^ 2 / 4) := by
      rw [h3eq]; exact hmsq
    exact lt_of_mul_lt_mul_right h3 (le_of_lt hr24)
  have h4 : r ^ 2 < 4 * px ^ 2 := by linarith [hC3, hpy3]
  have hpx_neg : px < -r / 2 := by
    by_contra hcon
    have hcon' : -r / 2 ≤ px := not_lt.mp hcon
    have h5 : px ^ 2 ≤ r ^ 2 / 4 := by
      have e : px ^ 2 - r ^ 2 / 4 = (px + r / 2) * (px - r / 2) := by ring
      have h6 : (px + r / 2) * (px - r / 2) ≤ 0 := by
        apply mul_nonpos_of_nonneg_of_nonpos
        · linarith [hcon']
        · linarith [hpx0, hr]
      linarith [e, h6]
    linarith [h4, h5]
  have hXYnn : 0 ≤ -(r ^ 2 + 2 * inner ℝ p c) := by
    have h1nn : 0 < -r - 2 * px := by linarith [hpx_neg]
    have h2nn : 0 < r * (-r - 2 * px) := mul_pos hr h1nn
    rw [hw_eq']
    linarith [h2nn]
  have hprod : (px * (-r / 2) + py * ay) * (px * (-r / 2) + py * (-ay))
      = r ^ 2 * px ^ 2 / 4 - py ^ 2 * (3 * r ^ 2 / 4) := by
    linear_combination -(py ^ 2) * hay2
  have hcoord : 3 * r ^ 4 + 4 * (inner ℝ p a) * (inner ℝ p b)
      - 4 * (inner ℝ p c) ^ 2 = 0 := by
    rw [hu_eq, hv_eq, hw_eq']
    linear_combination 4 * hprod - 3 * r ^ 2 * hC3
  have key : (2 * r ^ 2 - 2 * (inner ℝ p a)) * (2 * r ^ 2 - 2 * (inner ℝ p b))
      - (-(r ^ 2 + 2 * (inner ℝ p c))) ^ 2
      = (3 * r ^ 4 + 4 * (inner ℝ p a) * (inner ℝ p b) - 4 * (inner ℝ p c) ^ 2)
        - 4 * r ^ 2 * ((inner ℝ p a) + (inner ℝ p b) + (inner ℝ p c)) := by
    ring
  have hXYsq : (‖p - a‖ * ‖p - b‖) ^ 2 = (-(r ^ 2 + 2 * inner ℝ p c)) ^ 2 := by
    rw [mul_pow, hX2, hY2]
    rw [hcoord, hsum] at key
    linear_combination key
  have hXY : ‖p - a‖ * ‖p - b‖ = -(r ^ 2 + 2 * inner ℝ p c) := by
    have h1pos : 0 ≤ ‖p - a‖ * ‖p - b‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have h2 : √((‖p - a‖ * ‖p - b‖) ^ 2) = √((-(r ^ 2 + 2 * inner ℝ p c)) ^ 2) := by
      rw [hXYsq]
    rw [Real.sqrt_sq h1pos, Real.sqrt_sq hXYnn] at h2
    exact h2
  have hfin_sq : (‖p - a‖ + ‖p - b‖) ^ 2 = (‖p - c‖) ^ 2 := by
    rw [add_pow_two, hX2, hY2, hZ2]
    linear_combination 2 * hXY - 2 * hsum
  have hfin : ‖p - a‖ + ‖p - b‖ = ‖p - c‖ := by
    have h1pos : 0 ≤ ‖p - a‖ + ‖p - b‖ :=
      add_nonneg (norm_nonneg _) (norm_nonneg _)
    have h2nn : 0 ≤ ‖p - c‖ := norm_nonneg _
    have h2 : √((‖p - a‖ + ‖p - b‖) ^ 2) = √(‖p - c‖ ^ 2) := by rw [hfin_sq]
    rw [Real.sqrt_sq h1pos, Real.sqrt_sq h2nn] at h2
    exact h2
  exact hfin

/-- **Van Schooten's theorem with distinctness hypotheses.** Let $A$, $B$, $C$, $P$ and $O$ be
points of the Euclidean plane $\mathbb{R}^2$ and let $r > 0$. Suppose that $AB = BC = CA$,
that $A$, $B$, $C$ and $P$ lie on the circle of radius $r$ about $O$, that $P \ne A$,
$P \ne B$ and $P \ne C$, and that $CP > AP$ and $CP > BP$. Then $PA + PB = PC$.

In the source, $P$ is a point on the arc $AB$ of the circumcircle not containing $C$; here that
condition is expressed by $CP > AP$ and $CP > BP$.

Source: https://en.wikipedia.org/wiki/Van_Schooten%27s_theorem.
It follows from `vanSchooten_general`; the hypotheses `P ≠ A`, `P ≠ B` and `P ≠ C` are unused
and keep the source's shape.
Proves `Wanted` entry `vanSchooten`.
-/
theorem vanSchooten : ∀ (A B C P O : EuclideanSpace ℝ (Fin 2)) (r : ℝ),
  0 < r →
  dist A B = dist B C →
  dist B C = dist C A →
  A ∈ Metric.sphere O r →
  B ∈ Metric.sphere O r →
  C ∈ Metric.sphere O r →
  P ∈ Metric.sphere O r →
  P ≠ A → P ≠ B → P ≠ C →
  dist C P > dist A P →
  dist C P > dist B P →
  dist P A + dist P B = dist P C := by
  intro A B C P O r hr he1 he2 hA hB hC hP _ _ _ h1 h2
  exact vanSchooten_general A B C P O r hr he1 he2 hA hB hC hP h1 h2

end

end MetaMathlibExt
