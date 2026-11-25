/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import MathlibExt.Analysis.Polynomial.Lagrange

/-!
# A bound for the Lebesgue function of the Chebyshev extrema

The nodal polynomial gives a cotangent formula for the Lagrange basis away from the nodes.
After reflecting the angles to the full circle, the terms group in pairs on either side of
an evaluation angle. The closest pair is bounded separately, and a telescoping sum of
logarithms of sines bounds the rest. This gives the upper bound of Trefethen's
*Approximation Theory and Approximation Practice*, Theorem 15.2.
-/

open Finset Polynomial Real

namespace MathlibExt.Analysis.Approximation.ChebyshevInterpolationWanted

/-! ## Estimating the paired cotangent sum -/

private theorem log_lower {r : ℝ} (hr : 1 ≤ r) : 2 * (r - 1) / (r + 1) ≤ log r := by
  convert le_log_one_add_of_nonneg (sub_nonneg.mpr hr) using 1 <;> ring_nf

-- The sine of the grid spacing satisfies `(n+1) sin (π/(2n)) ≥ π/2`.
private theorem sin_spacing (n : ℕ) (hn : 1 ≤ n) : π / 2 ≤ ((n : ℝ) + 1) * sin (π / (2 * n)) := by
  let a : ℝ := π / (2 * n)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have ha : 0 < a := by dsimp [a]; positivity
  have hna : (n : ℝ) * a = π / 2 := by dsimp [a]; field_simp
  have hp : π ^ 2 ≤ 12 := by nlinarith [pi_pos, pi_lt_d2]
  have hsq : (n : ℝ) ^ 2 * a ^ 2 = π ^ 2 / 4 := by nlinarith [congrArg (· ^ 2) hna]
  have haux : (n : ℝ) + 1 ≤ 2 * (n : ℝ) ^ 2 := by nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hb : ((n : ℝ) + 1) * a ^ 2 ≤ 6 := by
    nlinarith [mul_le_mul_of_nonneg_right haux (sq_nonneg a)]
  change π / 2 ≤ ((n : ℝ) + 1) * sin a
  calc
    π / 2 = (n : ℝ) * a := hna.symm
    _ ≤ ((n : ℝ) + 1) * (a - a ^ 3 / 6) := by
      nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hb)]
    _ ≤ ((n : ℝ) + 1) * sin a := by gcongr; exact (sin_gt_sub_cube ha).le

private theorem two_sub_log_pi_half : 2 - log (π / 2) ≤ π / 2 := by
  have hp : (1 : ℝ) ≤ π / 2 := by linarith [pi_gt_d2]
  have h := log_lower hp
  have hp' : 0 < π / 2 + 1 := by linarith
  have hpoly : 2 - π / 2 ≤ 2 * (π / 2 - 1) / (π / 2 + 1) := by
    apply (le_div_iff₀ hp').mpr
    nlinarith [pi_gt_d2, sq_nonneg (π - 3.14)]
  linarith

private theorem sin_parabola {d : ℝ} (hd : 0 ≤ d) (hd' : d ≤ 1) :
    sin (π * d) ≤ 4 * d * (1 - d) := by
  let s := d - 1 / 2
  have hs : |s| ≤ 1 / 2 := abs_le.mpr ⟨by dsimp [s]; linarith, by dsimp [s]; linarith⟩
  have hb : 0 ≤ 2 * |s| := by positivity
  obtain ⟨_, hconc⟩ := strictConcaveOn_sin_Icc.concaveOn
  have h := hconc
    (x := 0) (y := π / 4) ⟨le_rfl, pi_pos.le⟩ ⟨by positivity, by linarith [pi_pos]⟩
    (a := 1 - 2 * |s|) (b := 2 * |s|) (by linarith) hb (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, sin_zero, sin_pi_div_four] at h
  have he : 2 * |s| * (π / 4) = π * |s| / 2 := by ring
  rw [he] at h
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * |s| * (√2 / 2)) h 2
  have hr := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hsq' : 2 * s ^ 2 ≤ sin (π * s / 2) ^ 2 := by
    rw [show (2 * |s| * (√2 / 2)) ^ 2 = 2 * s ^ 2 by
      calc
        _ = |s| ^ 2 * (√2) ^ 2 := by ring
        _ = _ := by rw [sq_abs, hr]; ring] at hsq
    have habs : |π * s / 2| = π * |s| / 2 := by rw [abs_div, abs_mul, abs_of_pos pi_pos]; norm_num
    rw [← habs, ← abs_sin_eq_sin_abs_of_abs_le_pi, sq_abs] at hsq
    · exact hsq
    · rw [habs]
      nlinarith [mul_le_mul_of_nonneg_left hs pi_pos.le, pi_pos]
  rw [show π * d = π / 2 + π * s by dsimp [s]; ring, add_comm, sin_add_pi_div_two,
    show π * s = 2 * (π * s / 2) by ring, cos_two_mul_eq_one_sub]
  dsimp [s] at hsq'
  nlinarith

private theorem cot_nonneg_of_pos {t : ℝ} (ht : 0 < t) (ht' : t ≤ π / 2) : 0 ≤ cot t := by
  rw [cot_eq_cos_div_sin]
  exact div_nonneg (cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [pi_pos]) ht')
    (sin_nonneg_of_nonneg_of_le_pi ht.le (by linarith [pi_pos]))

private theorem cot_le_inv {t : ℝ} (ht : 0 < t) (ht' : t ≤ π / 2) : cot t ≤ t⁻¹ := by
  rcases ht'.eq_or_lt with he | hl
  · rw [he, cot_eq_cos_div_sin, cos_pi_div_two, zero_div]
    positivity
  · rw [← tan_inv_eq_cot]
    exact (inv_le_inv₀ (lt_of_lt_of_le ht (le_tan ht.le hl)) ht).2 (le_tan ht.le hl)

-- A midpoint cotangent is bounded by a logarithmic difference on its entire cell.
private theorem cot_midpoint_le_log {l h : ℝ} (hl : 0 < l) (hh : 0 < h) (hr : l + h ≤ π / 2) :
    h * cot (l + h / 2) ≤ log (sin (l + h)) - log (sin l) := by
  have hsl := sin_pos_of_pos_of_lt_pi hl (by linarith [pi_pos])
  have hsr : 0 < sin (l + h) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [pi_pos])
  have hmid : 0 < sin (l + h / 2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [pi_pos])
  have hc : 0 < cos (h / 2) := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith⟩
  have hsin := sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos] : -(π / 2) ≤ l) hr
    (show l ≤ l + h by linarith)
  have hlog := log_lower ((one_le_div hsl).mpr hsin)
  rw [log_div hsr.ne' hsl.ne'] at hlog
  have heq : 2 * (sin (l + h) / sin l - 1) / (sin (l + h) / sin l + 1) =
      2 * tan (h / 2) * cot (l + h / 2) := by
    have hadd : sin (l + h) + sin l = 2 * sin (l + h / 2) * cos (h / 2) := by
      rw [sin_add_sin, show (l + h + l) / 2 = l + h / 2 by ring,
        show (l + h - l) / 2 = h / 2 by ring]
    have hsub : sin (l + h) - sin l = 2 * sin (h / 2) * cos (l + h / 2) := by
      rw [sin_sub_sin, show (l + h - l) / 2 = h / 2 by ring,
        show (l + h + l) / 2 = l + h / 2 by ring]
    calc
      _ = 2 * (sin (l + h) - sin l) / (sin (l + h) + sin l) := by
        have hp : 0 < sin (l + h) + sin l := by positivity
        have hq : 0 < sin (l + h) / sin l + 1 := by positivity
        field_simp
      _ = _ := by
        rw [hadd, hsub, tan_eq_sin_div_cos, cot_eq_cos_div_sin]
        field_simp
  rw [heq] at hlog
  refine le_trans ?_ hlog
  have ht := le_tan (show 0 ≤ h / 2 by positivity) (show h / 2 < π / 2 by linarith)
  exact mul_le_mul_of_nonneg_right (by linarith) (cot_nonneg_of_pos (by linarith) (by linarith))

-- Outside the closest pair, the sine-weighted contributions are bounded by the midpoint pair.
private theorem cot_pair_le_midpoint {a j d : ℝ} (ha : 0 < a) (hj : 1 ≤ j)
    (hd : 0 < d) (hd' : d < 1) (hmax : (j + 1) * a ≤ π / 2) :
    sin (π * d) * (cot ((j + d) * a) + cot ((j + 1 - d) * a)) ≤
      2 * cot ((j + 1 / 2) * a) := by
  let u := (j + d) * a
  let v := (j + 1 - d) * a
  let m := (j + 1 / 2) * a
  let t := (d - 1 / 2) * a
  change sin (π * d) * (cot u + cot v) ≤ 2 * cot m
  have hu : 0 < u := by dsimp [u]; positivity
  have hv : 0 < v := mul_pos (by linarith) ha
  have hm : 0 < m := mul_pos (by linarith) ha
  have hm' : m ≤ π / 2 := by dsimp [m]; nlinarith
  have hpa : a ≤ π / 2 := by nlinarith
  have hsu : 0 < sin u := sin_pos_of_pos_of_lt_pi hu (by dsimp [u]; nlinarith [pi_pos])
  have hsv : 0 < sin v := sin_pos_of_pos_of_lt_pi hv (by dsimp [v]; nlinarith [pi_pos])
  have hsm : 0 < sin m := sin_pos_of_pos_of_lt_pi hm (by linarith [pi_pos])
  have hnum : 0 ≤ sin (2 * m) := sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith)
  have hden : sin u * sin v = sin m ^ 2 - sin t ^ 2 := by
    have h := two_mul_sin_mul_sin u v
    rw [show u - v = 2 * t by dsimp [u, v, t]; ring,
      show u + v = 2 * m by dsimp [u, v, m]; ring,
      cos_two_mul_eq_one_sub, cos_two_mul_eq_one_sub] at h
    linarith
  have hsm' : a ≤ 2 * sin m := by
    have h := mul_le_sin ha.le hpa
    have h' := sin_le_sin_of_le_of_le_pi_div_two (x := a) (by linarith [pi_pos]) hm'
      (by dsimp [m]; nlinarith)
    have h'' : a ≤ 2 * (2 / π * a) := by
      rw [show 2 * (2 / π * a) = 4 * a / π by ring]
      exact (le_div_iff₀ pi_pos).mpr (by nlinarith [mul_le_mul_of_nonneg_left pi_lt_four.le ha.le])
    linarith
  have hs : |sin t| ≤ 2 * |d - 1 / 2| * sin m := calc
    |sin t| ≤ |t| := abs_sin_le_abs
    _ = |d - 1 / 2| * a := by simp [t, abs_of_pos ha]
    _ ≤ 2 * |d - 1 / 2| * sin m := by
      linarith only [mul_le_mul_of_nonneg_left hsm' (abs_nonneg (d - 1 / 2))]
  have hs2 := pow_le_pow_left₀ (abs_nonneg (sin t)) hs 2
  rw [sq_abs, mul_pow, mul_pow, sq_abs] at hs2
  have hcomp : sin (π * d) * sin m ^ 2 ≤ sin u * sin v := by
    rw [hden]
    nlinarith [mul_le_mul_of_nonneg_right (sin_parabola hd.le hd'.le) (sq_nonneg (sin m))]
  have hadd : cot u + cot v = sin (2 * m) / (sin u * sin v) := by
    rw [cot_eq_cos_div_sin, cot_eq_cos_div_sin, ← show u + v = 2 * m by dsimp [u, v, m]; ring,
      sin_add]
    field_simp
    ring
  have hmid : 2 * cot m = sin (2 * m) / sin m ^ 2 := by
    rw [cot_eq_cos_div_sin, sin_two_mul]
    field_simp
  rw [hadd, hmid, ← mul_div_assoc]
  apply (div_le_div_iff₀ (mul_pos hsu hsv) (sq_pos_of_pos hsm)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hcomp hnum]

private theorem cot_closest_pair {a d : ℝ} (ha : 0 < a) (ha' : a ≤ π / 2)
    (hd : 0 < d) (hd' : d < 1) :
    a * (sin (π * d) * (cot (d * a) + cot ((1 - d) * a))) ≤ 4 := by
  have he : 0 < 1 - d := sub_pos.mpr hd'
  have hsin : 0 ≤ sin (π * d) :=
    sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [pi_pos])
  have hcot₁ := cot_le_inv (mul_pos hd ha) (by nlinarith : d * a ≤ π / 2)
  have hcot₂ := cot_le_inv (mul_pos he ha) (by nlinarith : (1 - d) * a ≤ π / 2)
  calc
    _ ≤ a * (sin (π * d) * ((d * a)⁻¹ + ((1 - d) * a)⁻¹)) := by gcongr
    _ = sin (π * d) / (d * (1 - d)) := by field_simp [ha.ne', hd.ne', he.ne']; ring
    _ ≤ 4 := by rw [div_le_iff₀ (mul_pos hd he), ← mul_assoc]; exact sin_parabola hd.le hd'.le

private theorem paired_cot_sum_le {n : ℕ} (hn : 1 ≤ n) {d : ℝ} (hd : 0 < d) (hd' : d < 1) :
    sin (π * d) / (2 * n) * (∑ j ∈ range n,
      (cot (((j : ℝ) + d) * (π / (2 * n))) + cot (((j : ℝ) + 1 - d) * (π / (2 * n))))) ≤
      2 / π * log ((n : ℝ) + 1) + 1 := by
  let a : ℝ := π / (2 * n)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have ha : 0 < a := by dsimp [a]; positivity
  have hna : (n : ℝ) * a = π / 2 := by dsimp [a]; field_simp
  have ha' : a ≤ π / 2 := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [mul_le_mul_of_nonneg_right hn' ha.le]
  have hs : 0 < sin a := sin_pos_of_pos_of_lt_pi ha (by linarith [pi_pos])
  let f (j : ℕ) := sin (π * d) * (cot (((j : ℝ) + d) * a) + cot (((j : ℝ) + 1 - d) * a))
  have hstep (j : ℕ) (hj : j + 1 < n) :
      a * f (j + 1) ≤ 2 * (log (sin (((j : ℝ) + 2) * a)) - log (sin (((j : ℝ) + 1) * a))) := by
    have hj' : (j : ℝ) + 2 ≤ n := by exact_mod_cast (show j + 2 ≤ n by omega)
    have hb : ((j : ℝ) + 2) * a ≤ π / 2 := by
      rw [← hna]
      gcongr
    have hsum := cot_pair_le_midpoint (j := (j : ℝ) + 1) ha
      (by linarith [Nat.cast_nonneg (α := ℝ) j]) hd hd' (by convert hb using 1; ring)
    have hlog := cot_midpoint_le_log (l := ((j : ℝ) + 1) * a) (by positivity) ha
      (by linarith only [hb])
    have heq : ((j : ℝ) + 1) * a + a / 2 = ((j : ℝ) + 1 + 1 / 2) * a := by ring
    have heq' : ((j : ℝ) + 1) * a + a = ((j : ℝ) + 2) * a := by ring
    rw [heq, heq'] at hlog
    dsimp [f]
    push_cast
    exact (mul_le_mul_of_nonneg_left hsum ha.le).trans (by linarith only [hlog])
  have hclosest : a * f 0 ≤ 4 := by simpa [f] using cot_closest_pair ha ha' hd hd'
  have htail : (∑ j ∈ range (n - 1), a * f (j + 1)) ≤ -2 * log (sin a) := by
    let g (j : ℕ) := log (sin (((j : ℝ) + 1) * a))
    have hgn : g (n - 1) = 0 := by
      simp [g, Nat.cast_sub hn, hna]
    calc
      _ ≤ ∑ j ∈ range (n - 1), 2 * (g (j + 1) - g j) := by
        apply sum_le_sum
        intro j hj
        have hj' := mem_range.mp hj
        simpa [g, Nat.cast_add, add_assoc, one_add_one_eq_two] using hstep j (by omega)
      _ = _ := by rw [← mul_sum, sum_range_sub, hgn]; simp [g]
  have htotal : a * ∑ j ∈ range n, f j ≤ 4 - 2 * log (sin a) := by
    have hsplit := sum_range_succ' f (n - 1)
    rw [Nat.sub_add_cancel hn] at hsplit
    rw [hsplit, mul_add, mul_sum]
    linarith only [htail, hclosest]
  have hsp : π / 2 ≤ ((n : ℝ) + 1) * sin a := sin_spacing n hn
  have hconst := log_le_log (show 0 < π / 2 by positivity) hsp
  rw [log_mul (by positivity) hs.ne'] at hconst
  have hfinal : a * ∑ j ∈ range n, f j ≤ 2 * log ((n : ℝ) + 1) + π := by
    linarith only [htotal, hconst, two_sub_log_pi_half]
  have heq : sin (π * d) / (2 * n) = a * sin (π * d) / π := by
    dsimp [a]
    field_simp [pi_ne_zero]
  rw [heq]
  change a * sin (π * d) / π * _ ≤ _
  rw [show a * sin (π * d) / π * _ = (a * ∑ j ∈ range n, f j) / π by
    unfold f
    rw [← mul_sum]
    ring]
  exact (div_le_iff₀ pi_pos).2 (by
    calc
      _ ≤ 2 * log ((n : ℝ) + 1) + π := hfinal
      _ = _ := by field_simp [pi_ne_zero])

/-! ## The nodal polynomial and the Lagrange basis -/

private theorem cheb_node_injective (n : ℕ) : Function.Injective (fun j : Fin (n + 1) =>
    Chebyshev.node n j) := by
  intro i j h
  apply Fin.ext
  rcases lt_trichotomy i.val j.val with hij | hij | hij
  · exact (ne_of_lt (Chebyshev.node_lt (by omega : j.val ≤ n) hij) h.symm).elim
  · exact hij
  · exact (ne_of_lt (Chebyshev.node_lt (by omega : i.val ≤ n) hij) h).elim

-- This polynomial is a nonzero constant multiple of the nodal polynomial.
private noncomputable def chebNodal (n : ℕ) : ℝ[X] :=
  (X ^ 2 - 1) * derivative (Chebyshev.T ℝ (n : ℤ))

private theorem eval_chebNodal_cos (n : ℕ) (θ : ℝ) :
    (chebNodal n).eval (cos θ) = -(n : ℝ) * sin θ * sin ((n : ℝ) * θ) := by
  have hU := Chebyshev.U_real_cos θ ((n : ℤ) - 1)
  push_cast at hU
  rw [sub_add_cancel] at hU
  unfold chebNodal
  rw [Chebyshev.T_derivative_eq_U]
  simp only [eval_mul, eval_sub, eval_pow, eval_X, eval_one, Int.cast_natCast, eval_natCast]
  rw [show cos θ ^ 2 - 1 = -(sin θ)^2 by linarith [sin_sq_add_cos_sq θ], ← hU]
  ring

private theorem eval_chebNodal_node {n : ℕ} (hn : 1 ≤ n) (j : Fin (n + 1)) :
    (chebNodal n).eval (Chebyshev.node n j) = 0 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [Chebyshev.node, eval_chebNodal_cos,
    show (n : ℝ) * ((j.val : ℝ) * π / n) = j.val * π by field_simp, sin_nat_mul_pi, mul_zero]

private theorem chebNodal_eq {n : ℕ} (hn : 1 ≤ n) :
    chebNodal n = C (chebNodal n).leadingCoeff *
      Lagrange.nodal univ (fun j : Fin (n + 1) => Chebyshev.node n j) := by
  let v (j : Fin (n + 1)) := Chebyshev.node n j
  have hnz : n ≠ 0 := by omega
  have hcast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by rw [Nat.cast_sub hn, Nat.cast_one]
  have hdU : (Chebyshev.U ℝ ((n : ℤ) - 1)).natDegree = n - 1 := by
    rw [← hcast, Chebyshev.natDegree_U_natCast]
  have hU : Chebyshev.U ℝ ((n : ℤ) - 1) ≠ 0 :=
    Chebyshev.U_ne_zero ℝ _ (by omega)
  have hc : (n : ℝ[X]) ≠ 0 := Nat.cast_ne_zero.mpr hnz
  have hX : (X ^ 2 - 1 : ℝ[X]) ≠ 0 := by
    intro h
    have he := congrArg (eval (0 : ℝ)) h
    norm_num at he
  have hdeg : (chebNodal n).natDegree = n + 1 := by
    unfold chebNodal
    rw [Chebyshev.T_derivative_eq_U]
    have he : (X ^ 2 - 1 : ℝ[X]).natDegree = 2 := by
      simpa using (natDegree_X_pow_sub_C (n := 2) (1 : ℝ))
    rw [Int.cast_natCast, natDegree_mul hX (mul_ne_zero hc hU), he, ← C_eq_natCast,
      natDegree_C_mul (Nat.cast_ne_zero.mpr hnz), hdU]
    omega
  have hp : chebNodal n ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  have hdvd : Lagrange.nodal univ v ∣ chebNodal n := by
    rw [Lagrange.nodal_eq]
    apply prod_dvd_of_coprime
    · intro i _ j _ h
      exact isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.mpr
        (sub_ne_zero.mpr ((cheb_node_injective n).ne h)))
    · intro i _
      exact dvd_iff_isRoot.mpr (eval_chebNodal_node hn i)
  apply Eq.symm
  apply eq_of_dvd_of_natDegree_le_of_leadingCoeff
  · have hu : IsUnit (C (chebNodal n).leadingCoeff) :=
      (isUnit_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hp)).map C
    simpa only [one_mul] using mul_dvd_mul (hu.dvd : C (chebNodal n).leadingCoeff ∣ 1) hdvd
  · rw [natDegree_C_mul (leadingCoeff_ne_zero.mpr hp), Lagrange.natDegree_nodal, card_univ,
      Fintype.card_fin, hdeg]
  · simp [leadingCoeff_mul, Lagrange.nodal_monic.leadingCoeff]

private theorem cheb_ode_eval (n : ℕ) (x : ℝ) :
    (1 - x ^ 2) * ((Chebyshev.T ℝ (n : ℤ)).derivative.derivative.eval x) =
      x * (Chebyshev.T ℝ (n : ℤ)).derivative.eval x -
        (n : ℝ) ^ 2 * (Chebyshev.T ℝ (n : ℤ)).eval x := by
  simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply, eval_mul, eval_sub,
    eval_one, eval_pow, eval_X, Int.cast_natCast, eval_natCast] using
    congrArg (eval x) (Chebyshev.one_sub_X_sq_mul_derivative_derivative_T_eq_poly_in_T
      (R := ℝ) (n : ℤ))

private theorem eval_derivative_chebNodal (n : ℕ) (x : ℝ) :
    (chebNodal n).derivative.eval x =
      (n : ℝ)^2 * (Chebyshev.T ℝ (n : ℤ)).eval x +
      x * (Chebyshev.T ℝ (n : ℤ)).derivative.eval x := by
  simp only [chebNodal, derivative_mul, derivative_sub, derivative_one, sub_zero,
    derivative_pow, derivative_X, mul_one]
  norm_num
  linarith only [cheb_ode_eval n x]

private theorem abs_eval_derivative_chebNodal_node {n : ℕ} (hn : 1 ≤ n) (j : Fin (n + 1)) :
    |(chebNodal n).derivative.eval (Chebyshev.node n j)| =
      (if j.val = 0 ∨ j.val = n then 2 else 1) * (n : ℝ)^2 := by
  let x := Chebyshev.node n j
  let T := Chebyshev.T ℝ (n : ℤ)
  have hj : j.val ≤ n := by omega
  have ht : T.eval x = (-1 : ℝ) ^ j.val := Chebyshev.eval_T_real_node (mem_Iic.mpr hj)
  have ht' : |(n : ℝ)^2 * T.eval x| = (n : ℝ)^2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg _), ht, abs_pow]
    simp
  change |(chebNodal n).derivative.eval x| = _
  rw [eval_derivative_chebNodal]
  change |(n : ℝ)^2 * T.eval x + x * T.derivative.eval x| = _
  by_cases h : j.val = 0 ∨ j.val = n
  · have hx : x ^ 2 = 1 := by
      rcases h with h | h
      · simp [x, h, Chebyshev.node_eq_one]
      · simp [x, h, Chebyshev.node_eq_neg_one (by omega : n ≠ 0)]
    have hode := cheb_ode_eval n x
    change (1 - x ^ 2) * T.derivative.derivative.eval x =
      x * T.derivative.eval x - (n : ℝ)^2 * T.eval x at hode
    rw [hx, sub_self, zero_mul] at hode
    rw [ite_eq_left h, show (n : ℝ)^2 * T.eval x + x * T.derivative.eval x =
      2 * ((n : ℝ)^2 * T.eval x) by linarith only [hode], abs_mul, ht']
    norm_num
  · have hxl : -1 < x := by
      rw [← Chebyshev.node_eq_neg_one (by omega : n ≠ 0)]
      exact Chebyshev.node_lt le_rfl (by omega : j.val < n)
    have hxr : x < 1 := by
      rw [← Chebyshev.node_eq_one (n := n)]
      exact Chebyshev.node_lt hj (by omega : 0 < j.val)
    have hxx : x^2 - 1 ≠ 0 := by
      have hh := mul_pos (show 0 < x + 1 by linarith) (show 0 < 1 - x by linarith)
      exact ne_of_lt (by nlinarith : x^2 - 1 < 0)
    have hz := eval_chebNodal_node hn j
    simp only [chebNodal, eval_mul, eval_sub, eval_one, eval_pow, eval_X] at hz
    change (x ^ 2 - 1) * T.derivative.eval x = 0 at hz
    rw [ite_eq_right h, (mul_eq_zero.mp hz).resolve_left hxx, mul_zero, add_zero, ht', one_mul]

private theorem cot_add_pi (t : ℝ) : cot (t + π) = cot t := by
  rw [cot_eq_cos_div_sin, cot_eq_cos_div_sin, cos_add_pi, sin_add_pi, neg_div_neg_eq]

private theorem abs_cot_neg (t : ℝ) : |cot (-t)| = |cot t| := by
  rw [cot_eq_cos_div_sin, cot_eq_cos_div_sin, cos_neg, sin_neg, div_neg, abs_neg]

-- The cosine difference splits the Lagrange quotient into two reflected circle terms.
private theorem sin_div_cos_sub_cos {θ φ : ℝ} (h : cos θ ≠ cos φ) :
    sin θ / (cos θ - cos φ) = -(cot ((θ - φ) / 2) + cot ((θ + φ) / 2)) / 2 := by
  let u := (θ - φ) / 2
  let v := (θ + φ) / 2
  have hd : cos θ - cos φ = -2 * sin v * sin u := cos_sub_cos θ φ
  have hz : -2 * sin v * sin u ≠ 0 := hd ▸ sub_ne_zero.mpr h
  have hu : sin u ≠ 0 := right_ne_zero_of_mul hz
  have hv : sin v ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hz)
  have hs : sin θ = sin u * cos v + cos u * sin v := by
    rw [← sin_add, show u + v = θ by dsimp [u, v]; ring]
  change sin θ / (cos θ - cos φ) = -(cot u + cot v) / 2
  rw [hd, hs, cot_eq_cos_div_sin, cot_eq_cos_div_sin]
  field_simp [hu, hv]
  ring

private theorem abs_basis_le_cot {n : ℕ} (hn : 1 ≤ n) (θ : ℝ) (j : Fin (n + 1))
    (hx : cos θ ≠ Chebyshev.node n j) :
    |(Lagrange.basis univ (fun i : Fin (n + 1) => Chebyshev.node n i) j).eval (cos θ)| ≤
      (|sin ((n : ℝ) * θ)| / (2 * n)) *
        ((|cot ((θ - (j : ℕ) * π / n) / 2)| + |cot ((θ + (j : ℕ) * π / n) / 2)|) /
          (if j.val = 0 ∨ j.val = n then 2 else 1)) := by
  let v (i : Fin (n + 1)) := Chebyshev.node n i
  let p := Lagrange.nodal univ v
  let c := (chebNodal n).leadingCoeff
  let b : ℝ := if j.val = 0 ∨ j.val = n then 2 else 1
  let φ : ℝ := (j : ℕ) * π / n
  have hb : 0 < b := by dsimp [b]; split <;> positivity
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  change |(Lagrange.basis univ v j).eval (cos θ)| ≤ _
  have hw : chebNodal n = C c * p := chebNodal_eq hn
  have hd := abs_eval_derivative_chebNodal_node hn j
  change |(chebNodal n).derivative.eval (v j)| = b * (n : ℝ)^2 at hd
  rw [hw, derivative_C_mul, eval_mul, eval_C, abs_mul] at hd
  have hc : |c| ≠ 0 := by
    intro hc0
    rw [hc0, zero_mul] at hd
    exact (mul_pos hb (sq_pos_of_pos hn0)).ne' hd.symm
  have hp := eval_chebNodal_cos n θ
  rw [hw, eval_mul, eval_C] at hp
  have hpa := congrArg abs hp
  rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos hn0] at hpa
  have hβ := sin_div_cos_sub_cos (θ := θ) (φ := φ) hx
  have hβ' := congrArg abs hβ
  rw [abs_div, abs_div, abs_neg, abs_of_pos (show (0 : ℝ) < 2 by norm_num)] at hβ'
  change |(Lagrange.basis univ v j).eval (cos θ)| ≤
    (|sin ((n : ℝ) * θ)| / (2 * n)) *
      ((|cot ((θ - φ) / 2)| + |cot ((θ + φ) / 2)|) / b)
  calc
    _ = |p.eval (cos θ)| / (|p.derivative.eval (v j)| * |cos θ - v j|) := by
      rw [Lagrange.eval_basis_not_at_node (mem_univ j) hx,
        Lagrange.nodalWeight_eq_eval_derivative_nodal (mem_univ j), abs_mul, abs_mul, abs_inv,
        abs_inv, ← mul_inv, div_eq_mul_inv]
    _ = |sin ((n : ℝ) * θ)| / ((n : ℝ) * b) * (|sin θ| / |cos θ - cos φ|) := by
      have ha : |p.eval (cos θ)| = ((n : ℝ) * |sin θ| * |sin ((n : ℝ) * θ)|) / |c| := by
        apply (eq_div_iff hc).2
        linarith only [hpa]
      have he : |p.derivative.eval (v j)| = b * (n : ℝ)^2 / |c| := by
        apply (eq_div_iff hc).2
        linarith only [hd]
      change |p.eval (cos θ)| / (|p.derivative.eval (v j)| * |cos θ - cos φ|) = _
      rw [ha, he]
      have hφ : |cos θ - cos φ| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hx)
      field_simp [hc, hn0.ne', hb.ne', hφ]
    _ = |sin ((n : ℝ) * θ)| / (2 * n) * (|cot ((θ - φ) / 2) + cot ((θ + φ) / 2)| / b) := by
      rw [hβ']
      ring
    _ ≤ _ := by gcongr; exact abs_add_le _ _

/-! ## Folding and translating the angular grid -/

private theorem window_sum_eq {n : ℕ} (g : ℤ → ℝ) (hp : Function.Periodic g (2 * (n : ℤ)))
    (k : ℤ) : (∑ j ∈ range (2 * n), g (k + j)) = ∑ j ∈ range (2 * n), g j := by
  let G (k : ℤ) := ∑ j ∈ range (2 * n), g (k + j)
  have hG : Function.Periodic G 1 := by
    intro i
    by_cases hn : n = 0
    · simp [G, hn]
    obtain ⟨m, hm⟩ : ∃ m : ℕ, 2 * n = m + 1 := ⟨2 * n - 1, by omega⟩
    simp only [G, hm]
    rw [sum_range_succ (f := fun j : ℕ ↦ g (i + 1 + j)),
      sum_range_succ' (f := fun j : ℕ ↦ g (i + j))]
    have hleft : (∑ j ∈ range m, g (i + 1 + j)) =
        (∑ j ∈ range m, g (i + (↑(j + 1) : ℤ))) := by
      apply sum_congr rfl
      intro j _
      push_cast
      congr 1
      ring
    rw [hleft]
    simp only [Nat.cast_zero, add_zero]
    congr 1
    rw [show i + 1 + (m : ℤ) = i + 2 * (n : ℤ) by omega]
    exact hp i
  have h := hG.zsmul k (0 : ℤ)
  simpa [G] using h

-- Splitting a window of length `2*n` at `k` gives two sets of `n` indices.
private theorem window_sum_pairs (n : ℕ) (g : ℤ → ℝ) (k : ℤ) :
    (∑ j ∈ range (2 * n), g (k + 1 - (n : ℤ) + j)) =
      ∑ j ∈ range n, (g (k - j) + g (k + 1 + j)) := by
  rw [two_mul, sum_range_add, sum_add_distrib]
  congr 1
  · rw [← sum_range_reflect (f := fun j : ℕ ↦ g (k + 1 - (n : ℤ) + j))]
    apply sum_congr rfl
    intro j hj
    have hj' := mem_range.mp hj
    push_cast [Nat.cast_sub (show j ≤ n - 1 by omega), Nat.cast_sub (show 1 ≤ n by omega)]
    congr 1
    ring
  · apply sum_congr rfl
    intro j _
    push_cast
    congr 1
    ring

-- The two half-weights fold the reflected Lobatto grid into one full circular grid.
private theorem sum_reflected_eq {n : ℕ} (hn : 1 ≤ n) (g : ℤ → ℝ)
    (hp : Function.Periodic g (2 * (n : ℤ))) :
    (∑ j : Fin (n + 1), (g j.val + g (-(j.val : ℤ))) /
      (if j.val = 0 ∨ j.val = n then (2 : ℝ) else 1)) =
        ∑ j ∈ range n, (g (-(j : ℤ)) + g ((j : ℤ) + 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hpn : g (-(↑(m + 1) : ℤ)) = g (↑(m + 1) : ℤ) := by
    simpa only [show -(↑(m + 1) : ℤ) + 2 * ↑(m + 1) = ↑(m + 1) by ring] using
      (hp (-(↑(m + 1) : ℤ))).symm
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc, sum_add_distrib,
    sum_range_succ' (f := fun j : ℕ ↦ g (-(j : ℤ))),
    sum_range_succ (f := fun j : ℕ ↦ g ((j : ℤ) + 1))]
  simp only [Nat.cast_add, Nat.cast_one] at hpn
  simp only [Fin.val_zero, Nat.cast_zero, neg_zero, true_or, ite_true, Fin.val_succ,
    Fin.val_castSucc, Fin.val_last, or_true, Nat.cast_add, Nat.cast_one, hpn]
  have hinner (j : Fin m) : ¬ (j.val + 1 = 0 ∨ j.val + 1 = m + 1) := by omega
  simp only [ite_eq_right (hinner _), div_one, sum_add_distrib]
  rw [Fin.sum_univ_eq_sum_range (f := fun j : ℕ ↦ g ((j : ℤ) + 1)),
    Fin.sum_univ_eq_sum_range (f := fun j : ℕ ↦ g (-((j : ℤ) + 1)))]
  ring

private theorem abs_sin_shift {d : ℝ} (hd : 0 < d) (hd' : d < 1) (k : ℤ) :
    |sin (π * (d + k))| = sin (π * d) := by
  rw [show π * (d + k) = π * d + (k : ℝ) * π by ring, sin_add_int_mul_pi, abs_mul,
    abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
  exact abs_of_nonneg (sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [pi_pos]))

/-- **Lebesgue constants of Chebyshev points** (ATAP Theorem 15.2): for `n ≥ 1` the Lagrange
basis polynomials `ℓ_j` of the `n + 1` Chebyshev points satisfy
`∑_j |ℓ_j(x)| ≤ (2/π) log(n + 1) + 1` for every `x ∈ [-1, 1]`. -/
public theorem sum_abs_lagrange_basis_chebyshev_le {n : ℕ} (hn : 1 ≤ n) {x : ℝ}
    (hx : x ∈ Set.Icc (-1) 1) :
    ∑ j : Fin (n + 1),
        |(Lagrange.basis (Finset.univ : Finset (Fin (n + 1))) (fun i => Chebyshev.node n i)
          j).eval x| ≤ 2 / π * Real.log (n + 1) + 1 := by
  by_cases hnode : ∃ j : Fin (n + 1), x = Chebyshev.node n j
  · obtain ⟨j, rfl⟩ := hnode
    let v (i : Fin (n + 1)) := Chebyshev.node n i
    change Lagrange.lebesgueFunction v (v j) ≤ _
    rw [Lagrange.lebesgueFunction_at_node v (cheb_node_injective n) j]
    have hlog : 0 ≤ log ((n : ℝ) + 1) :=
      log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
    linarith [mul_nonneg (by positivity : 0 ≤ 2 / π) hlog]
  push Not at hnode
  let θ := arccos x
  have hxθ : cos θ = x := cos_arccos hx.1 hx.2
  let t : ℝ := (n : ℝ) * θ / π
  let k : ℤ := ⌊t⌋
  let d : ℝ := t - k
  let a : ℝ := π / (2 * n)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have ha : 0 < a := by dsimp [a]; positivity
  have hna : 2 * (n : ℝ) * a = π := by dsimp [a]; field_simp
  have hta : t * a = θ / 2 := by dsimp [t, a]; field_simp [pi_ne_zero]
  have ht : (n : ℝ) * θ = π * (d + k) := by dsimp [d, t]; field_simp [pi_ne_zero]; ring
  have hd' : d < 1 := Int.fract_lt_one t
  have hd : 0 < d := by
    have hk := Int.floor_le t
    change (k : ℝ) ≤ t at hk
    by_contra! hd
    have he : t = (k : ℝ) := by dsimp [d] at hd; linarith
    have ht0 : 0 ≤ t := div_nonneg (mul_nonneg hn0.le (arccos_nonneg x)) pi_pos.le
    have htn : t ≤ n := (div_le_iff₀ pi_pos).2 (by gcongr; exact arccos_le_pi x)
    have hk0 : 0 ≤ k := by rw [he] at ht0; exact_mod_cast ht0
    have hkn : k ≤ (n : ℤ) := by rw [he] at htn; exact_mod_cast htn
    have hcast : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk0
    have hj : k.toNat < n + 1 := by omega
    let j : Fin (n + 1) := ⟨k.toNat, hj⟩
    apply hnode j
    rw [← hxθ, Chebyshev.node]
    congr 1
    have hreal : (k.toNat : ℝ) = (k : ℝ) := by exact_mod_cast hcast
    change θ = (k.toNat : ℝ) * π / n
    rw [hreal, ← he]
    dsimp [t]
    field_simp [pi_ne_zero]
  let g (i : ℤ) := |cot ((t - (i : ℝ)) * a)|
  have hg : Function.Periodic g (2 * (n : ℤ)) := by
    intro i
    dsimp [g]
    push_cast
    rw [← cot_add_pi ((t - ((i : ℝ) + 2 * (n : ℝ))) * a)]
    congr 2
    nlinarith only [hna]
  have hsum : (∑ j : Fin (n + 1), (g j.val + g (-(j.val : ℤ))) /
      (if j.val = 0 ∨ j.val = n then (2 : ℝ) else 1)) =
      ∑ j ∈ range n, (cot (((j : ℝ) + d) * a) + cot (((j : ℝ) + 1 - d) * a)) := by
    rw [sum_reflected_eq hn g hg]
    have hzero := window_sum_pairs n g 0
    simp only [zero_add, zero_sub, add_comm (1 : ℤ)] at hzero
    rw [← hzero, window_sum_eq g hg, ← window_sum_eq g hg (k + 1 - (n : ℤ)), window_sum_pairs]
    apply sum_congr rfl
    intro j hj
    have hj' : (j : ℝ) + 1 ≤ n := by exact_mod_cast (show j + 1 ≤ n by simpa using mem_range.mp hj)
    have h₁ : 0 < ((j : ℝ) + d) * a := by positivity
    have h₂ : 0 < ((j : ℝ) + 1 - d) * a := mul_pos (by linarith [Nat.cast_nonneg (α := ℝ) j]) ha
    have hmax : (n : ℝ) * a = π / 2 := by linarith only [hna]
    have h₃ : ((j : ℝ) + d) * a ≤ π / 2 := by
      rw [← hmax]
      gcongr
      linarith
    have h₄ : ((j : ℝ) + 1 - d) * a ≤ π / 2 := by
      rw [← hmax]
      gcongr
      linarith
    simp only [g, Int.cast_sub, Int.cast_add, Int.cast_one, Int.cast_natCast]
    rw [show (t - ((k : ℝ) - j)) * a = ((j : ℝ) + d) * a by dsimp [d]; ring,
      show (t - ((k : ℝ) + 1 + j)) * a = -(((j : ℝ) + 1 - d) * a) by dsimp [d]; ring,
      abs_cot_neg, abs_of_nonneg (cot_nonneg_of_pos h₁ h₃), abs_of_nonneg (cot_nonneg_of_pos h₂ h₄)]
  rw [← hxθ]
  calc
    _ ≤ ∑ j : Fin (n + 1), |sin ((n : ℝ) * θ)| / (2 * n) *
        ((g j.val + g (-(j.val : ℤ))) / (if j.val = 0 ∨ j.val = n then (2 : ℝ) else 1)) := by
      apply sum_le_sum
      intro j _
      have h₁ : (θ - (j.val : ℝ) * π / n) / 2 = (t - (j.val : ℝ)) * a := by
        dsimp [a] at hta ⊢
        rw [sub_mul, hta]
        ring
      have h₂ : (θ + (j.val : ℝ) * π / n) / 2 = (t - (-(j.val : ℝ))) * a := by
        dsimp [a] at hta ⊢
        rw [sub_mul, hta]
        ring
      simpa only [g, Int.cast_neg, Int.cast_natCast, ← h₁, ← h₂] using
        abs_basis_le_cot hn θ j (hxθ ▸ hnode j)
    _ = sin (π * d) / (2 * n) * (∑ j ∈ range n,
        (cot (((j : ℝ) + d) * a) + cot (((j : ℝ) + 1 - d) * a))) := by
      rw [← mul_sum, hsum, ht, abs_sin_shift hd hd']
    _ ≤ _ := paired_cot_sum_le hn hd hd'

end MathlibExt.Analysis.Approximation.ChebyshevInterpolationWanted
