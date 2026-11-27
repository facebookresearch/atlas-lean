/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Roots

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.RingTheory.Polynomial.SmallDegreeVieta

/-!
# Marden's theorem

This file proves that the critical points of a cubic with three noncollinear complex roots are the
foci of the ellipse tangent to the three side lines of the root triangle at their midpoints.
-/

@[expose] public section

namespace MetaMathlibExt

private lemma marden_vertices_ne {a b c : ℂ} (h : ((b - a) / (c - a)).im ≠ 0) :
    a ≠ b ∧ b ≠ c ∧ c ≠ a := by
  have hab : a ≠ b := by
    intro hab
    subst b
    simp at h
  have hca : c ≠ a := by
    intro hca
    subst c
    simp at h
  have hbc : b ≠ c := by
    intro hbc
    subst c
    have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
    simp [hba] at h
  exact ⟨hab, hbc, hca⟩

private lemma marden_area_ne_of_im_div_ne {z w : ℂ} (h : (z / w).im ≠ 0) :
    z.im * w.re - z.re * w.im ≠ 0 := by
  intro harea
  apply h
  rw [Complex.div_im, ← sub_div, harea, zero_div]

private lemma marden_im_div_ne_of_area_ne {z w : ℂ}
    (h : z.im * w.re - z.re * w.im ≠ 0) : (z / w).im ≠ 0 := by
  intro him
  rw [Complex.div_im, ← sub_div] at him
  rcases div_eq_zero_iff.mp him with harea | hw
  · exact h harea
  · apply h
    rw [Complex.normSq_eq_zero.mp hw]
    simp

private lemma marden_area_cyclic (a b c : ℂ) :
    (c - b).im * (a - b).re - (c - b).re * (a - b).im =
        (b - a).im * (c - a).re - (b - a).re * (c - a).im ∧
      (a - c).im * (b - c).re - (a - c).re * (b - c).im =
        (b - a).im * (c - a).re - (b - a).re * (c - a).im := by
  constructor <;> simp only [Complex.sub_re, Complex.sub_im] <;> ring

private lemma marden_cyclic_nondegenerate {a b c : ℂ}
    (h : ((b - a) / (c - a)).im ≠ 0) :
    ((c - b) / (a - b)).im ≠ 0 ∧ ((a - c) / (b - c)).im ≠ 0 := by
  have harea := marden_area_ne_of_im_div_ne h
  constructor
  · apply marden_im_div_ne_of_area_ne
    rw [(marden_area_cyclic a b c).1]
    exact harea
  · apply marden_im_div_ne_of_area_ne
    rw [(marden_area_cyclic a b c).2]
    exact harea

private lemma marden_derivative (a b c : ℂ) :
    Polynomial.derivative
        ((Polynomial.X - Polynomial.C a) *
          (Polynomial.X - Polynomial.C b) *
          (Polynomial.X - Polynomial.C c)) =
      Polynomial.C 3 * Polynomial.X ^ 2 -
        Polynomial.C (2 * (a + b + c)) * Polynomial.X +
        Polynomial.C (a * b + b * c + c * a) := by
  simp only [Polynomial.derivative_mul, Polynomial.derivative_sub,
    Polynomial.derivative_X, Polynomial.derivative_C]
  simp only [map_add, map_mul, map_ofNat]
  ring

private lemma marden_critical_points (a b c : ℂ) :
    ∃ f1 f2 : ℂ,
      Polynomial.roots (Polynomial.derivative
        ((Polynomial.X - Polynomial.C a) *
          (Polynomial.X - Polynomial.C b) *
          (Polynomial.X - Polynomial.C c))) = {f1, f2} ∧
      f1 + f2 = 2 * (a + b + c) / 3 ∧
      f1 * f2 = (a * b + b * c + c * a) / 3 := by
  let p := Polynomial.derivative
    ((Polynomial.X - Polynomial.C a) *
      (Polynomial.X - Polynomial.C b) *
      (Polynomial.X - Polynomial.C c))
  have hp : p = Polynomial.C 3 * Polynomial.X ^ 2 +
      Polynomial.C (-(2 * (a + b + c))) * Polynomial.X +
      Polynomial.C (a * b + b * c + c * a) := by
    dsimp [p]
    rw [marden_derivative]
    simp only [map_neg, map_mul, map_add, map_ofNat]
    ring
  have hdegree : p.natDegree = 2 := by
    rw [hp]
    compute_degree <;> norm_num
  have hcard : p.roots.card = 2 := by
    rw [IsAlgClosed.card_roots_eq_natDegree, hdegree]
  rcases Multiset.card_eq_two.mp hcard with ⟨f1, f2, hroots⟩
  have hvieta := (Polynomial.roots_quadratic_eq_pair_iff_of_ne_zero'
    (R := ℂ) (a := 3) (b := -(2 * (a + b + c)))
    (c := a * b + b * c + c * a) (x1 := f1) (x2 := f2) (by norm_num)).mp
    (hp ▸ hroots)
  refine ⟨f1, f2, hroots, ?_, hvieta.2⟩
  convert hvieta.1 using 1
  ring

private lemma marden_midpoint_data {a b c f1 f2 : ℂ}
    (hsum : f1 + f2 = 2 * (a + b + c) / 3)
    (hprod : f1 * f2 = (a * b + b * c + c * a) / 3) :
    ((a + b) / 2 - f1) * ((a + b) / 2 - f2) = -(b - a) ^ 2 / 12 ∧
      ((a + b) / 2 - f1) + ((a + b) / 2 - f2) = (a + b - 2 * c) / 3 := by
  constructor
  · calc
      ((a + b) / 2 - f1) * ((a + b) / 2 - f2) =
          ((a + b) / 2) ^ 2 - (a + b) / 2 * (f1 + f2) + f1 * f2 := by ring
      _ = -(b - a) ^ 2 / 12 := by rw [hsum, hprod]; ring
  · rw [show ((a + b) / 2 - f1) + ((a + b) / 2 - f2) =
      a + b - (f1 + f2) by ring, hsum]
    ring

private lemma marden_distance_sum_sq (u v : ℂ) :
    (‖u‖ + ‖v‖) ^ 2 =
      (‖u + v‖ ^ 2 + ‖u - v‖ ^ 2) / 2 + 2 * ‖u * v‖ := by
  rw [parallelogram_law_with_norm ℂ, norm_mul]
  ring

private lemma marden_symmetric_midpoint_norm (a b c : ℂ) :
    ‖a + b - 2 * c‖ ^ 2 / 18 + ‖b - a‖ ^ 2 / 6 =
        ‖b + c - 2 * a‖ ^ 2 / 18 + ‖c - b‖ ^ 2 / 6 ∧
      ‖a + b - 2 * c‖ ^ 2 / 18 + ‖b - a‖ ^ 2 / 6 =
        ‖c + a - 2 * b‖ ^ 2 / 18 + ‖a - c‖ ^ 2 / 6 := by
  constructor
  · simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
    norm_num
    ring
  · simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
    norm_num
    ring

private lemma marden_midpoint_sum_sq {a b c f1 f2 : ℂ}
    (hsum : f1 + f2 = 2 * (a + b + c) / 3)
    (hprod : f1 * f2 = (a * b + b * c + c * a) / 3) :
    (‖(a + b) / 2 - f1‖ + ‖(a + b) / 2 - f2‖) ^ 2 =
      ‖a + b - 2 * c‖ ^ 2 / 18 + ‖f2 - f1‖ ^ 2 / 2 + ‖b - a‖ ^ 2 / 6 := by
  have hmid := marden_midpoint_data hsum hprod
  have hdiff : ((a + b) / 2 - f1) - ((a + b) / 2 - f2) = f2 - f1 := by ring
  calc
    (‖(a + b) / 2 - f1‖ + ‖(a + b) / 2 - f2‖) ^ 2 =
        (‖((a + b) / 2 - f1) + ((a + b) / 2 - f2)‖ ^ 2 +
          ‖((a + b) / 2 - f1) - ((a + b) / 2 - f2)‖ ^ 2) / 2 +
          2 * ‖((a + b) / 2 - f1) * ((a + b) / 2 - f2)‖ :=
      marden_distance_sum_sq _ _
    _ = ‖a + b - 2 * c‖ ^ 2 / 18 + ‖f2 - f1‖ ^ 2 / 2 +
        ‖b - a‖ ^ 2 / 6 := by
      rw [hmid.2, hdiff, hmid.1]
      simp only [norm_div, norm_neg, norm_pow]
      norm_num
      ring

private lemma marden_midpoint_sums {a b c f1 f2 : ℂ}
    (hsum : f1 + f2 = 2 * (a + b + c) / 3)
    (hprod : f1 * f2 = (a * b + b * c + c * a) / 3) :
    ‖(a + b) / 2 - f1‖ + ‖(a + b) / 2 - f2‖ =
        ‖(b + c) / 2 - f1‖ + ‖(b + c) / 2 - f2‖ ∧
      ‖(a + b) / 2 - f1‖ + ‖(a + b) / 2 - f2‖ =
        ‖(c + a) / 2 - f1‖ + ‖(c + a) / 2 - f2‖ := by
  have hsum_bc : f1 + f2 = 2 * (b + c + a) / 3 := by rw [hsum]; ring
  have hprod_bc : f1 * f2 = (b * c + c * a + a * b) / 3 := by rw [hprod]; ring
  have hsum_ca : f1 + f2 = 2 * (c + a + b) / 3 := by rw [hsum]; ring
  have hprod_ca : f1 * f2 = (c * a + a * b + b * c) / 3 := by rw [hprod]; ring
  have hab := marden_midpoint_sum_sq hsum hprod
  have hbc := marden_midpoint_sum_sq hsum_bc hprod_bc
  have hca := marden_midpoint_sum_sq hsum_ca hprod_ca
  constructor
  · apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
    rw [hab, hbc]
    nlinarith [(marden_symmetric_midpoint_norm a b c).1]
  · apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
    rw [hab, hca]
    nlinarith [(marden_symmetric_midpoint_norm a b c).2]

private lemma marden_side_sum_im_ne {a b c : ℂ}
    (h : ((b - a) / (c - a)).im ≠ 0) :
    (((a + b - 2 * c) / 3) / (b - a)).im ≠ 0 := by
  apply marden_im_div_ne_of_area_ne
  have harea := marden_area_ne_of_im_div_ne h
  rw [show
    ((a + b - 2 * c) / 3).im * (b - a).re -
        ((a + b - 2 * c) / 3).re * (b - a).im =
      (2 / 3 : ℝ) *
        ((b - a).im * (c - a).re - (b - a).re * (c - a).im) by
    simp only [Complex.div_re, Complex.div_im, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
    norm_num
    ring]
  exact mul_ne_zero (by norm_num) harea

private lemma marden_focus_off_line {a b c f1 f2 : ℂ}
    (h : ((b - a) / (c - a)).im ≠ 0)
    (hsum : f1 + f2 = 2 * (a + b + c) / 3)
    (hprod : f1 * f2 = (a * b + b * c + c * a) / 3) :
    (((a + b) / 2 - f1) / (b - a)).im ≠ 0 := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (marden_vertices_ne h).1.symm
  have hmid := marden_midpoint_data hsum hprod
  let u := ((a + b) / 2 - f1) / (b - a)
  let v := ((a + b) / 2 - f2) / (b - a)
  have huv : u * v = -(1 : ℂ) / 12 := by
    dsimp [u, v]
    rw [div_mul_div_comm, hmid.1]
    field_simp [hba]
  change u.im ≠ 0
  intro huim
  have hu_ne : u ≠ 0 := by
    intro hu
    rw [hu, zero_mul] at huv
    norm_num at huv
  have hu_re : u.re ≠ 0 := by
    intro hre
    apply hu_ne
    apply Complex.ext
    · simpa using hre
    · simpa using huim
  have hvim : v.im = 0 := by
    have himul := congrArg Complex.im huv
    simp only [Complex.mul_im] at himul
    norm_num [huim] at himul
    exact himul.resolve_left hu_re
  have huvsum : u + v = ((a + b - 2 * c) / 3) / (b - a) := by
    dsimp [u, v]
    rw [← add_div, hmid.2]
  apply marden_side_sum_im_ne h
  have him := congrArg Complex.im huvsum
  simpa [huim, hvim] using him.symm

private lemma marden_conj_partner {u v : ℂ} (hu : u ≠ 0)
    (huv : u * v = -(1 : ℂ) / 12) :
    (starRingEnd ℂ) v = -((1 / (12 * Complex.normSq u) : ℝ) : ℂ) * u := by
  have hv : v = (-(1 : ℂ) / 12) / u := by
    apply (eq_div_iff hu).2
    rw [mul_comm]
    exact huv
  rw [hv, map_div₀, map_div₀, map_neg, map_one, map_ofNat]
  apply (div_eq_iff ((map_ne_zero (starRingEnd ℂ)).2 hu)).2
  rw [mul_assoc, mul_comm u ((starRingEnd ℂ) u), ← Complex.normSq_eq_conj_mul_self]
  push_cast
  field_simp [Complex.normSq_eq_zero.not.mpr hu]

private lemma marden_not_sameRay {u : ℂ} (huim : u.im ≠ 0) {k t : ℝ}
    (hk : 0 < k) (ht : t ≠ 0) :
    ¬SameRay ℝ (u + (t : ℂ)) ((k : ℂ) * u - (t : ℂ)) := by
  have hx_ne : u + (t : ℂ) ≠ 0 := by
    intro hx
    apply huim
    have him := congrArg Complex.im hx
    simpa using him
  have hy_ne : (k : ℂ) * u - (t : ℂ) ≠ 0 := by
    intro hy
    have him := congrArg Complex.im hy
    have hki : k * u.im ≠ 0 := mul_ne_zero hk.ne' huim
    apply hki
    simpa [Complex.mul_im] using him
  intro hray
  rcases hray.exists_pos_right hx_ne hy_ne with ⟨r, hr, heq⟩
  have him := congrArg Complex.im heq
  simp only [Complex.add_im, Complex.ofReal_im, add_zero, Complex.smul_im,
    Complex.sub_im, sub_zero, Complex.mul_im, Complex.ofReal_re, zero_mul,
    add_zero, smul_eq_mul] at him
  have hrk : r * k = 1 := by
    have hzero : (1 - r * k) * u.im = 0 := by nlinarith [him]
    have : 1 - r * k = 0 := (mul_eq_zero.mp hzero).resolve_right huim
    linarith
  have hre := congrArg Complex.re heq
  simp only [Complex.add_re, Complex.ofReal_re, Complex.smul_re, Complex.sub_re,
    Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero, smul_eq_mul] at hre
  have htzero : t = 0 := by
    rw [show r * (k * u.re - t) = (r * k) * u.re - r * t by ring, hrk] at hre
    nlinarith
  exact ht htzero

private lemma marden_normalized_strict {u v : ℂ}
    (huv : u * v = -(1 : ℂ) / 12) (huim : u.im ≠ 0) {t : ℝ} (ht : t ≠ 0) :
    ‖u‖ + ‖v‖ < ‖u + (t : ℂ)‖ + ‖v + (t : ℂ)‖ := by
  have hu : u ≠ 0 := by
    intro hu
    subst u
    simp at huim
  let k : ℝ := 1 / (12 * Complex.normSq u)
  have hnormSq : 0 < Complex.normSq u := Complex.normSq_pos.mpr hu
  have hk : 0 < k := by
    dsimp [k]
    positivity
  have hconj : (starRingEnd ℂ) v = -(k : ℂ) * u := by
    simpa [k] using marden_conj_partner hu huv
  have hvnorm : ‖v‖ = k * ‖u‖ := by
    calc
      ‖v‖ = ‖(starRingEnd ℂ) v‖ := (Complex.norm_conj v).symm
      _ = ‖-(k : ℂ) * u‖ := congrArg (fun z : ℂ => ‖z‖) hconj
      _ = k * ‖u‖ := by
        rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hk.le]
  have hvt : ‖v + (t : ℂ)‖ = ‖(k : ℂ) * u - (t : ℂ)‖ := by
    calc
      ‖v + (t : ℂ)‖ = ‖(starRingEnd ℂ) (v + (t : ℂ))‖ :=
        (Complex.norm_conj _).symm
      _ = ‖(starRingEnd ℂ) v + (t : ℂ)‖ := by
        rw [map_add, Complex.conj_ofReal]
      _ = ‖-(k : ℂ) * u + (t : ℂ)‖ := by rw [hconj]
      _ = ‖(k : ℂ) * u - (t : ℂ)‖ := by
        rw [show -(k : ℂ) * u + (t : ℂ) = -((k : ℂ) * u - (t : ℂ)) by ring,
          norm_neg]
  have htriangle := norm_add_lt_of_not_sameRay (marden_not_sameRay huim hk ht)
  calc
    ‖u‖ + ‖v‖ = (1 + k) * ‖u‖ := by rw [hvnorm]; ring
    _ = ‖((1 + k : ℝ) : ℂ) * u‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith : 0 ≤ 1 + k)]
    _ = ‖(u + (t : ℂ)) + ((k : ℂ) * u - (t : ℂ))‖ := by
      congr 1
      push_cast
      ring
    _ < ‖u + (t : ℂ)‖ + ‖(k : ℂ) * u - (t : ℂ)‖ := htriangle
    _ = ‖u + (t : ℂ)‖ + ‖v + (t : ℂ)‖ := by rw [hvt]

private lemma marden_strict_side {a b c f1 f2 : ℂ}
    (h : ((b - a) / (c - a)).im ≠ 0)
    (hsum : f1 + f2 = 2 * (a + b + c) / 3)
    (hprod : f1 * f2 = (a * b + b * c + c * a) / 3) :
    ∀ t : ℝ, t ≠ 0 →
      ‖(a + b) / 2 - f1‖ + ‖(a + b) / 2 - f2‖ <
        ‖(a + b) / 2 + (t : ℂ) * (b - a) - f1‖ +
          ‖(a + b) / 2 + (t : ℂ) * (b - a) - f2‖ := by
  have hd : b - a ≠ 0 := sub_ne_zero.mpr (marden_vertices_ne h).1.symm
  have hmid := marden_midpoint_data hsum hprod
  let u := ((a + b) / 2 - f1) / (b - a)
  let v := ((a + b) / 2 - f2) / (b - a)
  have huv : u * v = -(1 : ℂ) / 12 := by
    dsimp [u, v]
    rw [div_mul_div_comm, hmid.1]
    field_simp [hd]
  have huim : u.im ≠ 0 := by
    dsimp [u]
    exact marden_focus_off_line h hsum hprod
  have hu0 : (b - a) * u = (a + b) / 2 - f1 := by
    dsimp [u]
    field_simp [hd]
  have hv0 : (b - a) * v = (a + b) / 2 - f2 := by
    dsimp [v]
    field_simp [hd]
  intro t ht
  have hut : (b - a) * (u + (t : ℂ)) =
      (a + b) / 2 + (t : ℂ) * (b - a) - f1 := by
    rw [mul_add, hu0]
    ring
  have hvt : (b - a) * (v + (t : ℂ)) =
      (a + b) / 2 + (t : ℂ) * (b - a) - f2 := by
    rw [mul_add, hv0]
    ring
  have hscaled := mul_lt_mul_of_pos_left (marden_normalized_strict huv huim ht)
    (norm_pos_iff.mpr hd)
  calc
    ‖(a + b) / 2 - f1‖ + ‖(a + b) / 2 - f2‖ =
        ‖(b - a) * u‖ + ‖(b - a) * v‖ := by rw [hu0, hv0]
    _ = ‖b - a‖ * (‖u‖ + ‖v‖) := by rw [norm_mul, norm_mul]; ring
    _ < ‖b - a‖ * (‖u + (t : ℂ)‖ + ‖v + (t : ℂ)‖) := hscaled
    _ = ‖(b - a) * (u + (t : ℂ))‖ + ‖(b - a) * (v + (t : ℂ))‖ := by
      rw [norm_mul, norm_mul]
      ring
    _ = ‖(a + b) / 2 + (t : ℂ) * (b - a) - f1‖ +
        ‖(a + b) / 2 + (t : ℂ) * (b - a) - f2‖ := by rw [hut, hvt]

/-- **Marden's theorem.** Let $a, b, c$ be complex numbers such that $(b - a)/(c - a)$ has
nonzero imaginary part, so that they are the vertices of a nondegenerate triangle, and let
$p(z) = (z - a)(z - b)(z - c)$. Then there are complex numbers $f_1, f_2$ and a real number $L$
such that the roots of $p'$, counted with multiplicity, are exactly $f_1$ and $f_2$, and such
that the function $\sigma(z) = |z - f_1| + |z - f_2|$ satisfies
$\sigma((a + b)/2) = \sigma((b + c)/2) = \sigma((c + a)/2) = L$ and, for every real $t \ne 0$,
$\sigma((a + b)/2 + t(b - a)) > L$, $\sigma((b + c)/2 + t(c - b)) > L$ and
$\sigma((c + a)/2 + t(a - c)) > L$.

Thus the ellipse $\sigma(z) = L$ with foci $f_1$ and $f_2$ (a circle when $f_1 = f_2$) passes
through the midpoints of the three sides and touches each side line only at its midpoint: it is
the Steiner inellipse, and its foci are the roots of $p'$.

Proof: The statement is Marden's theorem (M. Marden, *Geometry of Polynomials*, 2nd ed.,
Math. Surveys No. 3, AMS, 1966; D. Kalman, *An Elementary Proof of Marden's Theorem*,
Amer. Math. Monthly 115(4) (2008), 330-338, <https://doi.org/10.1080/00029890.2008.11920532>).
Following [Wikipedia, *Marden's theorem*](https://en.wikipedia.org/wiki/Marden%27s_theorem),
we use Vieta's relations, the midpoint identity for the derivative, and the ellipse reflection
property expressed by a strict triangle inequality.

Proves `Wanted` entry `marden`.

Source: https://en.wikipedia.org/wiki/Marden%27s_theorem.
-/
theorem marden : ∀ (a b c : ℂ),
    ((b - a) / (c - a)).im ≠ 0 →
    ∃ (f1 f2 : ℂ) (L : ℝ),
      Polynomial.roots (Polynomial.derivative
        ((Polynomial.X - Polynomial.C a) *
          (Polynomial.X - Polynomial.C b) *
          (Polynomial.X - Polynomial.C c))) = {f1, f2} ∧
      ‖(a + b) / 2 - f1‖ + ‖(a + b) / 2 - f2‖ = L ∧
      ‖(b + c) / 2 - f1‖ + ‖(b + c) / 2 - f2‖ = L ∧
      ‖(c + a) / 2 - f1‖ + ‖(c + a) / 2 - f2‖ = L ∧
      (∀ t : ℝ, t ≠ 0 →
        L < ‖(a + b) / 2 + (t : ℂ) * (b - a) - f1‖ +
          ‖(a + b) / 2 + (t : ℂ) * (b - a) - f2‖) ∧
      (∀ t : ℝ, t ≠ 0 →
        L < ‖(b + c) / 2 + (t : ℂ) * (c - b) - f1‖ +
          ‖(b + c) / 2 + (t : ℂ) * (c - b) - f2‖) ∧
      (∀ t : ℝ, t ≠ 0 →
        L < ‖(c + a) / 2 + (t : ℂ) * (a - c) - f1‖ +
          ‖(c + a) / 2 + (t : ℂ) * (a - c) - f2‖) := by
  intro a b c h
  rcases marden_critical_points a b c with ⟨f1, f2, hroots, hsum, hprod⟩
  have hmids := marden_midpoint_sums hsum hprod
  have hcyclic := marden_cyclic_nondegenerate h
  have hsum_bc : f1 + f2 = 2 * (b + c + a) / 3 := by rw [hsum]; ring
  have hprod_bc : f1 * f2 = (b * c + c * a + a * b) / 3 := by rw [hprod]; ring
  have hsum_ca : f1 + f2 = 2 * (c + a + b) / 3 := by rw [hsum]; ring
  have hprod_ca : f1 * f2 = (c * a + a * b + b * c) / 3 := by rw [hprod]; ring
  let L := ‖(a + b) / 2 - f1‖ + ‖(a + b) / 2 - f2‖
  refine ⟨f1, f2, L, hroots, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [L] using hmids.1.symm
  · simpa [L] using hmids.2.symm
  · simpa [L] using marden_strict_side h hsum hprod
  · simpa [L, hmids.1] using
      marden_strict_side hcyclic.1 hsum_bc hprod_bc
  · simpa [L, hmids.2] using
      marden_strict_side hcyclic.2 hsum_ca hprod_ca

end MetaMathlibExt
