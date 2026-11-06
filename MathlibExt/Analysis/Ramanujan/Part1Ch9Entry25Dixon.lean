/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Data.Finset.Defs
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Basic

@[expose] public section

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9

namespace Entry25Dixon

open scoped Topology
open Filter

noncomputable section

def chapter9DilogCosTerm (rho angle : ℝ) (j : ℕ) : ℝ :=
  let k := j + 1
  rho ^ k * Real.cos ((k : ℝ) * angle) / ((k : ℝ) ^ 2)

def chapter9DilogSinTerm (rho angle : ℝ) (j : ℕ) : ℝ :=
  let k := j + 1
  rho ^ k * Real.sin ((k : ℝ) * angle) / ((k : ℝ) ^ 2)

/-- Complex polar form of `exp (I * t)`. -/
private lemma dixon_exp_polar (t : ℝ) : Complex.exp (Complex.I * (t : ℂ)) =
    ((Real.cos t : ℝ) : ℂ) + ((Real.sin t : ℝ) : ℂ) * Complex.I := by
  rw [mul_comm Complex.I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

private lemma dixon_exp_polar' (t : ℝ) : Complex.exp ((t : ℂ) * Complex.I) =
    ((Real.cos t : ℝ) : ℂ) + ((Real.sin t : ℝ) : ℂ) * Complex.I := by
  rw [mul_comm]; exact dixon_exp_polar t

private lemma dixon_re_z (x theta : ℝ) :
    (((x : ℂ) * Complex.exp (Complex.I * theta)) : ℂ).re = x * Real.cos theta := by
  rw [dixon_exp_polar]
  simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

private lemma dixon_im_z (x theta : ℝ) :
    (((x : ℂ) * Complex.exp (Complex.I * theta)) : ℂ).im = x * Real.sin theta := by
  rw [dixon_exp_polar]
  simp only [Complex.mul_im, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

private lemma dixon_re_one_sub_z (x theta : ℝ) :
    ((1 : ℂ) - (x : ℂ) * Complex.exp (Complex.I * theta)).re
      = 1 - x * Real.cos theta := by
  rw [Complex.sub_re, Complex.one_re, dixon_re_z]

private lemma dixon_im_one_sub_z (x theta : ℝ) :
    ((1 : ℂ) - (x : ℂ) * Complex.exp (Complex.I * theta)).im
      = -(x * Real.sin theta) := by
  rw [Complex.sub_im, Complex.one_im, dixon_im_z]; ring

private lemma dixon_normSq_one_sub_z (x theta : ℝ) :
    Complex.normSq ((1 : ℂ) - (x : ℂ) * Complex.exp (Complex.I * theta))
      = 1 - 2 * x * Real.cos theta + x ^ 2 := by
  rw [Complex.normSq_apply, dixon_re_one_sub_z, dixon_im_one_sub_z]
  have h := Real.sin_sq_add_cos_sq theta
  nlinarith [h, sq_nonneg (x * Real.cos theta), sq_nonneg (x * Real.sin theta)]

/-- The hypothesis `hxy` says `z + w = z * w`. -/
private lemma dixon_zw_mul (x y theta phi : ℝ)
    (hxy : (x : ℂ) * Complex.exp (Complex.I * theta) +
      (y : ℂ) * Complex.exp (Complex.I * phi) =
        (x * y : ℝ) * Complex.exp (Complex.I * (theta + phi))) :
    (x : ℂ) * Complex.exp (Complex.I * theta) +
      (y : ℂ) * Complex.exp (Complex.I * phi) =
        ((x : ℂ) * Complex.exp (Complex.I * theta)) *
        ((y : ℂ) * Complex.exp (Complex.I * phi)) := by
  rw [hxy]
  push_cast
  have hexp : Complex.exp (Complex.I * ((theta : ℂ) + phi)) =
      Complex.exp (Complex.I * theta) * Complex.exp (Complex.I * phi) := by
    rw [mul_add, Complex.exp_add]
  rw [hexp]
  ring

private lemma dixon_norm_z (x theta : ℝ) (hx0 : 0 ≤ x) :
    ‖((x : ℂ) * Complex.exp (Complex.I * theta))‖ = x := by
  have e : ‖Complex.exp (Complex.I * (theta : ℂ))‖ = 1 := by
    rw [mul_comm Complex.I]
    exact Complex.norm_exp_ofReal_mul_I theta
  rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0, e, mul_one]

private lemma dixon_z_ne_one (x y theta phi : ℝ)
    (h : (x : ℂ) * Complex.exp (Complex.I * theta) +
      (y : ℂ) * Complex.exp (Complex.I * phi) =
        ((x : ℂ) * Complex.exp (Complex.I * theta)) *
        ((y : ℂ) * Complex.exp (Complex.I * phi))) :
    (x : ℂ) * Complex.exp (Complex.I * theta) ≠ 1 := by
  intro hz
  have h2 : (1 : ℂ) + (y : ℂ) * Complex.exp (Complex.I * phi) =
      (1 : ℂ) * ((y : ℂ) * Complex.exp (Complex.I * phi)) := by
    rw [← hz]; exact h
  rw [one_mul] at h2
  have h1 : (1 : ℂ) = 0 := by
    have h3 := congrArg (· - (y : ℂ) * Complex.exp (Complex.I * phi)) h2
    simp at h3
  exact one_ne_zero h1

private lemma dixon_w_eq_div (x y theta phi : ℝ)
    (h : (x : ℂ) * Complex.exp (Complex.I * theta) +
      (y : ℂ) * Complex.exp (Complex.I * phi) =
        ((x : ℂ) * Complex.exp (Complex.I * theta)) *
        ((y : ℂ) * Complex.exp (Complex.I * phi)))
    (hz : (x : ℂ) * Complex.exp (Complex.I * theta) ≠ 1) :
    (y : ℂ) * Complex.exp (Complex.I * phi) =
      ((x : ℂ) * Complex.exp (Complex.I * theta)) /
        (((x : ℂ) * Complex.exp (Complex.I * theta)) - 1) := by
  have hsub : ((x : ℂ) * Complex.exp (Complex.I * theta)) - 1 ≠ 0 :=
    sub_ne_zero.mpr hz
  have key : ((y : ℂ) * Complex.exp (Complex.I * phi)) *
      (((x : ℂ) * Complex.exp (Complex.I * theta)) - 1) =
        (x : ℂ) * Complex.exp (Complex.I * theta) := by
    linear_combination -h
  exact (eq_div_iff hsub).mpr key

private lemma dixon_re_le_half (x y theta phi : ℝ)
    (h : (x : ℂ) * Complex.exp (Complex.I * theta) +
      (y : ℂ) * Complex.exp (Complex.I * phi) =
        ((x : ℂ) * Complex.exp (Complex.I * theta)) *
        ((y : ℂ) * Complex.exp (Complex.I * phi)))
    (hw : ‖(y : ℂ) * Complex.exp (Complex.I * phi)‖ ≤ 1) :
    (((x : ℂ) * Complex.exp (Complex.I * theta)) : ℂ).re ≤ 1 / 2 := by
  have hz1 : (x : ℂ) * Complex.exp (Complex.I * theta) ≠ 1 :=
    dixon_z_ne_one x y theta phi h
  have hw_eq : (y : ℂ) * Complex.exp (Complex.I * phi) =
      ((x : ℂ) * Complex.exp (Complex.I * theta)) /
        (((x : ℂ) * Complex.exp (Complex.I * theta)) - 1) :=
    dixon_w_eq_div x y theta phi h hz1
  have hpos : (0 : ℝ) < ‖((x : ℂ) * Complex.exp (Complex.I * theta)) - 1‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hz1)
  have hle : ‖(x : ℂ) * Complex.exp (Complex.I * theta)‖ ≤
      ‖((x : ℂ) * Complex.exp (Complex.I * theta)) - 1‖ := by
    rw [hw_eq, norm_div, div_le_one hpos] at hw
    exact hw
  have hsq : Complex.normSq ((x : ℂ) * Complex.exp (Complex.I * theta)) ≤
      Complex.normSq (((x : ℂ) * Complex.exp (Complex.I * theta)) - 1) := by
    have e1 := Complex.sq_norm ((x : ℂ) * Complex.exp (Complex.I * theta))
    have e2 := Complex.sq_norm (((x : ℂ) * Complex.exp (Complex.I * theta)) - 1)
    rw [← e1, ← e2]
    exact pow_le_pow_left₀ (norm_nonneg _) hle 2
  rw [Complex.normSq_apply, Complex.normSq_apply] at hsq
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
    sub_zero] at hsq
  nlinarith [hsq]

private lemma dixon_side_nonvanish (x theta : ℝ)
    (hre : (((x : ℂ) * Complex.exp (Complex.I * theta)) : ℂ).re ≤ 1 / 2) :
    1 - x * Real.cos theta ≠ 0 := by
  rw [dixon_re_z] at hre
  intro hcon
  linarith

private lemma dixon_Ax_expand (x theta : ℝ) : 1 - 2 * x * Real.cos theta + x ^ 2 =
    (1 - x * Real.cos theta) ^ 2 + (x * Real.sin theta) ^ 2 := by
  have h := Real.sin_sq_add_cos_sq theta
  linear_combination (-(x ^ 2)) * h

private lemma dixon_side_pos (x theta : ℝ)
    (hre : (((x : ℂ) * Complex.exp (Complex.I * theta)) : ℂ).re ≤ 1 / 2) :
    0 < 1 - 2 * x * Real.cos theta + x ^ 2 := by
  rw [dixon_re_z] at hre
  rw [dixon_Ax_expand]
  have hcos : (1 : ℝ) / 2 ≤ 1 - x * Real.cos theta := by linarith
  have h4 : (1 / 2 : ℝ) ^ 2 ≤ (1 - x * Real.cos theta) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hcos 2
  have hnn : (0 : ℝ) ≤ (x * Real.sin theta) ^ 2 := sq_nonneg _
  norm_num at h4 ⊢
  linarith

private lemma dixon_aux_summable_inv_sq_shift :
    Summable (fun j : ℕ => (1 : ℝ) / ((((j + 1 : ℕ) : ℝ) ^ 2))) := by
  have h2 : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2)) :=
    (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
  have h := (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2)) 1).mpr h2
  simpa [Nat.cast_add, Nat.cast_one] using h

private lemma dixon_norm_dilogCos_le (rho angle : ℝ) (h0 : 0 ≤ rho) (h1 : rho ≤ 1) (j : ℕ) :
    ‖chapter9DilogCosTerm rho angle j‖ ≤ 1 / ((((j + 1 : ℕ) : ℝ) ^ 2)) := by
  have hk : (0 : ℝ) < ((((j + 1 : ℕ) : ℝ) ^ 2)) := by positivity
  have hcos : |Real.cos ((((j + 1 : ℕ) : ℝ)) * angle)| ≤ 1 := Real.abs_cos_le_one _
  have hpow : rho ^ (j + 1) ≤ 1 := pow_le_one₀ h0 h1
  have hnn : (0 : ℝ) ≤ rho ^ (j + 1) := pow_nonneg h0 _
  unfold chapter9DilogCosTerm
  simp only
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hk]
  apply div_le_div_of_nonneg_right _ hk.le
  calc |rho ^ (j + 1) * Real.cos _|
      = rho ^ (j + 1) * |Real.cos _| := by rw [abs_mul, abs_of_nonneg hnn]
    _ ≤ 1 * 1 := mul_le_mul hpow hcos (abs_nonneg _) zero_le_one
    _ = 1 := mul_one 1

private lemma dixon_norm_dilogSin_le (rho angle : ℝ) (h0 : 0 ≤ rho) (h1 : rho ≤ 1) (j : ℕ) :
    ‖chapter9DilogSinTerm rho angle j‖ ≤ 1 / ((((j + 1 : ℕ) : ℝ) ^ 2)) := by
  have hk : (0 : ℝ) < ((((j + 1 : ℕ) : ℝ) ^ 2)) := by positivity
  have hsin : |Real.sin ((((j + 1 : ℕ) : ℝ)) * angle)| ≤ 1 := Real.abs_sin_le_one _
  have hpow : rho ^ (j + 1) ≤ 1 := pow_le_one₀ h0 h1
  have hnn : (0 : ℝ) ≤ rho ^ (j + 1) := pow_nonneg h0 _
  unfold chapter9DilogSinTerm
  simp only
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hk]
  apply div_le_div_of_nonneg_right _ hk.le
  calc |rho ^ (j + 1) * Real.sin _|
      = rho ^ (j + 1) * |Real.sin _| := by rw [abs_mul, abs_of_nonneg hnn]
    _ ≤ 1 * 1 := mul_le_mul hpow hsin (abs_nonneg _) zero_le_one
    _ = 1 := mul_one 1

private lemma dixon_summable_dilogCos (rho angle : ℝ) (h0 : 0 ≤ rho) (h1 : rho ≤ 1) :
    Summable (chapter9DilogCosTerm rho angle) :=
  Summable.of_norm_bounded dixon_aux_summable_inv_sq_shift
    (dixon_norm_dilogCos_le rho angle h0 h1)

private lemma dixon_summable_dilogSin (rho angle : ℝ) (h0 : 0 ≤ rho) (h1 : rho ≤ 1) :
    Summable (chapter9DilogSinTerm rho angle) :=
  Summable.of_norm_bounded dixon_aux_summable_inv_sq_shift
    (dixon_norm_dilogSin_le rho angle h0 h1)

/-- The complex dilogarithm summand `u^(j+1)/(j+1)^2`. -/
private def dixonL (u : ℂ) (j : ℕ) : ℂ :=
  u ^ (j + 1) / (((j + 1 : ℕ) : ℝ) : ℂ) ^ 2

private lemma dixon_zpow_eq (x theta : ℝ) (j : ℕ) :
    ((x : ℂ) * Complex.exp (Complex.I * (theta : ℂ))) ^ (j + 1) =
      ((x ^ (j + 1) : ℝ) : ℂ) *
        ((Real.cos (((j + 1 : ℕ) : ℝ) * theta) : ℂ) +
         (Real.sin (((j + 1 : ℕ) : ℝ) * theta) : ℂ) * Complex.I) := by
  rw [mul_pow, ← Complex.ofReal_pow]
  congr 1
  rw [← Complex.exp_nat_mul]
  have e := dixon_exp_polar' (((j + 1 : ℕ) : ℝ) * theta)
  convert e using 2
  push_cast; ring

private lemma dixon_Lterm_re (x theta : ℝ) (j : ℕ) :
    (dixonL ((x : ℂ) * Complex.exp (Complex.I * (theta : ℂ))) j).re
      = chapter9DilogCosTerm x theta j := by
  unfold dixonL chapter9DilogCosTerm
  simp only
  rw [← Complex.ofReal_pow, Complex.div_ofReal_re, dixon_zpow_eq]
  simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

private lemma dixon_Lterm_im (x theta : ℝ) (j : ℕ) :
    (dixonL ((x : ℂ) * Complex.exp (Complex.I * (theta : ℂ))) j).im
      = chapter9DilogSinTerm x theta j := by
  unfold dixonL chapter9DilogSinTerm
  simp only
  rw [← Complex.ofReal_pow, Complex.div_ofReal_im, dixon_zpow_eq]
  simp only [Complex.mul_im, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

private lemma dixon_norm_Lterm_le (u : ℂ) (hu : ‖u‖ ≤ 1) (j : ℕ) :
    ‖dixonL u j‖ ≤ (1 : ℝ) / ((((j + 1 : ℕ) : ℝ) ^ 2)) := by
  have hk : (0 : ℝ) < ((((j + 1 : ℕ) : ℝ) ^ 2)) := by positivity
  have hpow : ‖u‖ ^ (j + 1) ≤ 1 := pow_le_one₀ (norm_nonneg _) hu
  unfold dixonL
  rw [norm_div, Complex.norm_pow]
  have hden : ‖((((j + 1 : ℕ) : ℝ) : ℂ) ^ 2)‖ = ((((j + 1 : ℕ) : ℝ) ^ 2)) := by
    rw [Complex.norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  rw [hden]
  exact div_le_div_of_nonneg_right hpow hk.le

private lemma dixon_summable_Lterm (u : ℂ) (hu : ‖u‖ ≤ 1) : Summable (dixonL u) :=
  Summable.of_norm_bounded dixon_aux_summable_inv_sq_shift (dixon_norm_Lterm_le u hu)

private lemma dixon_one_sub_mem_slitPlane (x theta : ℝ)
    (hhalf : (1 : ℝ) / 2 ≤ 1 - x * Real.cos theta) :
    (1 : ℂ) - (x : ℂ) * Complex.exp (Complex.I * theta) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  rw [dixon_re_one_sub_z]
  linarith

private lemma dixon_log_one_sub_z_re (x theta : ℝ)
    (hAx : 0 < 1 - 2 * x * Real.cos theta + x ^ 2) :
    (Complex.log (1 - (x : ℂ) * Complex.exp (Complex.I * theta))).re
      = Real.log (1 - 2 * x * Real.cos theta + x ^ 2) / 2 := by
  rw [Complex.log_re]
  have hnorm : ‖(1 : ℂ) - (x : ℂ) * Complex.exp (Complex.I * theta)‖
      = Real.sqrt (1 - 2 * x * Real.cos theta + x ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg _), Complex.sq_norm, dixon_normSq_one_sub_z]
  rw [hnorm, Real.log_sqrt hAx.le]

private lemma dixon_log_one_sub_z_im (x theta : ℝ)
    (hhalf : (1 : ℝ) / 2 ≤ 1 - x * Real.cos theta) :
    (Complex.log (1 - (x : ℂ) * Complex.exp (Complex.I * theta))).im
      = -Real.arctan (x * Real.sin theta / (1 - x * Real.cos theta)) := by
  rw [Complex.log_im]
  have hre_pos : (0 : ℝ) < 1 - x * Real.cos theta := by linarith
  have harg_bound : |((1 : ℂ) - (x : ℂ) * Complex.exp (Complex.I * theta)).arg|
      < Real.pi / 2 := by
    rw [Complex.abs_arg_lt_pi_div_two_iff]
    left
    rw [dixon_re_one_sub_z]
    exact hre_pos
  have htan : Real.tan (((1 : ℂ) - (x : ℂ) * Complex.exp (Complex.I * theta)).arg)
      = -(x * Real.sin theta / (1 - x * Real.cos theta)) := by
    rw [Complex.tan_arg, dixon_im_one_sub_z, dixon_re_one_sub_z]
    ring
  have h1 := abs_lt.mp harg_bound
  have h2 : Real.arctan (Real.tan
      (((1 : ℂ) - (x : ℂ) * Complex.exp (Complex.I * theta)).arg))
      = ((1 : ℂ) - (x : ℂ) * Complex.exp (Complex.I * theta)).arg :=
    Real.arctan_tan h1.1 h1.2
  rw [htan, Real.arctan_neg] at h2
  exact h2.symm

private def dixonM (u : ℂ) : ℂ :=
  ∑' j : ℕ, u ^ j / ((((j + 1 : ℕ) : ℝ) : ℂ))

private def dixonLi (u : ℂ) : ℂ :=
  ∑' j : ℕ, dixonL u j

private lemma dixon_deriv_eq (y : ℂ) (j : ℕ) :
    ((((j + 1 : ℕ)) : ℂ) * y ^ j) / ((((j + 1 : ℕ) : ℝ) : ℂ)) ^ 2
      = y ^ j / ((((j + 1 : ℕ) : ℝ) : ℂ)) := by
  have hc : ((((j + 1 : ℕ) : ℝ) : ℂ)) ≠ 0 := by
    have hpos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt hpos)
  have ecast : ((((j + 1 : ℕ) : ℝ) : ℂ)) = (((j + 1 : ℕ)) : ℂ) :=
    Complex.ofReal_natCast _
  rw [ecast]
  have hn : ((((j + 1 : ℕ))) : ℂ) ≠ 0 := ecast ▸ hc
  field_simp

private lemma dixon_hasDerivAt_Li (u : ℂ) (hu : ‖u‖ < 1) :
    HasDerivAt dixonLi (dixonM u) u := by
  set r : ℝ := (1 + ‖u‖) / 2 with hr
  have hr0 : (0 : ℝ) < r := by rw [hr]; have hnn := norm_nonneg u; linarith [hu]
  have hr1 : ‖u‖ < r := by rw [hr]; linarith [hu]
  have hrr : r < 1 := by rw [hr]; linarith [hu]
  have hsum : Summable (fun j : ℕ => r ^ j) :=
    summable_geometric_of_lt_one (le_of_lt hr0) hrr
  have hopen : IsOpen (Metric.ball (0 : ℂ) r) := Metric.isOpen_ball
  have hpre : IsPreconnected (Metric.ball (0 : ℂ) r) :=
    (convex_ball (0 : ℂ) r).isPreconnected
  have hderiv : ∀ j : ℕ, ∀ y ∈ Metric.ball (0 : ℂ) r,
      HasDerivAt (fun v : ℂ => dixonL v j) (y ^ j / ((((j + 1 : ℕ) : ℝ) : ℂ))) y := by
    intro j y _
    have h1 : HasDerivAt (fun v : ℂ => v ^ (j + 1)) ((((j + 1 : ℕ)) : ℂ) * y ^ j) y := by
      have h := hasDerivAt_pow (j + 1) y
      rwa [Nat.add_sub_cancel] at h
    have h2 := h1.div_const (((((j + 1 : ℕ) : ℝ) : ℂ)) ^ 2)
    rw [dixon_deriv_eq] at h2
    exact h2
  have hbound : ∀ j : ℕ, ∀ y ∈ Metric.ball (0 : ℂ) r,
      ‖(y ^ j / ((((j + 1 : ℕ) : ℝ) : ℂ)))‖ ≤ r ^ j := by
    intro j y hy
    have hym : ‖y‖ < r := by
      have hmem := Metric.mem_ball.mp hy
      rwa [dist_zero_right] at hmem
    have h1 : ‖y ^ j / ((((j + 1 : ℕ) : ℝ) : ℂ))‖ = ‖y‖ ^ j / (((j + 1 : ℕ) : ℝ)) := by
      rw [norm_div, Complex.norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((j + 1 : ℕ) : ℝ))]
    rw [h1, div_le_iff₀ (by positivity : (0 : ℝ) < ((j + 1 : ℕ) : ℝ))]
    have hc1 : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by
      have hle : (1 : ℕ) ≤ j + 1 := Nat.le_add_left 1 j
      exact_mod_cast hle
    calc ‖y‖ ^ j ≤ r ^ j := pow_le_pow_left₀ (norm_nonneg _) hym.le j
      _ ≤ r ^ j * (((j + 1 : ℕ) : ℝ)) :=
        le_mul_of_one_le_right (pow_nonneg hr0.le _) hc1
  have hy0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_self]; exact hr0
  have hsum0 : Summable (fun j : ℕ => dixonL (0 : ℂ) j) := by
    have h0terms : ∀ j : ℕ, dixonL (0 : ℂ) j = 0 := by
      intro j
      unfold dixonL
      rw [zero_pow (by omega : j + 1 ≠ 0), zero_div]
    have hfun : (fun j : ℕ => dixonL (0 : ℂ) j) = fun _ => (0 : ℂ) :=
      funext (fun j => h0terms j)
    rw [hfun]
    exact summable_zero
  have hy : u ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right]; exact hr1
  have h := hasDerivAt_tsum_of_isPreconnected (u := fun j : ℕ => r ^ j)
    (t := Metric.ball (0 : ℂ) r) (g := fun j v => dixonL v j)
    (g' := fun j v => v ^ j / ((((j + 1 : ℕ) : ℝ) : ℂ))) (y₀ := 0) (y := u)
    hsum hopen hpre hderiv hbound hy0 hsum0 hy
  exact h

private lemma dixon_uM_eq (u : ℂ) (hu : ‖u‖ < 1) :
    u * dixonM u = -Complex.log (1 - u) := by
  have hlog := Complex.hasSum_taylorSeries_neg_log hu
  have hMsumm : Summable (fun j : ℕ => u ^ j / ((((j + 1 : ℕ) : ℝ) : ℂ))) := by
    apply Summable.of_norm_bounded (g := fun j : ℕ => ‖u‖ ^ j)
      (summable_geometric_of_lt_one (norm_nonneg _) hu)
    intro j
    rw [norm_div, Complex.norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((j + 1 : ℕ) : ℝ))]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < ((j + 1 : ℕ) : ℝ))]
    have hc1 : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by
      have hle : (1 : ℕ) ≤ j + 1 := Nat.le_add_left 1 j
      exact_mod_cast hle
    have hnn : (0 : ℝ) ≤ ‖u‖ ^ j := pow_nonneg (norm_nonneg _) _
    exact le_mul_of_one_le_right hnn hc1
  unfold dixonM
  rw [← tsum_mul_left]
  have hshift : (fun j : ℕ => u * (u ^ j / ((((j + 1 : ℕ) : ℝ) : ℂ))))
      = (fun n : ℕ => u ^ (n + 1) / ((((n + 1 : ℕ)) : ℂ))) := by
    funext j
    have ecast : ((((j + 1 : ℕ) : ℝ) : ℂ)) = (((j + 1 : ℕ)) : ℂ) :=
      Complex.ofReal_natCast _
    rw [ecast, ← mul_div_assoc, mul_comm u (u ^ j), ← pow_succ]
  rw [hshift]
  have hshift2 : HasSum (fun n : ℕ => u ^ (n + 1) / ((((n + 1 : ℕ)) : ℂ)))
      (-Complex.log (1 - u)) := by
    have h2 := (hasSum_nat_add_iff' (f := fun n : ℕ => u ^ n / ((((n : ℕ)) : ℂ)))
      (k := 1)).mpr hlog
    rw [Finset.sum_range_one] at h2
    simp only [pow_zero, Nat.cast_zero, div_zero, sub_zero] at h2
    exact h2
  exact hshift2.tsum_eq

private def dixonV (u : ℂ) : ℂ := u / (u - 1)

private def dixonF (u : ℂ) : ℂ :=
  dixonLi u + dixonLi (dixonV u)
    + (1 / 2 : ℂ) * (Complex.log (1 - u) * Complex.log (1 - u))

private def dixonU : Set ℂ := Metric.ball (0 : ℂ) 1 ∩ {u | u.re < 1 / 2}

private lemma dixon_hasDerivAt_V (u : ℂ) (hu10 : u - 1 ≠ 0) :
    HasDerivAt dixonV ((1 * (u - 1) - u * ((1 : ℂ) - 0)) / (u - 1) ^ 2) u := by
  have h2 : HasDerivAt (fun v : ℂ => v - 1) ((1 : ℂ) - 0) u :=
    (hasDerivAt_id (x := u)).sub (hasDerivAt_const (x := u) (c := (1 : ℂ)))
  exact (hasDerivAt_id u).div h2 hu10

private lemma dixon_norm_V_lt_one (u : ℂ) (hu2 : u.re < 1 / 2) :
    ‖dixonV u‖ < 1 := by
  have hsq : Complex.normSq u < Complex.normSq (u - 1) := by
    rw [Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
      sub_zero]
    nlinarith [hu2]
  have e1 := Complex.sq_norm u
  have e2 := Complex.sq_norm (u - 1)
  rw [← e1, ← e2] at hsq
  have hlt : ‖u‖ < ‖u - 1‖ := lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hsq
  have hpos : (0 : ℝ) < ‖u - 1‖ := lt_of_le_of_lt (norm_nonneg _) hlt
  have e : ‖dixonV u‖ = ‖u‖ / ‖u - 1‖ := by
    unfold dixonV; rw [norm_div]
  rw [e, div_lt_one hpos]
  exact hlt

private lemma dixon_F_hasDerivAt_aux (u : ℂ) (hu1 : ‖u‖ < 1) (hu2 : u.re < 1 / 2)
    (hu10 : u - 1 ≠ 0) :
    HasDerivAt dixonF
      (dixonM u + dixonM (dixonV u) * ((1 * (u - 1) - u * ((1 : ℂ) - 0)) / (u - 1) ^ 2)
        + (1 / 2 : ℂ) * ((((0 : ℂ) - 1) / (1 - u)) * Complex.log (1 - u)
          + Complex.log (1 - u) * (((0 : ℂ) - 1) / (1 - u)))) u := by
  have hLi := dixon_hasDerivAt_Li u hu1
  have hV := dixon_hasDerivAt_V u hu10
  have hmem : (1 : ℂ) - u ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    have hre : ((1 : ℂ) - u).re = 1 - u.re := by
      rw [Complex.sub_re, Complex.one_re]
    rw [hre]; linarith [hu2]
  have hvv : ‖dixonV u‖ < 1 := dixon_norm_V_lt_one u hu2
  have hLiv := dixon_hasDerivAt_Li (dixonV u) hvv
  have hcomp : HasDerivAt (dixonLi ∘ dixonV)
      (dixonM (dixonV u) * ((1 * (u - 1) - u * ((1 : ℂ) - 0)) / (u - 1) ^ 2)) u :=
    HasDerivAt.comp u hLiv hV
  have h1 : HasDerivAt (fun v : ℂ => (1 : ℂ) - v) ((0 : ℂ) - 1) u :=
    (hasDerivAt_const (x := u) (c := (1 : ℂ))).sub (hasDerivAt_id (x := u))
  have hlog1 : HasDerivAt (fun v : ℂ => Complex.log (1 - v))
      (((0 : ℂ) - 1) / (1 - u)) u :=
    h1.clog hmem
  have hmul := hlog1.mul hlog1
  have hlogpart : HasDerivAt
      (fun v : ℂ => (1 / 2 : ℂ) * (Complex.log (1 - v) * Complex.log (1 - v)))
      ((1 / 2 : ℂ) * ((((0 : ℂ) - 1) / (1 - u)) * Complex.log (1 - u)
        + Complex.log (1 - u) * (((0 : ℂ) - 1) / (1 - u)))) u :=
    HasDerivAt.const_mul (1 / 2 : ℂ) hmul
  exact (hLi.add hcomp).add hlogpart

private lemma dixon_M_zero : dixonM 0 = 1 := by
  have hvanish : ∀ b' : ℕ, b' ≠ 0 →
      (0 : ℂ) ^ b' / ((((b' + 1 : ℕ) : ℝ) : ℂ)) = 0 := by
    intro b' hb
    rw [zero_pow hb, zero_div]
  have h1 : (∑' j : ℕ, (0 : ℂ) ^ j / ((((j + 1 : ℕ) : ℝ) : ℂ)))
      = (0 : ℂ) ^ 0 / ((((0 + 1 : ℕ) : ℝ) : ℂ)) :=
    tsum_eq_single 0 (fun b' hb => hvanish b' hb)
  unfold dixonM
  rw [h1]
  simp

private lemma dixon_V_zero : dixonV 0 = 0 := by
  unfold dixonV
  simp

private lemma dixon_Fderiv_zero (u : ℂ) (hu1 : ‖u‖ < 1) (hu2 : u.re < 1 / 2)
    (hu10 : u - 1 ≠ 0) :
    dixonM u + dixonM (dixonV u) * ((1 * (u - 1) - u * ((1 : ℂ) - 0)) / (u - 1) ^ 2)
      + (1 / 2 : ℂ) * ((((0 : ℂ) - 1) / (1 - u)) * Complex.log (1 - u)
        + Complex.log (1 - u) * (((0 : ℂ) - 1) / (1 - u))) = 0 := by
  by_cases hune : u = 0
  · subst hune
    rw [dixon_V_zero, dixon_M_zero]
    simp only [sub_zero, Complex.log_one, mul_zero, zero_mul, add_zero]
    norm_num
  · have h1u : (1 : ℂ) - u ≠ 0 := by
      have e : (1 : ℂ) - u = -(u - 1) := by ring
      rw [e]; exact neg_ne_zero.mpr hu10
    have hMu : dixonM u = -Complex.log (1 - u) / u := by
      have h := dixon_uM_eq u hu1
      have h' : dixonM u * u = -Complex.log (1 - u) := by
        rw [mul_comm]; exact h
      exact (eq_div_iff hune).mpr h'
    have hv0 : dixonV u ≠ 0 := by
      unfold dixonV
      exact div_ne_zero hune hu10
    have hvv : ‖dixonV u‖ < 1 := dixon_norm_V_lt_one u hu2
    have hMv : dixonM (dixonV u) = -Complex.log (1 - dixonV u) / dixonV u := by
      have h := dixon_uM_eq (dixonV u) hvv
      have h' : dixonM (dixonV u) * dixonV u = -Complex.log (1 - dixonV u) := by
        rw [mul_comm]; exact h
      exact (eq_div_iff hv0).mpr h'
    have h1v : 1 - dixonV u = 1 / (1 - u) := by
      unfold dixonV
      field_simp
      ring
    have harg : ((1 : ℂ) - u).arg ≠ Real.pi := by
      have hb : |((1 : ℂ) - u).arg| < Real.pi / 2 := by
        rw [Complex.abs_arg_lt_pi_div_two_iff]
        left
        have e : ((1 : ℂ) - u).re = 1 - u.re := by
          rw [Complex.sub_re, Complex.one_re]
        rw [e]; linarith [hu2]
      intro hcon
      rw [hcon, abs_of_pos Real.pi_pos] at hb
      linarith [Real.pi_pos]
    have hlog1v : Complex.log (1 - dixonV u) = -Complex.log (1 - u) := by
      rw [h1v, one_div]
      exact Complex.log_inv _ harg
    rw [hMu, hMv, hlog1v]
    unfold dixonV
    field_simp
    ring

private lemma dixon_F_hasDerivAt (u : ℂ) (hu1 : ‖u‖ < 1) (hu2 : u.re < 1 / 2)
    (hu10 : u - 1 ≠ 0) : HasDerivAt dixonF 0 u := by
  have hF := dixon_F_hasDerivAt_aux u hu1 hu2 hu10
  have hval := dixon_Fderiv_zero u hu1 hu2 hu10
  rwa [hval] at hF

private lemma dixonU_mem {u : ℂ} : u ∈ dixonU ↔ ‖u‖ < 1 ∧ u.re < 1 / 2 := by
  unfold dixonU
  rw [Set.mem_inter_iff, Metric.mem_ball, dist_zero_right]
  simp only [Set.mem_ofPred_eq]

private lemma dixonU_open : IsOpen dixonU :=
  Metric.isOpen_ball.inter (isOpen_lt Complex.continuous_re continuous_const)

private lemma dixonU_pre : IsPreconnected dixonU :=
  ((convex_ball (0 : ℂ) 1).inter (convex_halfSpace_re_lt (1 / 2))).isPreconnected

private lemma dixonU_zero : (0 : ℂ) ∈ dixonU := by
  unfold dixonU
  rw [Set.mem_inter_iff, Metric.mem_ball, dist_self]
  refine ⟨by norm_num, ?_⟩
  change (0 : ℂ).re < 1 / 2
  rw [Complex.zero_re]; norm_num

private lemma dixon_mem_imp_sub_ne {u : ℂ} (hu : u ∈ dixonU) : u - 1 ≠ 0 := by
  rw [dixonU_mem] at hu
  obtain ⟨_, hx2⟩ := hu
  intro hcon
  rw [sub_eq_zero.mp hcon, Complex.one_re] at hx2
  norm_num at hx2

private lemma dixon_F_const (u : ℂ) (hu : u ∈ dixonU) : dixonF u = dixonF 0 := by
  have hdiff : DifferentiableOn ℂ dixonF dixonU := by
    intro x hx
    rw [dixonU_mem] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hxU : x ∈ dixonU := dixonU_mem.mpr ⟨hx1, hx2⟩
    have hFx := dixon_F_hasDerivAt x hx1 hx2 (dixon_mem_imp_sub_ne hxU)
    exact hFx.differentiableAt.differentiableWithinAt
  have hderiv : Set.EqOn (deriv dixonF) 0 dixonU := by
    intro x hx
    rw [dixonU_mem] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hxU : x ∈ dixonU := dixonU_mem.mpr ⟨hx1, hx2⟩
    exact (dixon_F_hasDerivAt x hx1 hx2 (dixon_mem_imp_sub_ne hxU)).deriv
  exact IsOpen.is_const_of_deriv_eq_zero dixonU_open dixonU_pre hdiff hderiv hu dixonU_zero

private lemma dixon_F_zero : dixonF 0 = 0 := by
  have hLi0 : dixonLi 0 = 0 := by
    have h0 : ∀ j : ℕ, dixonL (0 : ℂ) j = 0 := by
      intro j
      unfold dixonL
      rw [zero_pow (by omega : j + 1 ≠ 0), zero_div]
    calc dixonLi 0 = ∑' _ : ℕ, (0 : ℂ) := tsum_congr (fun j => h0 j)
      _ = 0 := tsum_zero
  have hv0 : dixonV 0 = 0 := dixon_V_zero
  unfold dixonF
  rw [hLi0, hv0, hLi0]
  simp

private lemma dixon_tsum_re (x theta : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    (dixonLi ((x : ℂ) * Complex.exp (Complex.I * theta))).re
      = ∑' j : ℕ, chapter9DilogCosTerm x theta j := by
  have hnorm : ‖((x : ℂ) * Complex.exp (Complex.I * theta))‖ ≤ 1 := by
    rw [dixon_norm_z x theta h0]; exact h1
  have hs := dixon_summable_Lterm _ hnorm
  unfold dixonLi
  rw [Complex.re_tsum hs]
  exact tsum_congr (fun j => dixon_Lterm_re x theta j)

private lemma dixon_tsum_im (x theta : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    (dixonLi ((x : ℂ) * Complex.exp (Complex.I * theta))).im
      = ∑' j : ℕ, chapter9DilogSinTerm x theta j := by
  have hnorm : ‖((x : ℂ) * Complex.exp (Complex.I * theta))‖ ≤ 1 := by
    rw [dixon_norm_z x theta h0]; exact h1
  have hs := dixon_summable_Lterm _ hnorm
  unfold dixonLi
  rw [Complex.im_tsum hs]
  exact tsum_congr (fun j => dixon_Lterm_im x theta j)

private lemma dixon_Li_continuousOn :
    ContinuousOn dixonLi (Metric.closedBall (0 : ℂ) 1) := by
  have hcont : ∀ j : ℕ,
      ContinuousOn (fun v : ℂ => dixonL v j) (Metric.closedBall (0 : ℂ) 1) := by
    intro j
    have hne : ∀ v : ℂ, v ∈ Metric.closedBall (0 : ℂ) 1 →
        ((((j + 1 : ℕ) : ℝ) : ℂ) ^ 2) ≠ 0 := by
      intro v _
      have hpos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
      have hc : ((((j + 1 : ℕ) : ℝ) : ℂ)) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (ne_of_gt hpos)
      exact pow_ne_zero 2 hc
    exact ((continuous_id.pow _).continuousOn).div continuousOn_const hne
  have hbound : ∀ j : ℕ, ∀ v : ℂ, v ∈ Metric.closedBall (0 : ℂ) 1 →
      ‖dixonL v j‖ ≤ 1 / ((((j + 1 : ℕ) : ℝ) ^ 2)) := by
    intro j v hv
    have hmem : ‖v‖ ≤ 1 := by
      have hdist := Metric.mem_closedBall.mp hv
      rwa [dist_zero_right] at hdist
    exact dixon_norm_Lterm_le v hmem j
  have h := continuousOn_tsum (f := fun j (v : ℂ) => dixonL v j)
    (u := fun j : ℕ => (1 : ℝ) / ((((j + 1 : ℕ) : ℝ) ^ 2)))
    (s := Metric.closedBall (0 : ℂ) 1)
    hcont dixon_aux_summable_inv_sq_shift hbound
  exact h

private lemma dixon_ray_mem_U (z : ℂ) (hz1 : ‖z‖ ≤ 1) (hz2 : z.re ≤ 1 / 2)
    (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) : ((((t : ℝ)) : ℂ) * z) ∈ dixonU := by
  obtain ⟨ht0, ht1⟩ := Set.mem_Ico.mp ht
  rw [dixonU_mem]
  refine ⟨?_, ?_⟩
  · have e : ‖((((t : ℝ)) : ℂ) * z)‖ = t * ‖z‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
    rw [e]
    calc t * ‖z‖ ≤ t * 1 := mul_le_mul_of_nonneg_left hz1 ht0
      _ = t := mul_one t
      _ < 1 := ht1
  · have ere : (((((t : ℝ)) : ℂ) * z)).re = t * z.re := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [ere]
    by_cases hzpos : 0 < z.re
    · calc t * z.re < 1 * z.re := mul_lt_mul_of_pos_right ht1 hzpos
        _ = z.re := one_mul _
        _ ≤ 1 / 2 := hz2
    · have hzle : z.re ≤ 0 := le_of_not_gt hzpos
      calc t * z.re ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0 hzle
        _ < 1 / 2 := by norm_num

private lemma dixon_F_boundary (z w : ℂ) (hz1 : ‖z‖ ≤ 1) (hz2 : z.re ≤ 1 / 2)
    (hz3 : z ≠ 1) (hw : w = z / (z - 1)) (hw1 : ‖w‖ ≤ 1) :
    dixonLi z + dixonLi w
      + (1 / 2 : ℂ) * (Complex.log (1 - z) * Complex.log (1 - z)) = 0 := by
  have hzne : z - 1 ≠ 0 := sub_ne_zero.mpr hz3
  have hzmem : z ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hz1
  have hwmem : w ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hw1
  have hVw : dixonV z = w := hw.symm
  have hcont_g : Continuous (fun t : ℝ => ((((t : ℝ)) : ℂ) * z)) :=
    Complex.continuous_ofReal.mul continuous_const
  have hg : Tendsto (fun t : ℝ => ((((t : ℝ)) : ℂ) * z)) (𝓝[<] (1 : ℝ)) (𝓝 z) := by
    have h := (hcont_g.tendsto (1 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)) (a := (1 : ℝ)))
    simpa using h
  have hIco_nbhd : ∀ᶠ t in 𝓝[<] (1 : ℝ), t ∈ Set.Ico (0 : ℝ) 1 :=
    Filter.eventually_of_mem (Ico_mem_nhdsLT (by norm_num : (0 : ℝ) < 1))
      (fun t ht => ht)
  have hg_in : ∀ᶠ t in 𝓝[<] (1 : ℝ),
      ((((t : ℝ)) : ℂ) * z) ∈ Metric.closedBall (0 : ℂ) 1 := by
    filter_upwards [hIco_nbhd] with t ht
    have hUmem := dixon_ray_mem_U z hz1 hz2 t ht
    obtain ⟨hnorm, _⟩ := dixonU_mem.mp hUmem
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hnorm.le
  have hg_sub : Tendsto (fun t : ℝ => ((((t : ℝ)) : ℂ) * z)) (𝓝[<] (1 : ℝ))
      (𝓝[Metric.closedBall (0 : ℂ) 1] z) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hg hg_in
  have hLiz : Tendsto (fun t : ℝ => dixonLi ((((t : ℝ)) : ℂ) * z)) (𝓝[<] (1 : ℝ))
      (𝓝 (dixonLi z)) :=
    Filter.Tendsto.congr (fun t => rfl)
      (Filter.Tendsto.comp
        (dixon_Li_continuousOn.continuousWithinAt hzmem) hg_sub)
  have hVcont : ContinuousAt dixonV z := (dixon_hasDerivAt_V z hzne).continuousAt
  have hVg : Tendsto (fun t : ℝ => dixonV ((((t : ℝ)) : ℂ) * z)) (𝓝[<] (1 : ℝ))
      (𝓝 (dixonV z)) :=
    Filter.Tendsto.congr (fun t => rfl) (Filter.Tendsto.comp hVcont hg)
  rw [hVw] at hVg
  have hVg_in : ∀ᶠ t in 𝓝[<] (1 : ℝ),
      dixonV ((((t : ℝ)) : ℂ) * z) ∈ Metric.closedBall (0 : ℂ) 1 := by
    filter_upwards [hIco_nbhd] with t ht
    have hUmem := dixon_ray_mem_U z hz1 hz2 t ht
    have hlt := dixon_norm_V_lt_one _ (dixonU_mem.mp hUmem).2
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hlt.le
  have hVg_sub : Tendsto (fun t : ℝ => dixonV ((((t : ℝ)) : ℂ) * z)) (𝓝[<] (1 : ℝ))
      (𝓝[Metric.closedBall (0 : ℂ) 1] w) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hVg hVg_in
  have hLiw : Tendsto (fun t : ℝ => dixonLi (dixonV ((((t : ℝ)) : ℂ) * z)))
      (𝓝[<] (1 : ℝ)) (𝓝 (dixonLi (dixonV z))) := by
    have h := Filter.Tendsto.congr (fun t => rfl)
      (Filter.Tendsto.comp
        (dixon_Li_continuousOn.continuousWithinAt hwmem) hVg_sub)
    rwa [← hVw] at h
  have h1zslit : (1 : ℂ) - z ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    have e : ((1 : ℂ) - z).re = 1 - z.re := by
      rw [Complex.sub_re, Complex.one_re]
    rw [e]; linarith [hz2]
  have hlogc : ContinuousAt Complex.log (1 - z) := continuousAt_clog h1zslit
  have h1g : Tendsto (fun t : ℝ => (1 : ℂ) - ((((t : ℝ)) : ℂ) * z)) (𝓝[<] (1 : ℝ))
      (𝓝 (1 - z)) :=
    tendsto_const_nhds.sub hg
  have hlogtend : Tendsto
      (fun t : ℝ => Complex.log (1 - ((((t : ℝ)) : ℂ) * z))) (𝓝[<] (1 : ℝ))
      (𝓝 (Complex.log (1 - z))) :=
    Filter.Tendsto.congr (fun t => rfl) (Filter.Tendsto.comp hlogc h1g)
  have hlogpart : Tendsto
      (fun t : ℝ => (1 / 2 : ℂ)
        * (Complex.log (1 - ((((t : ℝ)) : ℂ) * z))
          * Complex.log (1 - ((((t : ℝ)) : ℂ) * z))))
      (𝓝[<] (1 : ℝ))
      (𝓝 ((1 / 2 : ℂ) * (Complex.log (1 - z) * Complex.log (1 - z)))) :=
    tendsto_const_nhds.mul (hlogtend.mul hlogtend)
  have hlim : Tendsto (fun t : ℝ => dixonF ((((t : ℝ)) : ℂ) * z)) (𝓝[<] (1 : ℝ))
      (𝓝 (dixonF z)) := by
    have h := (hLiz.add hLiw).add hlogpart
    simpa only [dixonF] using h
  have hF0 : ∀ t : ℝ, t ∈ Set.Ico (0 : ℝ) 1 → dixonF ((((t : ℝ)) : ℂ) * z) = 0 := by
    intro t ht
    have hUmem := dixon_ray_mem_U z hz1 hz2 t ht
    rw [dixon_F_const _ hUmem, dixon_F_zero]
  have heq : (fun _ : ℝ => (0 : ℂ)) =ᶠ[𝓝[<] (1 : ℝ)]
      (fun t => dixonF ((((t : ℝ)) : ℂ) * z)) :=
    Filter.eventually_of_mem (Ico_mem_nhdsLT (by norm_num : (0 : ℝ) < 1))
      (fun t ht => (hF0 t ht).symm)
  have hconst : Tendsto (fun t : ℝ => dixonF ((((t : ℝ)) : ℂ) * z)) (𝓝[<] (1 : ℝ))
      (𝓝 0) :=
    Tendsto.congr' heq tendsto_const_nhds
  have hFz : dixonF z = 0 := tendsto_nhds_unique hlim hconst
  unfold dixonF at hFz
  rwa [hVw] at hFz

private lemma dixon_claim (z w : ℂ) (hz2 : z.re ≤ 1 / 2) (hz3 : z ≠ 1)
    (hw : w = z / (z - 1))
    (hFz : dixonLi z + dixonLi w
      + (1 / 2 : ℂ) * (Complex.log (1 - z) * Complex.log (1 - z)) = 0) :
    dixonLi z + dixonLi w
      = (1 / 2 : ℂ) * Complex.log (1 - z) * Complex.log (1 - w) := by
  have hu10 : z - 1 ≠ 0 := sub_ne_zero.mpr hz3
  have h1u : (1 : ℂ) - z ≠ 0 := by
    have e : (1 : ℂ) - z = -(z - 1) := by ring
    rw [e]; exact neg_ne_zero.mpr hu10
  have harg : ((1 : ℂ) - z).arg ≠ Real.pi := by
    have hb : |((1 : ℂ) - z).arg| < Real.pi / 2 := by
      rw [Complex.abs_arg_lt_pi_div_two_iff]
      left
      have e : ((1 : ℂ) - z).re = 1 - z.re := by
        rw [Complex.sub_re, Complex.one_re]
      rw [e]; linarith [hz2]
    intro hcon
    rw [hcon, abs_of_pos Real.pi_pos] at hb
    linarith [Real.pi_pos]
  have h1w : (1 : ℂ) - w = (1 - z)⁻¹ := by
    rw [hw]
    field_simp
    ring
  have hlogw : Complex.log (1 - w) = -Complex.log (1 - z) := by
    rw [h1w]
    exact Complex.log_inv _ harg
  rw [hlogw]
  linear_combination hFz

/-- **Entry 25 of Chapter 9 of Ramanujan's notebooks.** Let $x, y \in [0, 1]$ and let $\theta$
and $\varphi$ be real numbers with $x e^{i\theta} + y e^{i\varphi} = xy \, e^{i(\theta + \varphi)}$.
Then $1 - x \cos\theta \ne 0$ and $1 - y \cos\varphi \ne 0$. Put
$A_x = 1 - 2x \cos\theta + x^2$, $A_y = 1 - 2y \cos\varphi + y^2$,
$u_x = \arctan \frac{x \sin\theta}{1 - x \cos\theta}$ and
$u_y = \arctan \frac{y \sin\varphi}{1 - y \cos\varphi}$.
Then $A_x > 0$, $A_y > 0$, the four series
$\sum_{k \ge 1} \frac{x^k \cos k\theta}{k^2}$, $\sum_{k \ge 1} \frac{y^k \cos k\varphi}{k^2}$,
$\sum_{k \ge 1} \frac{x^k \sin k\theta}{k^2}$ and $\sum_{k \ge 1} \frac{y^k \sin k\varphi}{k^2}$
converge absolutely, and

$$
\sum_{k \ge 1} \frac{x^k \cos k\theta}{k^2} + \sum_{k \ge 1} \frac{y^k \cos k\varphi}{k^2} =
\frac{\log A_x \log A_y}{8} - \frac{u_x u_y}{2},
$$

$$
\sum_{k \ge 1} \frac{x^k \sin k\theta}{k^2} + \sum_{k \ge 1} \frac{y^k \sin k\varphi}{k^2} =
-\frac{u_y \log A_x}{4} - \frac{u_x \log A_y}{4}.
$$

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 9.
-/
theorem ramanujan_part1_ch9_entry25_dixon (x y theta phi : ℝ)
    (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1)
    (hxy : (x : ℂ) * Complex.exp (Complex.I * theta) +
      (y : ℂ) * Complex.exp (Complex.I * phi) =
        (x * y : ℝ) * Complex.exp (Complex.I * (theta + phi))) :
    let Ax := 1 - 2 * x * Real.cos theta + x ^ 2
    let Ay := 1 - 2 * y * Real.cos phi + y ^ 2
    let ux := Real.arctan (x * Real.sin theta / (1 - x * Real.cos theta))
    let uy := Real.arctan (y * Real.sin phi / (1 - y * Real.cos phi))
    1 - x * Real.cos theta ≠ 0 ∧
      1 - y * Real.cos phi ≠ 0 ∧
      0 < Ax ∧ 0 < Ay ∧
      Summable (chapter9DilogCosTerm x theta) ∧
      Summable (chapter9DilogCosTerm y phi) ∧
      Summable (chapter9DilogSinTerm x theta) ∧
      Summable (chapter9DilogSinTerm y phi) ∧
      (∑' j : ℕ, chapter9DilogCosTerm x theta j) +
          ∑' j : ℕ, chapter9DilogCosTerm y phi j =
        Real.log Ax * Real.log Ay / 8 - ux * uy / 2 ∧
      (∑' j : ℕ, chapter9DilogSinTerm x theta j) +
          ∑' j : ℕ, chapter9DilogSinTerm y phi j =
        -Real.log Ax * uy / 4 - Real.log Ay * ux / 4 := by
  have hxy' := dixon_zw_mul x y theta phi hxy
  have hnormz : ‖((x : ℂ) * Complex.exp (Complex.I * theta))‖ ≤ 1 := by
    rw [dixon_norm_z x theta hx.1]; exact hx.2
  have hnormw : ‖((y : ℂ) * Complex.exp (Complex.I * phi))‖ ≤ 1 := by
    rw [dixon_norm_z y phi hy.1]; exact hy.2
  have hrez : ((((x : ℂ) * Complex.exp (Complex.I * theta)))).re ≤ 1 / 2 :=
    dixon_re_le_half x y theta phi hxy' hnormw
  have hrew : ((((y : ℂ) * Complex.exp (Complex.I * phi)))).re ≤ 1 / 2 :=
    dixon_re_le_half y x phi theta (by linear_combination hxy') hnormz
  have hz_ne : ((x : ℂ) * Complex.exp (Complex.I * theta)) ≠ 1 :=
    dixon_z_ne_one x y theta phi hxy'
  have hw_eq : ((y : ℂ) * Complex.exp (Complex.I * phi))
      = ((x : ℂ) * Complex.exp (Complex.I * theta))
        / (((x : ℂ) * Complex.exp (Complex.I * theta)) - 1) :=
    dixon_w_eq_div x y theta phi hxy' hz_ne
  have hFz := dixon_F_boundary _ _ hnormz hrez hz_ne hw_eq hnormw
  have hclaim := dixon_claim _ _ hrez hz_ne hw_eq hFz
  have hAx_pos := dixon_side_pos x theta hrez
  have hAy_pos := dixon_side_pos y phi hrew
  have hnvx := dixon_side_nonvanish x theta hrez
  have hnvy := dixon_side_nonvanish y phi hrew
  have hsCx := dixon_summable_dilogCos x theta hx.1 hx.2
  have hsCy := dixon_summable_dilogCos y phi hy.1 hy.2
  have hsSx := dixon_summable_dilogSin x theta hx.1 hx.2
  have hsSy := dixon_summable_dilogSin y phi hy.1 hy.2
  have hcos_re_x := dixon_tsum_re x theta hx.1 hx.2
  have hcos_re_y := dixon_tsum_re y phi hy.1 hy.2
  have hsin_im_x := dixon_tsum_im x theta hx.1 hx.2
  have hsin_im_y := dixon_tsum_im y phi hy.1 hy.2
  have hhalf_x : (1 : ℝ) / 2 ≤ 1 - x * Real.cos theta := by
    have h := hrez; rw [dixon_re_z] at h; linarith
  have hhalf_y : (1 : ℝ) / 2 ≤ 1 - y * Real.cos phi := by
    have h := hrew; rw [dixon_re_z] at h; linarith
  have hPre := dixon_log_one_sub_z_re x theta hAx_pos
  have hPim := dixon_log_one_sub_z_im x theta hhalf_x
  have hQre := dixon_log_one_sub_z_re y phi hAy_pos
  have hQim := dixon_log_one_sub_z_im y phi hhalf_y
  have e12 : ((1 / 2 : ℂ)) = ((((1 / 2 : ℝ)) : ℂ)) := by simp
  have hre0 := congrArg Complex.re hclaim
  have him0 := congrArg Complex.im hclaim
  rw [Complex.add_re, hcos_re_x, hcos_re_y, e12, Complex.mul_re, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hPre, hPim, hQre,
    hQim] at hre0
  rw [Complex.add_im, hsin_im_x, hsin_im_y, e12, Complex.mul_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hPre, hPim, hQre,
    hQim] at him0
  intro Ax Ay ux uy
  refine ⟨hnvx, hnvy, hAx_pos, hAy_pos, hsCx, hsCy, hsSx, hsSy, ?_, ?_⟩
  · change (∑' j : ℕ, chapter9DilogCosTerm x theta j)
          + (∑' j : ℕ, chapter9DilogCosTerm y phi j)
        = Real.log (1 - 2 * x * Real.cos theta + x ^ 2)
          * Real.log (1 - 2 * y * Real.cos phi + y ^ 2) / 8
          - Real.arctan (x * Real.sin theta / (1 - x * Real.cos theta))
            * Real.arctan (y * Real.sin phi / (1 - y * Real.cos phi)) / 2
    linear_combination hre0
  · change (∑' j : ℕ, chapter9DilogSinTerm x theta j)
          + (∑' j : ℕ, chapter9DilogSinTerm y phi j)
        = -Real.log (1 - 2 * x * Real.cos theta + x ^ 2)
          * Real.arctan (y * Real.sin phi / (1 - y * Real.cos phi)) / 4
          - Real.log (1 - 2 * y * Real.cos phi + y ^ 2)
            * Real.arctan (x * Real.sin theta / (1 - x * Real.cos theta)) / 4
    linear_combination him0

end
end Entry25Dixon
end MathlibExt.Analysis.Ramanujan.Part1Ch9
end
