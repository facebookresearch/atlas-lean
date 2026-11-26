/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PDE.HeatKernel
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# One-dimensional heat-kernel derivatives and domination

Spatial derivatives of the existing Gaussian kernel, and an integrable bound
uniform on compact positive-time and bounded spatial parameter sets. These are
the differentiation-under-the-integral estimates used in the heat initial-value
construction. The dominating Gaussian is allowed a larger variance.

Reference: M. Schmidt, *Partial Differential Equations*, HWS 2025, Chapter 4,
Theorem 4.3 and its proof,
https://www.wim.uni-mannheim.de/media/Lehrstuehle/wim/schmidt/HWS2025/chapter_4.pdf.
-/

@[expose] public section

open MeasureTheory Set Real
open scoped ContDiff

namespace MathlibExt.Analysis.PDE.HeatKernel

/-- The first spatial derivative of the one-dimensional heat kernel. -/
noncomputable def heatKernelDx (t x : ℝ) : ℝ := -x / (2 * t) * heatKernel ℝ t x

/-- The second spatial derivative `(x² / (4 t²) - 1 / (2 t)) Φ(t, x)` in dimension one; for
`0 < t` it is also the time derivative (`hasDerivAt_heatKernel_time_dxx`). -/
noncomputable def heatKernelDxx (t x : ℝ) : ℝ :=
  (x ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * heatKernel ℝ t x

/-- Real-coordinate formula for the kernel. -/
theorem heatKernel_real (t x : ℝ) :
    heatKernel ℝ t x = (4 * π * t) ^ (-(1 : ℝ) / 2) * exp (-x ^ 2 / (4 * t)) := by
  simp [heatKernel, Real.norm_eq_abs, sq_abs]

/-- Spatial smoothness of the kernel for each fixed time. -/
theorem heatKernel_contDiff (t : ℝ) : ContDiff ℝ ∞ (heatKernel ℝ t) := by
  unfold heatKernel
  exact contDiff_const.mul (((contDiff_norm_sq ℝ).neg.div_const _).exp)

/-- Actual first spatial derivative. -/
theorem hasDerivAt_heatKernel_space (t x : ℝ) :
    HasDerivAt (heatKernel ℝ t) (heatKernelDx t x) x := by
  have hq : HasDerivAt (fun y : ℝ => -y ^ 2 / (4 * t)) (-x / (2 * t)) x := by
    convert (((hasDerivAt_id' x).pow 2).neg.div_const (4 * t)) using 1
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
    ring
  have hd := hq.exp.const_mul ((4 * π * t) ^ (-(1 : ℝ) / 2))
  convert hd using 1
  · ext y
    exact heatKernel_real t y
  · rw [heatKernelDx, heatKernel_real]
    ring

/-- Actual second spatial derivative for positive time. -/
theorem hasDerivAt_heatKernelDx_space {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (heatKernelDx t) (heatKernelDxx t x) x := by
  have hd := ((hasDerivAt_id' x).neg.div_const (2 * t)).mul
    (hasDerivAt_heatKernel_space t x)
  convert hd using 1
  · rfl
  · unfold heatKernelDxx heatKernelDx
    simp only [Pi.neg_apply]
    field_simp
    ring

/-- In one dimension, the time derivative is the second spatial derivative. -/
theorem hasDerivAt_heatKernel_time_dxx {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s => heatKernel ℝ s x) (heatKernelDxx t x) t := by
  simpa [heatKernelDxx, Real.norm_eq_abs, sq_abs, mul_comm] using
    hasDerivAt_heatKernel_time ht x

/-- Continuity in the spatial variable of the first derivative kernel. -/
theorem heatKernelDx_continuous (t : ℝ) : Continuous (heatKernelDx t) := by
  unfold heatKernelDx
  exact (continuous_id.neg.div_const _).mul (heatKernel_contDiff t).continuous

/-- Continuity in the spatial variable of the second derivative kernel. -/
theorem heatKernelDxx_continuous (t : ℝ) : Continuous (heatKernelDxx t) := by
  unfold heatKernelDxx
  exact (((continuous_id.pow 2).div_const _).sub continuous_const).mul
    (heatKernel_contDiff t).continuous

private theorem gaussian_shift_bound {a b R t x : ℝ} (ha : 0 < a)
    (hat : a ≤ t) (htb : t ≤ b) (hx : |x| ≤ R) (y : ℝ) :
    exp (-(x - y) ^ 2 / (4 * t)) ≤ exp (R ^ 2 / (4 * a)) * exp (-(1 / (8 * b)) * y ^ 2) := by
  have ht : 0 < t := ha.trans_le hat
  have hb : 0 < b := ht.trans_le htb
  have hxx : x ^ 2 ≤ R ^ 2 := by
    nlinarith [sq_abs x, mul_nonneg (sub_nonneg.mpr hx)
      (add_nonneg (le_trans (abs_nonneg x) hx) (abs_nonneg x))]
  have h : y ^ 2 / (8 * b) ≤ (x - y) ^ 2 / (4 * t) + R ^ 2 / (4 * a) := by
    calc
      y ^ 2 / (8 * b) ≤ ((x - y) ^ 2 + x ^ 2) / (4 * b) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        nlinarith [sq_nonneg (y - 2 * x)]
      _ = (x - y) ^ 2 / (4 * b) + x ^ 2 / (4 * b) := by ring
      _ ≤ (x - y) ^ 2 / (4 * t) + R ^ 2 / (4 * a) := by
        apply add_le_add
        · exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
        · exact (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
            (by linarith : 4 * a ≤ 4 * b)).trans
              (div_le_div_of_nonneg_right hxx (by positivity))
  rw [← exp_add]
  apply exp_le_exp.mpr
  calc
    _ = -((x - y) ^ 2 / (4 * t)) := by ring
    _ ≤ R ^ 2 / (4 * a) - y ^ 2 / (8 * b) := by linarith
    _ = _ := by ring

private theorem kernel_bound {a b R t x : ℝ} (ha : 0 < a)
    (hat : a ≤ t) (htb : t ≤ b) (hx : |x| ≤ R) (y : ℝ) :
    heatKernel ℝ t (x - y) ≤
      ((4 * π * a) ^ (-(1 : ℝ) / 2) * exp (R ^ 2 / (4 * a))) *
        exp (-(1 / (8 * b)) * y ^ 2) := by
  rw [heatKernel_real]
  calc
    _ ≤ (4 * π * a) ^ (-(1 : ℝ) / 2) *
        (exp (R ^ 2 / (4 * a)) * exp (-(1 / (8 * b)) * y ^ 2)) := by
      apply mul_le_mul
      · apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by norm_num)
        gcongr
      · exact gaussian_shift_bound ha hat htb hx y
      · positivity
      · positivity
    _ = _ := by ring

/-- A single integrable function dominates the kernel and its first two spatial
(and first time) derivatives on `a ≤ t ≤ b`, `|x| ≤ R`, with `a > 0`.
The integration variable `y` is unrestricted. -/
theorem exists_integrable_heatKernel_bound {a b R : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ B : ℝ → ℝ, Integrable B ∧ ∀ t ∈ Icc a b, ∀ x, |x| ≤ R → ∀ y,
      ‖heatKernel ℝ t (x - y)‖ ≤ B y ∧
      ‖heatKernelDx t (x - y)‖ ≤ B y ∧ ‖heatKernelDxx t (x - y)‖ ≤ B y := by
  have hb : 0 < b := ha.trans_le hab
  let C := (4 * π * a) ^ (-(1 : ℝ) / 2) * exp (R ^ 2 / (4 * a))
  let Q := 3 + 2 * R ^ 2
  let D := 1 + Q / (2 * a) + Q / (4 * a ^ 2) + 1 / (2 * a)
  let G := fun y : ℝ => exp (-(1 / (8 * b)) * y ^ 2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hG (y : ℝ) : 0 ≤ G y := (exp_pos _).le
  have hi0 : Integrable G := integrable_exp_neg_mul_sq (by positivity)
  have hi2 : Integrable (fun y : ℝ => y ^ 2 * G y) := by
    simpa only [Real.rpow_two] using
      (integrable_rpow_mul_exp_neg_mul_sq (b := 1 / (8 * b)) (by positivity)
        (s := 2) (by norm_num))
  refine ⟨fun y => D * C * ((1 + y ^ 2) * G y), ?_, ?_⟩
  · simpa only [add_mul, one_mul, Pi.add_apply] using! (hi0.add hi2).const_mul (D * C)
  · intro t ht x hx y
    have hat := ht.1
    have htb := ht.2
    have ht0 : 0 < t := ha.trans_le ht.1
    have hk0 := (heatKernel_pos ht0 (x - y)).le
    have hk := kernel_bound ha ht.1 ht.2 hx y
    change heatKernel ℝ t (x - y) ≤ C * G y at hk
    have hxx : x ^ 2 ≤ R ^ 2 := by
      nlinarith [sq_abs x, mul_nonneg (sub_nonneg.mpr hx)
        (add_nonneg (le_trans (abs_nonneg x) hx) (abs_nonneg x))]
    have hz2 : (x - y) ^ 2 ≤ Q * (1 + y ^ 2) := by
      dsimp [Q]
      nlinarith [sq_nonneg (x + y), sq_nonneg R, sq_nonneg y,
        mul_nonneg (sq_nonneg R) (sq_nonneg y)]
    have hz : |x - y| ≤ Q * (1 + y ^ 2) := by
      have hz' : |x - y| ≤ 1 + (x - y) ^ 2 := by
        nlinarith [sq_nonneg (|x - y| - 1), sq_abs (x - y)]
      dsimp [Q] at *
      nlinarith [sq_nonneg (x + y), sq_nonneg R, sq_nonneg y,
        mul_nonneg (sq_nonneg R) (sq_nonneg y)]
    have hqa : 0 ≤ Q / (2 * a) := by positivity
    have hqaa : 0 ≤ Q / (4 * a ^ 2) := by positivity
    have haa : 0 ≤ 1 / (2 * a) := by positivity
    have h1 : 1 ≤ D := by dsimp [D]; linarith
    have h2 : Q / (2 * a) ≤ D := by dsimp [D]; linarith
    have h3 : Q / (4 * a ^ 2) + 1 / (2 * a) ≤ D := by dsimp [D]; linarith
    refine ⟨?_, ?_, ?_⟩
    · rw [Real.norm_eq_abs, abs_of_nonneg hk0]
      calc
        _ ≤ C * G y := hk
        _ ≤ D * (C * G y) := le_mul_of_one_le_left (mul_nonneg hC (hG y)) h1
        _ ≤ D * (C * G y) * (1 + y ^ 2) :=
          le_mul_of_one_le_right (mul_nonneg hD (mul_nonneg hC (hG y))) (by nlinarith [sq_nonneg y])
        _ = _ := by ring
    · simp only [heatKernelDx, Real.norm_eq_abs, abs_mul, abs_div, abs_neg,
        abs_of_pos (by positivity : 0 < 2 * t), abs_of_nonneg hk0]
      calc
        _ ≤ (Q * (1 + y ^ 2) / (2 * a)) * (C * G y) := by
          apply mul_le_mul
          · exact (div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
              (by linarith : 2 * a ≤ 2 * t)).trans
                (div_le_div_of_nonneg_right hz (by positivity))
          · exact hk
          · exact hk0
          · positivity
        _ ≤ D * C * ((1 + y ^ 2) * G y) := by
          calc
            _ = (Q / (2 * a)) * (C * ((1 + y ^ 2) * G y)) := by ring
            _ ≤ _ := by
              have hh := mul_le_mul_of_nonneg_right h2
                (mul_nonneg hC (mul_nonneg (by positivity : 0 ≤ 1 + y ^ 2) (hG y)))
              simpa only [mul_assoc] using hh
    · simp only [heatKernelDxx, Real.norm_eq_abs, abs_mul, abs_of_nonneg hk0]
      have he : |(x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)| ≤
          (Q / (4 * a ^ 2) + 1 / (2 * a)) * (1 + y ^ 2) := by
        calc
          _ ≤ (x - y) ^ 2 / (4 * t ^ 2) + 1 / (2 * t) := by
            calc
              _ ≤ |(x - y) ^ 2 / (4 * t ^ 2)| + |1 / (2 * t)| := abs_sub _ _
              _ = _ := by rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
          _ ≤ Q * (1 + y ^ 2) / (4 * a ^ 2) + 1 / (2 * a) := by
            apply add_le_add
            · exact (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
                (by nlinarith : 4 * a ^ 2 ≤ 4 * t ^ 2)).trans
                  (div_le_div_of_nonneg_right hz2 (by positivity))
            · exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
          _ = Q / (4 * a ^ 2) * (1 + y ^ 2) + 1 / (2 * a) := by ring
          _ ≤ Q / (4 * a ^ 2) * (1 + y ^ 2) + 1 / (2 * a) * (1 + y ^ 2) :=
            add_le_add le_rfl
              (le_mul_of_one_le_right haa (by nlinarith [sq_nonneg y] : (1 : ℝ) ≤ 1 + y ^ 2))
          _ = _ := by ring
      calc
        _ ≤ ((Q / (4 * a ^ 2) + 1 / (2 * a)) * (1 + y ^ 2)) * (C * G y) :=
          mul_le_mul he hk hk0 (by positivity)
        _ = (Q / (4 * a ^ 2) + 1 / (2 * a)) * (C * ((1 + y ^ 2) * G y)) := by ring
        _ ≤ _ := by
          have hh := mul_le_mul_of_nonneg_right h3
            (mul_nonneg hC (mul_nonneg (by positivity : 0 ≤ 1 + y ^ 2) (hG y)))
          simpa only [mul_assoc] using hh

end MathlibExt.Analysis.PDE.HeatKernel
