/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.VerticalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import MathlibExt.Analysis.Complex.VerticalIntegral.CauchyKernel
import MathlibExt.Analysis.Complex.VerticalIntegral.ContourShift
import MathlibExt.Analysis.Complex.VerticalIntegral.Integrable
import MathlibExt.Analysis.PerronKernel

/-!
# Perron-type kernels on a vertical line

Principal values of the classical Perron kernels along a line `re s = c` with `c > 0`:

* the discontinuous integral: `(1 / 2πi) ∫_(c) x ^ s / s ds` is `1`, `1 / 2` or `0` according
  as `x > 1`, `x = 1` or `0 < x < 1`;
* the higher-order kernel: for `k ≥ 1`, `(1 / 2πi) ∫_(c) x ^ s / s ^ (k + 1) ds` is
  `(log x) ^ k / k!` for `x ≥ 1` and `0` for `0 < x ≤ 1`;
* the Riesz (factorial) kernel: for `k ≥ 1`,
  `(1 / 2πi) ∫_(c) x ^ s / (s (s + 1) ⋯ (s + k)) ds` is `(1 - 1 / x) ^ k / k!` for `x ≥ 1` and
  `0` for `0 ≤ x ≤ 1`.

The discontinuous integral comes from the quantitative truncation bounds
`PerronKernel.perron_bound_gt_one` and `PerronKernel.perron_bound_lt_one`. The higher-order
kernel is computed by integrating by parts on the line for `x ≥ 1`, and by moving the line to
`re s → +∞` for `x ≤ 1`. The factorial kernel follows by induction on `k` from the partial
fraction recursion `1 / P (k + 1) s = (1 / P k s - 1 / P k (s + 1)) / (k + 1)`.

## Main statements

* `Complex.hasVerticalIntegral_cpow_div_self_of_one_lt`,
  `Complex.hasVerticalIntegral_cpow_div_self_of_lt_one`, `Complex.hasVerticalIntegral_one_div`
* `Complex.hasVerticalIntegral_cpow_div_pow_succ_of_one_le`,
  `Complex.hasVerticalIntegral_cpow_div_pow_succ_of_le_one`
* `Complex.hasVerticalIntegral_cpow_div_prod_of_one_le`,
  `Complex.hasVerticalIntegral_cpow_div_prod_of_le_one`
-/

@[expose] public section

open Filter MeasureTheory
open scoped Real Topology

namespace Complex

/-! ### The discontinuous integral -/

private theorem smul_integral_eq_perronKernel (x c R : ℝ) :
    (1 / (2 * π)) • ∫ t in (-R)..R, (fun s : ℂ => (x : ℂ) ^ s / s) (c + t * I) =
      PerronKernel.perronKernel x c R := by
  simp [PerronKernel.perronKernel, Complex.real_smul]

private theorem tendsto_const_div_div_pi (K : ℝ) :
    Tendsto (fun T : ℝ => K / T / π) atTop (𝓝 0) := by
  simpa using (tendsto_const_nhds.div_atTop tendsto_id).div_const π

/-- **The discontinuous integral for `x > 1`.** For `x > 1` and `c > 0`,
`(1 / 2πi) ∫_(c) x ^ s / s ds = 1` as a principal value. -/
theorem hasVerticalIntegral_cpow_div_self_of_one_lt {x c : ℝ} (hx : 1 < x) (hc : 0 < c) :
    HasVerticalIntegral c (fun s : ℂ => (x : ℂ) ^ s / s) 1 := by
  unfold HasVerticalIntegral
  simp only [smul_integral_eq_perronKernel]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (tendsto_const_div_div_pi (Real.exp (Real.log x * c) / Real.log x))
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  exact PerronKernel.perron_bound_gt_one (by linarith) hx hc hR

/-- **The discontinuous integral for `0 < x < 1`.** For `0 < x < 1` and `c > 0`,
`(1 / 2πi) ∫_(c) x ^ s / s ds = 0` as a principal value. -/
theorem hasVerticalIntegral_cpow_div_self_of_lt_one {x c : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (hc : 0 < c) : HasVerticalIntegral c (fun s : ℂ => (x : ℂ) ^ s / s) 0 := by
  unfold HasVerticalIntegral
  simp only [smul_integral_eq_perronKernel]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (tendsto_const_div_div_pi (Real.exp (Real.log x * c) / |Real.log x|))
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  exact PerronKernel.perron_bound_lt_one hx0 hx1 hc hR

/-- **The discontinuous integral at `x = 1`.** For `c > 0`, `(1 / 2πi) ∫_(c) ds / s = 1 / 2`
as a principal value. -/
theorem hasVerticalIntegral_one_div {c : ℝ} (hc : 0 < c) :
    HasVerticalIntegral c (fun s : ℂ => 1 / s) (1 / 2) := by
  unfold HasVerticalIntegral
  have hev : (fun R : ℝ => ((1 / π * Real.arctan (R / c) : ℝ) : ℂ)) =ᶠ[atTop]
      fun R : ℝ => (1 / (2 * π)) • ∫ t in (-R)..R, (fun s : ℂ => 1 / s) (c + t * I) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    rw [Complex.vertical_side_one_div hc.ne' hR, Complex.real_smul]
    push_cast
    field_simp
  refine Tendsto.congr' hev ?_
  have harc : Tendsto (fun R : ℝ => Real.arctan (R / c)) atTop (𝓝 (π / 2)) :=
    (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
      (tendsto_id.atTop_div_const hc)
  have hmul := harc.const_mul (1 / π)
  rw [show 1 / π * (π / 2) = 1 / 2 by field_simp] at hmul
  have h2 := (continuous_ofReal.tendsto _).comp hmul
  rw [show ((1 / 2 : ℝ) : ℂ) = 1 / 2 by push_cast; ring] at h2
  exact h2

/-! ### The kernel `x ^ s / s ^ (k + 1)` -/

/-- **The order-`(k + 1)` Perron kernel for `x ≥ 1`.** For `k ≥ 1`, `c > 0` and `x ≥ 1`,
`(1 / 2πi) ∫_(c) x ^ s / s ^ (k + 1) ds = (log x) ^ k / k!`. -/
theorem hasVerticalIntegral_cpow_div_pow_succ_of_one_le {k : ℕ} {x c : ℝ} (hk : 1 ≤ k)
    (hc : 0 < c) (hx : 1 ≤ x) :
    HasVerticalIntegral c (fun s : ℂ => (x : ℂ) ^ s / s ^ (k + 1))
      ((Real.log x : ℂ) ^ k / (k.factorial : ℂ)) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hcne : c ≠ 0 := hc.ne'
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log x := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := hLdef ▸ Real.log_nonneg hx
  have hxe : ∀ s : ℂ, (x : ℂ) ^ s = exp ((L : ℂ) * s) := by
    intro s
    rw [hLdef, cpow_def_of_ne_zero (by exact_mod_cast hx0.ne' : (x : ℂ) ≠ 0),
      ofReal_log hx0.le]
  -- the point on the vertical line
  obtain ⟨w, hwdef⟩ : ∃ w : ℝ → ℂ, w = fun t : ℝ => (c : ℂ) + t * I := ⟨_, rfl⟩
  have hwval : ∀ t : ℝ, w t = (c : ℂ) + t * I := fun t => by rw [hwdef]
  have hwre : ∀ t : ℝ, (w t).re = c := by intro t; rw [hwval]; simp
  have hwim : ∀ t : ℝ, (w t).im = t := by intro t; rw [hwval]; simp
  have hwne : ∀ t : ℝ, w t ≠ 0 := by
    intro t h
    have h1 : (w t).re = c := hwre t
    rw [h, zero_re] at h1
    exact hcne h1.symm
  have hwcont : Continuous w := by rw [hwdef]; fun_prop
  have hwd : ∀ t : ℝ, HasDerivAt w I t := by
    intro t
    rw [hwdef]
    simpa using (((hasDerivAt_id t).ofReal_comp).mul_const I).const_add (c : ℂ)
  -- the integrand family
  obtain ⟨f, hfdef⟩ : ∃ f : ℕ → ℝ → ℂ,
      f = fun (m : ℕ) (t : ℝ) => exp ((L : ℂ) * w t) / (w t) ^ (m + 1) := ⟨_, rfl⟩
  have hfval : ∀ (m : ℕ) (t : ℝ), f m t = exp ((L : ℂ) * w t) / (w t) ^ (m + 1) := by
    intro m t; rw [hfdef]
  have hfnorm : ∀ (m : ℕ) (t : ℝ), ‖f m t‖ = Real.exp (L * c) / ‖w t‖ ^ (m + 1) := by
    intro m t
    have hre : ((L : ℂ) * w t).re = L * c := by simp [mul_re, hwre t]
    rw [hfval, norm_div, norm_exp, norm_pow, hre]
  have hfcont : ∀ m : ℕ, Continuous (f m) := by
    intro m
    have hrw : f m = fun t : ℝ => exp ((L : ℂ) * w t) / (w t) ^ (m + 1) := funext (hfval m)
    rw [hrw]
    exact Continuous.div (continuous_exp.comp (continuous_const.mul hwcont))
      (hwcont.pow _) fun t => pow_ne_zero _ (hwne t)
  -- absolute integrability for order at least two
  have hInt : ∀ n : ℕ, Integrable (f (n + 1)) := fun n =>
    integrable_of_norm_le_div_pow hc (Real.exp_pos (L * c)).le (hfcont (n + 1))
      fun t => le_of_eq (by rw [hfnorm, hwval])
  -- truncated integrals
  obtain ⟨A, hAdef⟩ : ∃ A : ℕ → ℝ → ℂ, A = fun (m : ℕ) (R : ℝ) => ∫ t in (-R)..R, f m t :=
    ⟨_, rfl⟩
  have hAval : ∀ (m : ℕ) (R : ℝ), A m R = ∫ t in (-R)..R, f m t := by intro m R; rw [hAdef]
  have hconv : ∀ n : ℕ, Tendsto (A (n + 1)) atTop (𝓝 (∫ t : ℝ, f (n + 1) t)) := fun n =>
    (hInt n).tendsto_intervalIntegral_neg_self.congr fun R => (hAval (n + 1) R).symm
  -- derivatives for the integration by parts
  have hud : ∀ t : ℝ, HasDerivAt (fun t : ℝ => exp ((L : ℂ) * w t))
      ((L : ℂ) * I * exp ((L : ℂ) * w t)) t := by
    intro t
    have h2 := ((hwd t).const_mul (L : ℂ)).cexp
    rw [show (L : ℂ) * I * exp ((L : ℂ) * w t) = exp ((L : ℂ) * w t) * ((L : ℂ) * I) by ring]
    exact h2
  have hvd : ∀ (m : ℕ) (t : ℝ), HasDerivAt (fun t : ℝ => ((w t) ^ (m + 1))⁻¹)
      (-((m : ℂ) + 1) * I / (w t) ^ (m + 2)) t := by
    intro m t
    have hpow : HasDerivAt (fun t : ℝ => (w t) ^ (m + 1)) (((m : ℂ) + 1) * (w t) ^ m * I) t := by
      have h := (hwd t).pow (m + 1)
      simp only [Nat.add_sub_cancel] at h
      push_cast at h
      exact h
    have h2 := hpow.inv (pow_ne_zero _ (hwne t))
    have hw := hwne t
    have heq : -((m : ℂ) + 1) * I / (w t) ^ (m + 2) =
        -(((m : ℂ) + 1) * (w t) ^ m * I) / ((w t) ^ (m + 1)) ^ 2 := by
      field_simp
      ring
    rw [heq]
    exact h2
  -- the recursion
  have hIBP : ∀ (n : ℕ) (R : ℝ),
      ((n : ℂ) + 1) * A (n + 1) R = (L : ℂ) * A n R + I * (f n R - f n (-R)) := by
    intro n R
    have hcontu : Continuous fun t : ℝ => exp ((L : ℂ) * w t) :=
      continuous_exp.comp (continuous_const.mul hwcont)
    have hcontv' : Continuous fun t : ℝ => -((n : ℂ) + 1) * I / (w t) ^ (n + 2) :=
      continuous_const.div (hwcont.pow _) fun t => pow_ne_zero _ (hwne t)
    have hraw := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := fun t : ℝ => exp ((L : ℂ) * w t))
      (u' := fun t : ℝ => (L : ℂ) * I * exp ((L : ℂ) * w t))
      (v := fun t : ℝ => ((w t) ^ (n + 1))⁻¹)
      (v' := fun t : ℝ => -((n : ℂ) + 1) * I / (w t) ^ (n + 2))
      (a := -R) (b := R) (fun t _ => hud t) (fun t _ => hvd n t)
      ((continuous_const.mul hcontu).intervalIntegrable _ _) (hcontv'.intervalIntegrable _ _)
    have hL1 : (∫ t in (-R)..R, exp ((L : ℂ) * w t) * (-((n : ℂ) + 1) * I / (w t) ^ (n + 2))) =
        -((n : ℂ) + 1) * I * A (n + 1) R := by
      rw [hAval, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun t _ => ?_
      rw [hfval]
      ring
    have hL2 : (∫ t in (-R)..R, ((L : ℂ) * I * exp ((L : ℂ) * w t)) * ((w t) ^ (n + 1))⁻¹) =
        (L : ℂ) * I * A n R := by
      rw [hAval, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun t _ => ?_
      rw [hfval]
      ring
    have hb1 : exp ((L : ℂ) * w R) * ((w R) ^ (n + 1))⁻¹ = f n R := by rw [hfval]; ring
    have hb2 : exp ((L : ℂ) * w (-R)) * ((w (-R)) ^ (n + 1))⁻¹ = f n (-R) := by
      rw [hfval]; ring
    rw [hL1, hL2, hb1, hb2] at hraw
    linear_combination I * hraw + (((n : ℂ) + 1) * A (n + 1) R - (L : ℂ) * A n R) * I_mul_I
  -- the boundary terms vanish
  have hfbd : ∀ (n : ℕ) (t : ℝ), 1 ≤ |t| → ‖f n t‖ ≤ Real.exp (L * c) / |t| := by
    intro n t ht
    rw [hfnorm]
    have h1 : |t| ≤ ‖w t‖ := by
      have h := abs_im_le_norm (w t)
      rwa [hwim t] at h
    have h2 : |t| ≤ ‖w t‖ ^ (n + 1) :=
      le_trans h1 (le_self_pow₀ (le_trans ht h1) (Nat.succ_ne_zero n))
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le (lt_of_lt_of_le zero_lt_one ht) h2
  have hbdry : ∀ n : ℕ, Tendsto (fun R : ℝ => f n R - f n (-R)) atTop (𝓝 0) := by
    intro n
    refine squeeze_zero_norm' (a := fun R : ℝ => 2 * Real.exp (L * c) / R) ?_ ?_
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
      have h1 : |R| = R := abs_of_pos (lt_of_lt_of_le zero_lt_one hR)
      have h2 : |(-R)| = R := by rw [abs_neg]; exact h1
      have b1 := hfbd n R (by rw [h1]; exact hR)
      have b2 := hfbd n (-R) (by rw [h2]; exact hR)
      rw [h1] at b1
      rw [h2] at b2
      calc ‖f n R - f n (-R)‖ ≤ ‖f n R‖ + ‖f n (-R)‖ := norm_sub_le _ _
        _ ≤ Real.exp (L * c) / R + Real.exp (L * c) / R := add_le_add b1 b2
        _ = 2 * Real.exp (L * c) / R := by ring
    · exact tendsto_const_nhds.div_atTop tendsto_id
  -- base case of the recursion
  have hbase : Tendsto (A 1) atTop (𝓝 (2 * (π : ℂ) * (L : ℂ))) := by
    rcases eq_or_lt_of_le hL0 with hL | hL
    · have hLc : (L : ℂ) = 0 := by rw [← hL]; simp
      have h0 : ∀ R : ℝ, A 1 R = I * (f 0 R - f 0 (-R)) := by
        intro R
        have h := hIBP 0 R
        simp only [Nat.cast_zero, zero_add, one_mul, hLc, zero_mul] at h
        linear_combination h
      have ht : Tendsto (fun R : ℝ => I * (f 0 R - f 0 (-R))) atTop (𝓝 0) := by
        simpa using (hbdry 0).const_mul I
      rw [hLc, mul_zero]
      exact ht.congr fun R => (h0 R).symm
    · have hLne : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
      have hx1 : 1 < x := by
        rcases lt_or_eq_of_le hx with h | h
        · exact h
        · exfalso
          rw [hLdef, ← h] at hL
          simp at hL
      have h0 : ∀ R : ℝ, A 0 R = (A 1 R - I * (f 0 R - f 0 (-R))) / (L : ℂ) := by
        intro R
        have h := hIBP 0 R
        simp only [Nat.cast_zero, zero_add, one_mul] at h
        rw [eq_div_iff hLne]
        linear_combination -h
      have hA0 : Tendsto (A 0) atTop (𝓝 ((∫ t : ℝ, f 1 t) / (L : ℂ))) := by
        have h1 : Tendsto (fun R : ℝ => (A 1 R - I * (f 0 R - f 0 (-R))) / (L : ℂ)) atTop
            (𝓝 (((∫ t : ℝ, f 1 t) - I * 0) / (L : ℂ))) :=
          ((hconv 0).sub ((hbdry 0).const_mul I)).div_const _
        rw [mul_zero, sub_zero] at h1
        exact h1.congr fun R => (h0 R).symm
      have hK : Tendsto (fun R : ℝ => ((1 / (2 * π) : ℝ) : ℂ) * A 0 R) atTop (𝓝 1) := by
        refine Tendsto.congr (fun R => ?_) (hasVerticalIntegral_cpow_div_self_of_one_lt hx1 hc)
        rw [Complex.real_smul, hAval]
        congr 1
        refine intervalIntegral.integral_congr fun t _ => ?_
        simp only [hfval, hwval, hxe, zero_add, pow_one]
      have hlim2 := tendsto_nhds_unique (hA0.const_mul ((1 / (2 * π) : ℝ) : ℂ)) hK
      have hz1 : (∫ t : ℝ, f 1 t) = 2 * (π : ℂ) * (L : ℂ) := by
        have hpiC : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
        push_cast at hlim2
        field_simp at hlim2
        linear_combination hlim2
      rw [← hz1]
      exact hconv 0
  -- the induction
  have hz : ∀ n : ℕ, Tendsto (A (n + 1)) atTop
      (𝓝 (2 * (π : ℂ) * (L : ℂ) ^ (n + 1) / ((n + 1).factorial : ℂ))) := by
    intro n
    induction n with
    | zero => simpa using hbase
    | succ n ih =>
        have hn2 : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero (n + 1))
        have hfne : ((n + 1).factorial : ℂ) ≠ 0 := by
          exact_mod_cast (Nat.factorial_pos (n + 1)).ne'
        have heq : ∀ R : ℝ, A (n + 1 + 1) R =
            ((L : ℂ) * A (n + 1) R + I * (f (n + 1) R - f (n + 1) (-R))) / ((n : ℂ) + 2) := by
          intro R
          have h := hIBP (n + 1) R
          push_cast at h
          rw [eq_div_iff hn2]
          linear_combination h
        have ht := ((ih.const_mul (L : ℂ)).add ((hbdry (n + 1)).const_mul I)).div_const
          ((n : ℂ) + 2)
        have hval : ((L : ℂ) * (2 * (π : ℂ) * (L : ℂ) ^ (n + 1) / ((n + 1).factorial : ℂ)) +
              I * 0) / ((n : ℂ) + 2) =
            2 * (π : ℂ) * (L : ℂ) ^ (n + 1 + 1) / ((n + 1 + 1).factorial : ℂ) := by
          have hn2' : (n : ℂ) + 1 + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero (n + 1))
          rw [Nat.factorial_succ (n + 1)]
          push_cast
          field_simp
          ring
        rw [hval] at ht
        exact ht.congr fun R => (heq R).symm
  -- conclusion
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = n + 1 := ⟨k - 1, by omega⟩
  unfold HasVerticalIntegral
  have hfun : ∀ R : ℝ, ((1 / (2 * π) : ℝ) : ℂ) * A (n + 1) R =
      (1 / (2 * π)) • ∫ t in (-R)..R,
        (fun s : ℂ => (x : ℂ) ^ s / s ^ (n + 1 + 1)) (c + t * I) := by
    intro R
    rw [Complex.real_smul, hAval]
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [hfval, hwval, hxe]
  have htend := (hz n).const_mul ((1 / (2 * π) : ℝ) : ℂ)
  have hvalue : ((1 / (2 * π) : ℝ) : ℂ) *
      (2 * (π : ℂ) * (L : ℂ) ^ (n + 1) / ((n + 1).factorial : ℂ)) =
      (Real.log x : ℂ) ^ (n + 1) / ((n + 1).factorial : ℂ) := by
    rw [← hLdef]
    have hpiC : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp
  rw [hvalue] at htend
  exact htend.congr hfun

/-- **The order-`(k + 1)` Perron kernel for `0 < x ≤ 1`.** For `k ≥ 1`, `c > 0` and
`0 < x ≤ 1`, `(1 / 2πi) ∫_(c) x ^ s / s ^ (k + 1) ds = 0`. -/
theorem hasVerticalIntegral_cpow_div_pow_succ_of_le_one {k : ℕ} {x c : ℝ} (hk : 1 ≤ k)
    (hc : 0 < c) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    HasVerticalIntegral c (fun s : ℂ => (x : ℂ) ^ s / s ^ (k + 1)) 0 := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = n + 1 := ⟨k - 1, by omega⟩
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log x := ⟨_, rfl⟩
  have hL0 : L ≤ 0 := hLdef ▸ Real.log_nonpos hx0.le hx1
  have hxe : ∀ s : ℂ, (x : ℂ) ^ s = exp ((L : ℂ) * s) := by
    intro s
    rw [hLdef, cpow_def_of_ne_zero (by exact_mod_cast hx0.ne' : (x : ℂ) ≠ 0),
      ofReal_log hx0.le]
  obtain ⟨G, hGdef⟩ : ∃ G : ℂ → ℂ, G = fun s : ℂ => exp ((L : ℂ) * s) / s ^ (n + 2) :=
    ⟨_, rfl⟩
  have hGval : ∀ s : ℂ, G s = exp ((L : ℂ) * s) / s ^ (n + 2) := fun s => by rw [hGdef]
  have hGdiff : ∀ s : ℂ, s ≠ 0 → DifferentiableAt ℂ G s := by
    intro s hs
    rw [hGdef]
    exact (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => exp ((L : ℂ) * z)) s).div
      (by fun_prop) (pow_ne_zero _ hs)
  have hGnorm : ∀ s : ℂ, ‖G s‖ = Real.exp (L * s.re) / ‖s‖ ^ (n + 2) := by
    intro s
    rw [hGval, norm_div, norm_exp, norm_pow]
    congr 2
    simp [mul_re]
  have hwne : ∀ σ t : ℝ, 0 < σ → (σ : ℂ) + t * I ≠ 0 :=
    fun σ t hσ => ofReal_add_mul_I_ne_zero (Or.inl hσ.ne')
  have hGcont : ∀ σ : ℝ, 0 < σ → Continuous fun t : ℝ => G (σ + t * I) := by
    intro σ hσ
    simp only [hGdef]
    exact Continuous.div (by fun_prop) (by fun_prop) fun t => pow_ne_zero _ (hwne σ t hσ)
  have hGb : ∀ σ : ℝ, 0 < σ → ∀ t : ℝ,
      ‖G (σ + t * I)‖ ≤ Real.exp (L * σ) / ‖(σ : ℂ) + t * I‖ ^ (n + 2) := by
    intro σ hσ t
    rw [hGnorm, show ((σ : ℂ) + t * I).re = σ by simp]
  have hInt : ∀ σ : ℝ, 0 < σ → Integrable fun t : ℝ => G (σ + t * I) := fun σ hσ =>
    integrable_of_norm_le_div_pow hσ (Real.exp_pos _).le (hGcont σ hσ) (hGb σ hσ)
  have hPhibd : ∀ σ : ℝ, 0 < σ →
      ‖∫ t : ℝ, G (σ + t * I)‖ ≤ Real.exp (L * σ) / σ ^ (n + 1) * π := by
    intro σ hσ
    refine le_of_tendsto (hInt σ hσ).tendsto_intervalIntegral_neg_self.norm ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    exact (intervalIntegral.norm_integral_le_integral_norm (by linarith)).trans
      (intervalIntegral_norm_le_of_norm_le_div_pow hσ (Real.exp_pos _).le (hGcont σ hσ)
        (hGb σ hσ) hR)
  -- the horizontal edges decay like `1 / |im s|`
  have hGim : ∀ s : ℂ, c ≤ s.re → 1 ≤ |s.im| → ‖G s‖ ≤ 1 / |s.im| := by
    intro s hcs hs1
    rw [hGnorm]
    have hnum : Real.exp (L * s.re) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have hd0 : |s.im| ≤ ‖s‖ := abs_im_le_norm s
    have hd3 : |s.im| ≤ ‖s‖ ^ (n + 2) := hd0.trans (le_self_pow₀ (hs1.trans hd0) (by omega))
    exact div_le_div₀ zero_le_one hnum (by linarith) hd3
  -- the contour shift
  have hshift : ∀ σ : ℝ, c ≤ σ → ∫ t : ℝ, G (c + t * I) = ∫ t : ℝ, G (σ + t * I) := by
    intro σ hcσ
    have hσ0 : 0 < σ := lt_of_lt_of_le hc hcσ
    refine integral_vertical_eq_of_tendsto_horizontal (fun R _ s hs => ?_) (hInt c hc)
      (hInt σ hσ0) (tendsto_horizontal_sides_of_norm_le_div_abs_im hcσ
        fun s h1 _ h3 => hGim s h1 h3)
    refine (hGdiff s ?_).differentiableWithinAt
    intro h0
    have h1 : s.re ∈ Set.uIcc c σ := hs.1
    rw [Set.uIcc_of_le hcσ] at h1
    have h2 : s.re = 0 := by rw [h0]; simp
    linarith [h1.1]
  -- the value on the line `re s = c` is arbitrarily small
  have hkey : ∀ ε : ℝ, 0 < ε → ‖∫ t : ℝ, G (c + t * I)‖ ≤ ε := by
    intro ε hε
    set σ : ℝ := max (max c 1) (π / ε) with hσdef
    have hσ1 : 1 ≤ σ := le_trans (le_max_right c 1) (le_max_left _ _)
    have hσc : c ≤ σ := le_trans (le_max_left c 1) (le_max_left _ _)
    have hσe : π / ε ≤ σ := le_max_right _ _
    have hσ0 : 0 < σ := lt_of_lt_of_le zero_lt_one hσ1
    have hpiσ : π / σ ≤ ε := by
      rw [div_le_iff₀ hσ0]
      rw [div_le_iff₀ hε] at hσe
      nlinarith
    have hb := hPhibd σ hσ0
    rw [← hshift σ hσc] at hb
    have h1 : Real.exp (L * σ) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have h2 : (1 : ℝ) ≤ σ ^ n := one_le_pow₀ hσ1
    have hle : Real.exp (L * σ) / σ ^ n ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have h3 : Real.exp (L * σ) / σ ^ (n + 1) * π ≤ π / σ := by
      calc Real.exp (L * σ) / σ ^ (n + 1) * π = (Real.exp (L * σ) / σ ^ n) * (π / σ) := by
            rw [pow_succ]; field_simp
        _ ≤ 1 * (π / σ) := mul_le_mul_of_nonneg_right hle (by positivity)
        _ = π / σ := one_mul _
    linarith
  have hPhi0 : ∫ t : ℝ, G (c + t * I) = 0 :=
    norm_le_zero_iff.mp (le_of_forall_pos_le_add fun ε hε => by simpa using hkey ε hε)
  -- conclusion
  have h := hasVerticalIntegral_of_integrable (c := c)
    (f := fun s : ℂ => (x : ℂ) ^ s / s ^ (n + 1 + 1)) (hInt c hc) fun t => by
      simp only [hGval, hxe]
  rwa [hPhi0, smul_zero] at h

/-! ### The kernel `x ^ s / (s (s + 1) ⋯ (s + k))` -/

/-- The partial-fraction recursion for `P n s = s (s + 1) ⋯ (s + n)`. -/
private theorem one_div_prod_range_succ {n : ℕ} {s : ℂ} (hs : 0 < s.re) :
    1 / ∏ j ∈ Finset.range (n + 1 + 1), (s + j) =
      (1 / ∏ j ∈ Finset.range (n + 1), (s + j) -
        1 / ∏ j ∈ Finset.range (n + 1), (s + 1 + j)) / ((n : ℂ) + 1) := by
  have hne : ∀ (m : ℕ) (z : ℂ), 0 < z.re → ∏ j ∈ Finset.range m, (z + j) ≠ 0 := by
    intro m z hz
    refine Finset.prod_ne_zero_iff.mpr fun j _ h => ?_
    have h' := congrArg re h
    simp only [add_re, natCast_re, zero_re] at h'
    linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hs1 : 0 < (s + 1).re := by simp only [add_re, one_re]; linarith
  have hA := hne (n + 1) s hs
  have hB := hne (n + 1) (s + 1) hs1
  have hQ := hne (n + 1 + 1) s hs
  have h1 : ∏ j ∈ Finset.range (n + 1 + 1), (s + j) =
      (∏ j ∈ Finset.range (n + 1), (s + j)) * (s + ((n : ℂ) + 1)) := by
    rw [Finset.prod_range_succ]
    push_cast
    ring
  have h2 : ∏ j ∈ Finset.range (n + 1 + 1), (s + j) =
      s * ∏ j ∈ Finset.range (n + 1), (s + 1 + j) := by
    rw [Finset.prod_range_succ']
    push_cast
    rw [mul_comm]
    congr 1
    · ring
    · exact Finset.prod_congr rfl fun j _ => by ring
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  field_simp
  linear_combination (-∏ j ∈ Finset.range (n + 1), (s + 1 + j)) * h1 +
    (∏ j ∈ Finset.range (n + 1), (s + j)) * h2

/-- The factorial kernel by induction from the order-one kernel: if
`(1 / 2πi) ∫_(d) x ^ s / s ds = v₀` for every `d > 0`, then
`(1 / 2πi) ∫_(d) x ^ s / (s ⋯ (s + n)) ds = v₀ (1 - 1 / x) ^ n / n!` for every `d > 0`. -/
private theorem hasVerticalIntegral_cpow_div_prod_of_base {x : ℝ} (hx : 0 < x) {v₀ : ℂ}
    (hbase : ∀ d : ℝ, 0 < d → HasVerticalIntegral d (fun s : ℂ => (x : ℂ) ^ s / s) v₀)
    (n : ℕ) {d : ℝ} (hd : 0 < d) :
    HasVerticalIntegral d (fun s : ℂ => (x : ℂ) ^ s / ∏ j ∈ Finset.range (n + 1), (s + j))
      (v₀ * (1 - 1 / (x : ℂ)) ^ n / (n.factorial : ℂ)) := by
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  set P : ℕ → ℂ → ℂ := fun n s => ∏ j ∈ Finset.range (n + 1), (s + (j : ℂ)) with hP
  have hPne : ∀ n (s : ℂ), 0 < s.re → P n s ≠ 0 := by
    intro n s hs
    refine Finset.prod_ne_zero_iff.mpr fun j _ h => ?_
    have h' := congrArg re h
    simp only [add_re, natCast_re, zero_re] at h'
    linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hcont : ∀ n (d : ℝ), 0 < d → ∀ R : ℝ, IntervalIntegrable
      (fun t : ℝ => (x : ℂ) ^ ((d : ℂ) + t * I) / P n ((d : ℂ) + t * I)) volume (-R) R := by
    intro n d hd R
    refine (Continuous.div ?_ ?_ fun t => hPne n _ (by simp [hd])).intervalIntegrable _ _
    · exact Continuous.const_cpow (by fun_prop) (Or.inl hxC)
    · exact continuous_finsetProd _ fun j _ => by fun_prop
  induction n generalizing d with
  | zero => simpa using hbase d hd
  | succ n ih =>
    have hA := ih hd
    have hB0 := ih (d := d + 1) (by linarith)
    rw [show d + 1 = d - (-1) by ring] at hB0
    have hB := hB0.comp_sub_ofReal.const_mul ((x : ℂ)⁻¹)
    have iB : ∀ R : ℝ, IntervalIntegrable (fun t : ℝ => (x : ℂ)⁻¹ *
        ((x : ℂ) ^ ((d : ℂ) + t * I - ((-1 : ℝ) : ℂ)) /
          P n ((d : ℂ) + t * I - ((-1 : ℝ) : ℂ)))) volume (-R) R := by
      intro R
      have := (hcont n (d + 1) (by linarith) R).const_mul ((x : ℂ)⁻¹)
      convert this using 3 with t
      rw [show (d : ℂ) + t * I - ((-1 : ℝ) : ℂ) = ((d + 1 : ℝ) : ℂ) + t * I by push_cast; ring]
    have hS := ((hA.sub hB (hcont n d hd) iB).const_mul (1 / ((n : ℂ) + 1))).congr_line
      (g := fun s => (x : ℂ) ^ s / P (n + 1) s) fun t => by
        have hs : 0 < ((d : ℂ) + t * I).re := by simp [hd]
        have e : (d : ℂ) + t * I - ((-1 : ℝ) : ℂ) = (d : ℂ) + t * I + 1 := by push_cast; ring
        simp only [hP]
        rw [e, cpow_add _ 1 hxC, cpow_one,
          div_eq_mul_one_div ((x : ℂ) ^ _) (∏ j ∈ Finset.range (n + 1 + 1), _),
          one_div_prod_range_succ hs]
        have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
        have hA' := hPne n _ hs
        have hB' := hPne n ((d : ℂ) + t * I + 1) (by simp; linarith)
        simp only [hP] at hA' hB'
        field_simp
    convert hS using 1
    rw [Nat.factorial_succ, pow_succ]
    push_cast
    have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    set y : ℂ := 1 - 1 / (x : ℂ) with hy
    have hxinv : (x : ℂ)⁻¹ = 1 - y := by rw [hy]; ring
    rw [hxinv]
    clear_value y
    field_simp
    ring

/-- **The Riesz kernel for `x ≥ 1`.** For `k ≥ 1`, `c > 0` and `x ≥ 1`,
`(1 / 2πi) ∫_(c) x ^ s / (s (s + 1) ⋯ (s + k)) ds = (1 - 1 / x) ^ k / k!`. -/
theorem hasVerticalIntegral_cpow_div_prod_of_one_le {k : ℕ} {x c : ℝ} (hk : 1 ≤ k)
    (hc : 0 < c) (hx : 1 ≤ x) :
    HasVerticalIntegral c (fun s : ℂ => (x : ℂ) ^ s / ∏ j ∈ Finset.range (k + 1), (s + j))
      ((1 - 1 / (x : ℂ)) ^ k / (k.factorial : ℂ)) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  set v₀ : ℂ := if 1 < x then 1 else 1 / 2 with hv₀
  have hbase : ∀ d : ℝ, 0 < d → HasVerticalIntegral d (fun s : ℂ => (x : ℂ) ^ s / s) v₀ := by
    intro d hd
    by_cases h1 : 1 < x
    · simp only [hv₀, h1, ↓reduceIte]
      exact hasVerticalIntegral_cpow_div_self_of_one_lt h1 hd
    · have hx1 : x = 1 := le_antisymm (not_lt.mp h1) hx
      simp only [hv₀, h1, ↓reduceIte]
      exact (hasVerticalIntegral_one_div hd).congr_line fun t => by simp [hx1]
  convert hasVerticalIntegral_cpow_div_prod_of_base hx0 hbase k hc using 1
  by_cases h1 : 1 < x
  · simp only [hv₀, h1, ↓reduceIte, one_mul]
  · have hx1 : x = 1 := le_antisymm (not_lt.mp h1) hx
    simp [hx1, zero_pow (by omega : k ≠ 0)]

/-- **The Riesz kernel for `0 ≤ x ≤ 1`.** For `k ≥ 1`, `c > 0` and `0 ≤ x ≤ 1`,
`(1 / 2πi) ∫_(c) x ^ s / (s (s + 1) ⋯ (s + k)) ds = 0`. At `x = 0` the integrand vanishes on
the line, since `0 ^ s = 0` for `s ≠ 0`. -/
theorem hasVerticalIntegral_cpow_div_prod_of_le_one {k : ℕ} {x c : ℝ} (hk : 1 ≤ k)
    (hc : 0 < c) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    HasVerticalIntegral c (fun s : ℂ => (x : ℂ) ^ s / ∏ j ∈ Finset.range (k + 1), (s + j)) 0 := by
  rcases hx0.eq_or_lt with rfl | hx0
  · refine hasVerticalIntegral_zero.congr_line fun t => ?_
    have hs : (c : ℂ) + t * I ≠ 0 := ofReal_add_mul_I_ne_zero (Or.inl hc.ne')
    simp [zero_cpow hs]
  set v₀ : ℂ := if x < 1 then 0 else 1 / 2 with hv₀
  have hbase : ∀ d : ℝ, 0 < d → HasVerticalIntegral d (fun s : ℂ => (x : ℂ) ^ s / s) v₀ := by
    intro d hd
    by_cases h1 : x < 1
    · simp only [hv₀, h1, ↓reduceIte]
      exact hasVerticalIntegral_cpow_div_self_of_lt_one hx0 h1 hd
    · have hx1' : x = 1 := le_antisymm hx1 (not_lt.mp h1)
      simp only [hv₀, h1, ↓reduceIte]
      exact (hasVerticalIntegral_one_div hd).congr_line fun t => by simp [hx1']
  convert hasVerticalIntegral_cpow_div_prod_of_base hx0 hbase k hc using 1
  by_cases h1 : x < 1
  · simp [hv₀, h1]
  · have hx1' : x = 1 := le_antisymm hx1 (not_lt.mp h1)
    simp [hx1', zero_pow (by omega : k ≠ 0)]

end Complex
