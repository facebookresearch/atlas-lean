/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
import MathlibExt.Analysis.Complex.Bloch
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Algebra.Order.Round
import Mathlib.Topology.Algebra.Order.Field

@[expose] public section

open Set Filter Topology Metric

namespace MathlibExt.Analysis.Complex.GreatPicardWanted

/-!
# Great Picard theorem (essential singularity)
-/

/-- **Essential isolated singularity.** A function $f : \mathbb{C} \to \mathbb{C}$ has an
essential isolated singularity at $c \in \mathbb{C}$ when $f$ is holomorphic on some punctured
disc $0 < |z - c| < r$ with $r > 0$, $f(z)$ has no finite limit as $z \to c$ with $z \ne c$, and
$|f(z)|$ does not tend to $\infty$ as $z \to c$ with $z \ne c$. -/
def IsEssentialIsolatedSingularityAt (f : ℂ → ℂ) (c : ℂ) : Prop :=
  (∃ r : ℝ, 0 < r ∧ DifferentiableOn ℂ f (Metric.ball c r \ {c})) ∧
  ¬ (∃ l : ℂ, Tendsto f (𝓝[≠] c) (𝓝 l)) ∧
  ¬ Tendsto (fun z => ‖f z‖) (𝓝[≠] c) Filter.atTop

/-- Principal logarithm of a nowhere-zero holomorphic function on a ball. -/
private theorem gp_exists_log
    (c : ℂ) (R : ℝ) (g : ℂ → ℂ)
    (hg : DifferentiableOn ℂ g (Metric.ball c R))
    (hne : ∀ z ∈ Metric.ball c R, g z ≠ 0)
    (a : ℂ) (ha : Complex.exp a = g c)
    (hmem : c ∈ Metric.ball c R) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L (Metric.ball c R) ∧ L c = a ∧
      ∀ z ∈ Metric.ball c R, Complex.exp (L z) = g z := by
  have hopen : IsOpen (Metric.ball c R) := Metric.isOpen_ball
  have hR : 0 < R := by
    rw [Metric.mem_ball, dist_self] at hmem
    exact hmem
  have hg' : DifferentiableOn ℂ (deriv g) (Metric.ball c R) :=
    hg.deriv hopen
  have hlog : DifferentiableOn ℂ (fun z => deriv g z / g z) (Metric.ball c R) :=
    hg'.div hg hne
  have hexact : Complex.IsExactOn (fun z => deriv g z / g z) (Metric.ball c R) :=
    hlog.isExactOn_ball
  obtain ⟨L, hLc, hL⟩ := hexact.with_val_at c a
  refine ⟨L, ?_, hLc, ?_⟩
  · exact (fun z hz => (hL z hz).differentiableAt.differentiableWithinAt)
  · have hE : ∀ z ∈ Metric.ball c R, Complex.exp (-L z) * g z = 1 := by
      have hEderiv : ∀ z ∈ Metric.ball c R,
          HasDerivAt (fun w => Complex.exp (-L w) * g w) 0 z := by
        intro z hz
        have h1 : HasDerivAt L (deriv g z / g z) z := hL z hz
        have hexp : HasDerivAt (fun w => Complex.exp (-L w))
            (-Complex.exp (-L z) * (deriv g z / g z)) z := by
          have hneg : HasDerivAt (fun w => -L w) (-(deriv g z / g z)) z :=
            h1.neg
          have := hneg.cexp
          simpa [mul_comm] using this
        have hg1 : HasDerivAt g (deriv g z) z :=
          hg.hasDerivAt (hopen.mem_nhds hz)
        have hmul := hexp.mul hg1
        have hgz : g z ≠ 0 := hne z hz
        have hzero : -Complex.exp (-L z) * (deriv g z / g z) * g z +
            Complex.exp (-L z) * deriv g z = 0 := by
          field_simp
          ring
        have hfun : ((fun w => Complex.exp (-L w)) * g) = (fun w => Complex.exp (-L w) * g w) := rfl
        rw [hfun] at hmul
        rw [hzero] at hmul
        exact hmul
      have hEdiff : DifferentiableOn ℂ (fun w => Complex.exp (-L w) * g w) (Metric.ball c R) :=
        fun z hz => (hEderiv z hz).differentiableAt.differentiableWithinAt
      have hEqOn : Set.EqOn (deriv (fun w => Complex.exp (-L w) * g w)) 0 (Metric.ball c R) := by
        intro w hw
        have h := (hEderiv w hw).deriv
        simpa using h
      have hconst : ∀ x ∈ Metric.ball c R, ∀ y ∈ Metric.ball c R,
          (fun w => Complex.exp (-L w) * g w) x = (fun w => Complex.exp (-L w) * g w) y := by
        intro x hx y hy
        exact hopen.is_const_of_deriv_eq_zero
          (convex_ball c R |>.isPreconnected) hEdiff hEqOn hx hy
      have hEc : Complex.exp (-L c) * g c = 1 := by
        rw [← ha]
        rw [← Complex.exp_add]
        simp [hLc]
      intro z hz
      have hcc := hconst z hz c hmem
      simpa [hEc] using hcc
    intro z hz
    have h1 := hE z hz
    have hexp0 : Complex.exp (-L z) ≠ 0 := Complex.exp_ne_zero _
    have h2 : Complex.exp (-L z) * g z = Complex.exp (-L z) * Complex.exp (L z) := by
      rw [h1]
      rw [← Complex.exp_add]
      simp
    have h3 : g z = Complex.exp (L z) := (mul_left_cancel₀ hexp0 h2)
    exact h3.symm

/-- Every real is within 2 of a point whose `Real.cosh` squares to a natural. -/
private theorem gp_real_cosh_sq_near (x : ℝ) :
    ∃ a : ℝ, ∃ n : ℕ, |x - a| < 2 ∧ Real.cosh a ^ 2 = n := by
  have hcosh_nn : 0 ≤ Real.cosh x ^ 2 := sq_nonneg _
  have hle : (⌊Real.cosh x ^ 2⌋₊ : ℝ) ≤ Real.cosh x ^ 2 := Nat.floor_le hcosh_nn
  have hlt : Real.cosh x ^ 2 < (⌊Real.cosh x ^ 2⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hcosh1 : 1 ≤ Real.cosh x := Real.one_le_cosh x
  have hn1 : 1 ≤ ⌊Real.cosh x ^ 2⌋₊ :=
    (Nat.one_le_floor_iff _).mpr (one_le_pow₀ hcosh1)
  have hnR : (1 : ℝ) ≤ (⌊Real.cosh x ^ 2⌋₊ : ℝ) := by exact_mod_cast hn1
  set n : ℕ := ⌊Real.cosh x ^ 2⌋₊ with hn
  set s : ℝ := Real.sqrt (n : ℝ) with hs
  set t : ℝ := Real.sqrt ((n : ℝ) - 1) with ht
  have hs2 : s ^ 2 = (n : ℝ) := Real.sq_sqrt (by linarith)
  have ht2 : t ^ 2 = (n : ℝ) - 1 := Real.sq_sqrt (by linarith)
  have hs1 : 1 ≤ s := Real.one_le_sqrt.mpr hnR
  have hspos : 0 < s := by linarith
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  set y : ℝ := s + t with hy
  have hy1 : 1 ≤ y := by linarith
  have hypos : 0 < y := by linarith
  have hyne : y ≠ 0 := ne_of_gt hypos
  have hdiff : y * (s - t) = 1 := by linear_combination hs2 - ht2
  have hyinv : y⁻¹ = s - t := by
    calc y⁻¹ = y⁻¹ * (y * (s - t)) := by rw [hdiff, mul_one]
    _ = s - t := by rw [← mul_assoc, inv_mul_cancel₀ hyne, one_mul]
  have ha0nn : 0 ≤ Real.log y := Real.log_nonneg hy1
  have hcosh_a0 : Real.cosh (Real.log y) = s := by
    rw [Real.cosh_log hypos, hyinv, hy]
    ring
  have hsq : Real.cosh (Real.log y) ^ 2 = (n : ℝ) := by rw [hcosh_a0, hs2]
  have hcosh_le : Real.cosh (Real.log y) ≤ Real.cosh x := by
    have h1 : Real.cosh (Real.log y) ^ 2 ≤ Real.cosh x ^ 2 := by rw [hsq]; exact hle
    have h2 : |Real.cosh (Real.log y)| ≤ |Real.cosh x| := sq_le_sq.mp h1
    rw [abs_of_pos (Real.cosh_pos _), abs_of_pos (Real.cosh_pos _)] at h2
    exact h2
  have ha0_le : Real.log y ≤ |x| := by
    have h := (Real.cosh_le_cosh.mp hcosh_le)
    rwa [abs_of_nonneg ha0nn] at h
  have hexp2 : (4 : ℝ) < Real.exp 2 := by
    have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have hsqe : (2.7182818283 : ℝ) * 2.7182818283 < Real.exp 1 * Real.exp 1 :=
      mul_lt_mul h1 (le_of_lt h1) (by norm_num) (Real.exp_pos 1).le
    have h4 : (4 : ℝ) < 2.7182818283 * 2.7182818283 := by norm_num
    have hexp2eq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      have he : (2 : ℝ) = 1 + 1 := by norm_num
      rw [he, Real.exp_add]
    linarith
  have hexp_bound : Real.exp (|x| - Real.log y) < Real.exp 2 := by
    have hexp_sub : Real.exp (|x| - Real.log y) = Real.exp |x| / y := by
      rw [Real.exp_sub, Real.exp_log hypos]
    rw [hexp_sub]
    have h1 : Real.exp |x| ≤ 2 * Real.cosh x := by
      have e1 : Real.cosh x = Real.cosh |x| := (Real.cosh_abs x).symm
      have e2 : Real.cosh |x| = (Real.exp |x| + Real.exp (-|x|)) / 2 :=
        Real.cosh_eq _
      have hpos : 0 < Real.exp (-|x|) := Real.exp_pos _
      linarith
    have h2 : Real.cosh x < 2 * s := by
      have hn1' : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by linarith
      have h3 : Real.cosh x ^ 2 < (2 * s) ^ 2 := by
        have e : (2 * s) ^ 2 = 4 * (n : ℝ) := by
          have : (2 * s) ^ 2 = 4 * s ^ 2 := by ring
          rw [this, hs2]
        nlinarith [hlt, hn1']
      have h4 : |Real.cosh x| < |2 * s| := sq_lt_sq.mp h3
      rw [abs_of_pos (Real.cosh_pos _), abs_of_pos (by linarith : (0 : ℝ) < 2 * s)] at h4
      exact h4
    have h3 : s ≤ y := by linarith
    have h6 : (2 * Real.cosh x) / y < 4 := by
      rw [div_lt_iff₀ hypos]
      nlinarith [h2, h3, Real.cosh_pos x, hspos, hypos]
    have h5 : Real.exp |x| / y ≤ (2 * Real.cosh x) / y :=
      div_le_div_of_nonneg_right h1 hypos.le
    linarith
  have hlt2 : |x| - Real.log y < 2 := Real.exp_lt_exp.mp hexp_bound
  by_cases h : 0 ≤ x
  · refine ⟨Real.log y, n, ?_, hsq⟩
    have e : |x - Real.log y| = |(|x| - Real.log y)| := by rw [abs_of_nonneg h]
    rw [e, abs_of_nonneg (by linarith : (0 : ℝ) ≤ |x| - Real.log y)]
    exact hlt2
  · have hxneg : x < 0 := lt_of_not_ge h
    have ecosh : Real.cosh (-Real.log y) ^ 2 = (n : ℝ) := by
      rw [Real.cosh_neg]; exact hsq
    refine ⟨-Real.log y, n, ?_, ecosh⟩
    have hx : |x| = -x := abs_of_neg hxneg
    have hnp : x + Real.log y ≤ 0 := by linarith [ha0_le, hx]
    have e : |x - -Real.log y| = |x| - Real.log y := by
      have e1 : x - -Real.log y = x + Real.log y := sub_neg_eq_add _ _
      rw [e1, abs_of_nonpos hnp, hx]
      ring
    rw [e]
    exact hlt2

/-- The points where `Complex.cosh` squares to a natural are 6-dense. -/
private theorem gp_cosh_sq_net (q : ℂ) :
    ∃ ω : ℂ, ∃ n : ℕ, ‖q - ω‖ < 6 ∧ Complex.cosh ω ^ 2 = (n : ℂ) := by
  obtain ⟨a, n, ha2, hcosh⟩ := gp_real_cosh_sq_near q.re
  set m : ℤ := round (q.im / (2 * Real.pi)) with hm
  have hround : |q.im / (2 * Real.pi) - (m : ℝ)| ≤ 1 / 2 := abs_sub_round _
  have hpi : 0 < Real.pi := Real.pi_pos
  have h2pine : (2 : ℝ) * Real.pi ≠ 0 := mul_ne_zero (by norm_num) (ne_of_gt hpi)
  have h2pinn : (0 : ℝ) ≤ 2 * Real.pi := (mul_pos (by norm_num) hpi).le
  have him : |q.im - 2 * Real.pi * (m : ℝ)| ≤ Real.pi := by
    have e : q.im - 2 * Real.pi * (m : ℝ)
        = 2 * Real.pi * (q.im / (2 * Real.pi) - (m : ℝ)) := by
      field_simp
    rw [e, abs_mul, abs_of_nonneg h2pinn]
    calc 2 * Real.pi * |q.im / (2 * Real.pi) - ↑m|
        ≤ 2 * Real.pi * (1 / 2) :=
          mul_le_mul_of_nonneg_left hround h2pinn
      _ = Real.pi := by ring
  set ω : ℂ := (a : ℂ) + (m : ℂ) * (2 * Real.pi * Complex.I) with hω
  have hωre : ω.re = a := by simp [hω]
  have hωim : ω.im = (m : ℝ) * (2 * Real.pi) := by simp [hω]
  have hqre : (q - ω).re = q.re - a := by simp [Complex.sub_re, hωre]
  have hqim : (q - ω).im = q.im - 2 * Real.pi * (m : ℝ) := by
    simp [Complex.sub_im, hωim]; ring
  refine ⟨ω, n, ?_, ?_⟩
  · calc ‖q - ω‖ ≤ |(q - ω).re| + |(q - ω).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ = |q.re - a| + |q.im - 2 * Real.pi * (m : ℝ)| := by rw [hqre, hqim]
      _ < 2 + Real.pi := by linarith [ha2, him]
      _ < 6 := by linarith [Real.pi_lt_d2]
  · have hexp : Complex.exp ω = Complex.exp (a : ℂ) := by
      rw [hω, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    have hexp_neg : Complex.exp (-ω) = Complex.exp (-(a : ℂ)) := by
      have e1 : (-ω) = (-(a : ℂ)) + (((-m : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) := by
        rw [hω]; push_cast; ring
      rw [e1, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    have hcosh_eq : Complex.cosh ω = Complex.cosh (a : ℂ) := by
      have h1 : 2 * Complex.cosh ω = Complex.exp ω + Complex.exp (-ω) :=
        Complex.two_cosh ω
      have h2 : 2 * Complex.cosh (a : ℂ)
          = Complex.exp (a : ℂ) + Complex.exp (-(a : ℂ)) :=
        Complex.two_cosh (a : ℂ)
      rw [hexp, hexp_neg] at h1
      linear_combination (h1 - h2) / 2
    rw [hcosh_eq, ← Complex.ofReal_cosh]
    exact_mod_cast hcosh

/-- Bloch rescaling: a uniform derivative bound from omitted balls. -/
private theorem gp_bloch_deriv_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ H : ℂ → ℂ, ∀ z : ℂ, ∀ R δ : ℝ, 0 < R →
      DifferentiableOn ℂ H (Metric.ball z R) →
      (∀ p : ℂ, ¬ (Metric.ball p δ ⊆ H '' Metric.ball z R)) →
      ‖deriv H z‖ ≤ δ / (B * R) := by
  obtain ⟨B, hB, hbloch⟩ := MathlibExt.Analysis.Complex.BlochWanted.bloch
  refine ⟨B, hB, fun H z R δ hR hH hδ => ?_⟩
  have hRne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hR)
  have hδpos : 0 < δ := by
    by_contra hcon
    have hle : δ ≤ 0 := le_of_not_gt hcon
    have hempty : Metric.ball (H z) δ = ∅ := Metric.ball_eq_empty.mpr hle
    apply hδ (H z)
    rw [hempty]
    exact Set.empty_subset _
  by_cases hd : deriv H z = 0
  · rw [hd, norm_zero]
    exact div_nonneg hδpos.le (mul_nonneg hB.le hR.le)
  · have hRd : (R : ℂ) * deriv H z ≠ 0 := mul_ne_zero hRne hd
    have hmaps : Set.MapsTo (fun w : ℂ => z + (R : ℂ) * w)
        (Metric.ball (0 : ℂ) 1) (Metric.ball z R) := by
      intro w hw
      simp only [Metric.mem_ball, dist_eq_norm, sub_zero] at hw ⊢
      have e : z + (R : ℂ) * w - z = (R : ℂ) * w := by ring
      rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
      calc R * ‖w‖ < R * 1 := mul_lt_mul_of_pos_left hw hR
        _ = R := mul_one _
    have hinner : DifferentiableOn ℂ (fun w : ℂ => z + (R : ℂ) * w)
        (Metric.ball (0 : ℂ) 1) :=
      (differentiableOn_const _).add ((differentiableOn_const _).mul differentiableOn_id)
    have hk : DifferentiableOn ℂ
        (fun w : ℂ => (H (z + (R : ℂ) * w) - H z) / ((R : ℂ) * deriv H z))
        (Metric.ball (0 : ℂ) 1) :=
      ((hH.comp hinner hmaps).sub_const _).div_const _
    have hH_at : HasDerivAt H (deriv H z) z :=
      (hH.differentiableAt
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hR))).hasDerivAt
    have hinner0 : HasDerivAt (fun w : ℂ => z + (R : ℂ) * w) (R : ℂ) 0 := by
      have h1 : HasDerivAt (fun w : ℂ => (R : ℂ) * w) ((R : ℂ) * 1) 0 :=
        (hasDerivAt_id (0 : ℂ)).const_mul _
      rw [mul_one] at h1
      exact h1.const_add _
    have hkas : HasDerivAt
        (fun w : ℂ => (H (z + (R : ℂ) * w) - H z) / ((R : ℂ) * deriv H z)) 1 0 := by
      have h1 : HasDerivAt H (deriv H z) ((fun w : ℂ => z + (R : ℂ) * w) 0) := by
        have h0 : (fun w : ℂ => z + (R : ℂ) * w) 0 = z := by simp
        rw [h0]
        exact hH_at
      have h1 := (h1.comp (0 : ℂ) hinner0).sub_const (H z)
      have h2 := h1.div_const ((R : ℂ) * deriv H z)
      have hder : (deriv H z * (R : ℂ)) / ((R : ℂ) * deriv H z) = 1 := by
        rw [mul_comm (deriv H z) _]
        exact div_self hRd
      rw [hder] at h2
      exact h2
    have hk0 : deriv
        (fun w : ℂ => (H (z + (R : ℂ) * w) - H z) / ((R : ℂ) * deriv H z)) 0
        = 1 := hkas.deriv
    obtain ⟨V, w₀, -, hVsub, -, -, himg⟩ := hbloch _ hk hk0
    have hRd_norm : ‖(R : ℂ) * deriv H z‖ = R * ‖deriv H z‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    have hsub : Metric.ball (H z + (R : ℂ) * deriv H z * w₀) (R * ‖deriv H z‖ * B)
        ⊆ H '' Metric.ball z R := by
      intro p' hp'
      rw [Metric.mem_ball, dist_eq_norm] at hp'
      have huw : ‖(p' - H z) / ((R : ℂ) * deriv H z) - w₀‖ < B := by
        have e : (p' - H z) / ((R : ℂ) * deriv H z) - w₀
            = (p' - (H z + (R : ℂ) * deriv H z * w₀)) / ((R : ℂ) * deriv H z) := by
          field_simp
          ring
        have hpos : 0 < R * ‖deriv H z‖ :=
          mul_pos hR (norm_pos_iff.mpr hd)
        have e2 : B * (R * ‖deriv H z‖) = R * ‖deriv H z‖ * B := by ring
        rw [e, norm_div, hRd_norm, div_lt_iff₀ hpos, e2]
        exact hp'
      have huV : (p' - H z) / ((R : ℂ) * deriv H z)
          ∈ (fun w : ℂ => (H (z + (R : ℂ) * w) - H z)
            / ((R : ℂ) * deriv H z)) '' V := by
        rw [himg]
        rw [Metric.mem_ball, dist_eq_norm]
        exact huw
      obtain ⟨v, hvV, hkv⟩ := huV
      have hmem : z + (R : ℂ) * v ∈ Metric.ball z R := hmaps (hVsub hvV)
      have hHv : H (z + (R : ℂ) * v) = p' := by
        have hkv2 : (H (z + (R : ℂ) * v) - H z) / ((R : ℂ) * deriv H z)
            = (p' - H z) / ((R : ℂ) * deriv H z) := hkv
        have hcan : H (z + (R : ℂ) * v) - H z = p' - H z := by
          have hmul := (div_eq_div_iff hRd hRd).mp hkv2
          have hcan2 := mul_right_cancel₀ hRd hmul
          linear_combination hcan2
        linear_combination hcan
      exact ⟨_, hmem, hHv⟩
    by_contra hcon
    have hlt : δ / (B * R) < ‖deriv H z‖ := not_le.mp hcon
    have hBR : 0 < B * R := mul_pos hB hR
    have h := (div_lt_iff₀ hBR).mp hlt
    have e : ‖deriv H z‖ * (B * R) = R * ‖deriv H z‖ * B := by ring
    have hδR : δ < R * ‖deriv H z‖ * B := by linarith
    exact hδ _ ((Metric.ball_subset_ball hδR.le).trans hsub)

/-- Schottky construction: logarithms and square roots giving `H`. -/
private theorem gp_schottky_aux (g : ℂ → ℂ) (ζ₀ : ℂ) (ρ : ℝ)
    (hρ : 0 < ρ)
    (hg : DifferentiableOn ℂ g (Metric.ball ζ₀ ρ))
    (h0 : ∀ ζ ∈ Metric.ball ζ₀ ρ, g ζ ≠ 0)
    (h1 : ∀ ζ ∈ Metric.ball ζ₀ ρ, g ζ ≠ 1)
    (hlo : 1 / 2 ≤ ‖g ζ₀‖) (hhi : ‖g ζ₀‖ ≤ 3 / 2) :
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (Metric.ball ζ₀ ρ) ∧ ‖H ζ₀‖ ≤ 6 ∧
      (∀ ζ ∈ Metric.ball ζ₀ ρ, ∀ n : ℕ, Complex.cosh (H ζ) ^ 2 ≠ (n : ℂ)) ∧
      ∀ ζ ∈ Metric.ball ζ₀ ρ,
        ‖g ζ‖ ≤ Real.exp (2 * Real.pi * Real.exp (2 * ‖H ζ‖)) := by
  have hmem : ζ₀ ∈ Metric.ball ζ₀ ρ := Metric.mem_ball_self hρ
  have hpi : 0 < Real.pi := Real.pi_pos
  have h2pir : (0 : ℝ) < 2 * Real.pi := mul_pos (by norm_num) hpi
  have h2pi : (2 : ℂ) * Real.pi * Complex.I ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr (ne_of_gt hpi))) Complex.I_ne_zero
  have h2pi_norm : ‖(2 : ℂ) * Real.pi * Complex.I‖ = 2 * Real.pi := by
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [norm_mul, norm_mul, h2, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hpi, Complex.norm_I, mul_one]
  obtain ⟨L₁, hL₁diff, hL₁0, hL₁exp⟩ := gp_exists_log ζ₀ ρ g hg h0
    (Complex.log (g ζ₀)) (Complex.exp_log (h0 ζ₀ hmem)) hmem
  have hFdiff : DifferentiableOn ℂ (fun ζ => L₁ ζ / (2 * Real.pi * Complex.I))
      (Metric.ball ζ₀ ρ) := hL₁diff.div_const _
  have hFg : ∀ ζ ∈ Metric.ball ζ₀ ρ,
      Complex.exp ((L₁ ζ / (2 * Real.pi * Complex.I)) * (2 * Real.pi * Complex.I))
        = g ζ := by
    intro ζ hζ
    rw [div_mul_cancel₀ _ h2pi]
    exact hL₁exp ζ hζ
  have hFint : ∀ ζ ∈ Metric.ball ζ₀ ρ, ∀ k : ℤ,
      L₁ ζ / (2 * Real.pi * Complex.I) ≠ (k : ℂ) := by
    intro ζ hζ k hk
    apply h1 ζ hζ
    have hFV := hFg ζ hζ
    rw [hk, Complex.exp_int_mul_two_pi_mul_I] at hFV
    exact hFV.symm
  have hFne : ∀ ζ ∈ Metric.ball ζ₀ ρ, L₁ ζ / (2 * Real.pi * Complex.I) ≠ 0 := by
    intro ζ hζ hcon
    have hFV := hFint ζ hζ 0
    rw [Int.cast_zero] at hFV
    exact hFV hcon
  have hFm1 : ∀ ζ ∈ Metric.ball ζ₀ ρ,
      L₁ ζ / (2 * Real.pi * Complex.I) - 1 ≠ 0 := by
    intro ζ hζ hcon
    have h_eq : L₁ ζ / (2 * Real.pi * Complex.I) = 1 := by
      linear_combination hcon
    have hFV := hFint ζ hζ 1
    rw [Int.cast_one] at hFV
    exact hFV h_eq
  obtain ⟨L₂, hL₂diff, hL₂0, hL₂exp⟩ := gp_exists_log ζ₀ ρ
    (fun ζ => L₁ ζ / (2 * Real.pi * Complex.I)) hFdiff hFne
    (Complex.log (L₁ ζ₀ / (2 * Real.pi * Complex.I)))
    (Complex.exp_log (hFne ζ₀ hmem)) hmem
  have hFm1diff : DifferentiableOn ℂ
      (fun ζ => L₁ ζ / (2 * Real.pi * Complex.I) - 1) (Metric.ball ζ₀ ρ) :=
    hFdiff.sub_const _
  obtain ⟨L₃, hL₃diff, hL₃0, hL₃exp⟩ := gp_exists_log ζ₀ ρ
    (fun ζ => L₁ ζ / (2 * Real.pi * Complex.I) - 1) hFm1diff hFm1
    (Complex.log (L₁ ζ₀ / (2 * Real.pi * Complex.I) - 1))
    (Complex.exp_log (hFm1 ζ₀ hmem)) hmem
  have hS2 : ∀ ζ ∈ Metric.ball ζ₀ ρ, Complex.exp (L₂ ζ / 2) ^ 2
      = L₁ ζ / (2 * Real.pi * Complex.I) := by
    intro ζ hζ
    have h1sq : Complex.exp (L₂ ζ / 2) ^ 2 = Complex.exp (L₂ ζ) := by
      have e : L₂ ζ / 2 + L₂ ζ / 2 = L₂ ζ := by ring
      calc Complex.exp (L₂ ζ / 2) ^ 2
          = Complex.exp (L₂ ζ / 2) * Complex.exp (L₂ ζ / 2) := pow_two _
        _ = Complex.exp (L₂ ζ / 2 + L₂ ζ / 2) := (Complex.exp_add _ _).symm
        _ = Complex.exp (L₂ ζ) := by rw [e]
    rw [h1sq]
    exact hL₂exp ζ hζ
  have hT2 : ∀ ζ ∈ Metric.ball ζ₀ ρ, Complex.exp (L₃ ζ / 2) ^ 2
      = L₁ ζ / (2 * Real.pi * Complex.I) - 1 := by
    intro ζ hζ
    have h1sq : Complex.exp (L₃ ζ / 2) ^ 2 = Complex.exp (L₃ ζ) := by
      have e : L₃ ζ / 2 + L₃ ζ / 2 = L₃ ζ := by ring
      calc Complex.exp (L₃ ζ / 2) ^ 2
          = Complex.exp (L₃ ζ / 2) * Complex.exp (L₃ ζ / 2) := pow_two _
        _ = Complex.exp (L₃ ζ / 2 + L₃ ζ / 2) := (Complex.exp_add _ _).symm
        _ = Complex.exp (L₃ ζ) := by rw [e]
    rw [h1sq]
    exact hL₃exp ζ hζ
  have hST : ∀ ζ ∈ Metric.ball ζ₀ ρ,
      (Complex.exp (L₂ ζ / 2) - Complex.exp (L₃ ζ / 2))
        * (Complex.exp (L₂ ζ / 2) + Complex.exp (L₃ ζ / 2)) = 1 := by
    intro ζ hζ
    have e : (Complex.exp (L₂ ζ / 2) - Complex.exp (L₃ ζ / 2))
        * (Complex.exp (L₂ ζ / 2) + Complex.exp (L₃ ζ / 2))
        = Complex.exp (L₂ ζ / 2) ^ 2 - Complex.exp (L₃ ζ / 2) ^ 2 := by ring
    rw [e, hS2 ζ hζ, hT2 ζ hζ]
    ring
  have hGne : ∀ ζ ∈ Metric.ball ζ₀ ρ,
      Complex.exp (L₂ ζ / 2) - Complex.exp (L₃ ζ / 2) ≠ 0 := by
    intro ζ hζ hcon
    have h1 := hST ζ hζ
    rw [hcon, zero_mul] at h1
    exact one_ne_zero h1.symm
  have hGdiff : DifferentiableOn ℂ
      (fun ζ => Complex.exp (L₂ ζ / 2) - Complex.exp (L₃ ζ / 2))
      (Metric.ball ζ₀ ρ) :=
    ((hL₂diff.div_const 2).cexp).sub ((hL₃diff.div_const 2).cexp)
  have hGinv_all : ∀ ζ ∈ Metric.ball ζ₀ ρ,
      (Complex.exp (L₂ ζ / 2) - Complex.exp (L₃ ζ / 2))⁻¹
        = Complex.exp (L₂ ζ / 2) + Complex.exp (L₃ ζ / 2) := by
    intro ζ hζ
    apply mul_left_cancel₀ (hGne ζ hζ)
    rw [mul_inv_cancel₀ (hGne ζ hζ)]
    exact (hST ζ hζ).symm
  obtain ⟨H, hHdiff, hH0, hHexp⟩ := gp_exists_log ζ₀ ρ
    (fun ζ => Complex.exp (L₂ ζ / 2) - Complex.exp (L₃ ζ / 2)) hGdiff hGne
    (Complex.log (Complex.exp (L₂ ζ₀ / 2) - Complex.exp (L₃ ζ₀ / 2)))
    (Complex.exp_log (hGne ζ₀ hmem)) hmem
  have hcoshF : ∀ ζ ∈ Metric.ball ζ₀ ρ, Complex.cosh (H ζ) ^ 2
      = L₁ ζ / (2 * Real.pi * Complex.I) := by
    intro ζ hζ
    have hexpH : Complex.exp (H ζ)
        = Complex.exp (L₂ ζ / 2) - Complex.exp (L₃ ζ / 2) := hHexp ζ hζ
    have hexpneg : Complex.exp (-H ζ)
        = Complex.exp (L₂ ζ / 2) + Complex.exp (L₃ ζ / 2) := by
      have e1 : Complex.exp (-H ζ) = (Complex.exp (H ζ))⁻¹ := Complex.exp_neg _
      rw [e1, hexpH]
      exact hGinv_all ζ hζ
    have h2cosh : 2 * Complex.cosh (H ζ) = 2 * Complex.exp (L₂ ζ / 2) := by
      have htc := Complex.two_cosh (H ζ)
      rw [hexpH, hexpneg] at htc
      linear_combination htc
    have hcoshS : Complex.cosh (H ζ) = Complex.exp (L₂ ζ / 2) := by
      linear_combination h2cosh / 2
    rw [hcoshS]
    exact hS2 ζ hζ
  have hg0pos : 0 < ‖g ζ₀‖ := lt_of_lt_of_le (by norm_num) hlo
  have hlog1 : |Real.log ‖g ζ₀‖| ≤ 1 := by
    have h1 : Real.log ‖g ζ₀‖ ≤ 1 / 2 := by
      have hle := Real.log_le_sub_one_of_pos hg0pos
      linarith [hhi]
    have h2 : -1 ≤ Real.log ‖g ζ₀‖ := by
      have h3 := Real.one_sub_inv_le_log_of_pos hg0pos
      have h5 : (2 : ℝ)⁻¹ ≤ ‖g ζ₀‖ := by
        have e : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
        rw [e]
        linarith [hlo]
      have h6 : (‖g ζ₀‖)⁻¹ ≤ ((2 : ℝ)⁻¹)⁻¹ :=
        (inv_le_inv₀ hg0pos (show (0 : ℝ) < (2 : ℝ)⁻¹ by norm_num)).mpr h5
      rw [inv_inv] at h6
      linarith
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hL1c : ‖L₁ ζ₀‖ ≤ 1 + Real.pi := by
    have e : L₁ ζ₀ = Complex.log (g ζ₀) := hL₁0
    rw [e]
    have hle := Complex.norm_le_abs_re_add_abs_im (Complex.log (g ζ₀))
    rw [Complex.log_re, Complex.log_im] at hle
    have harg := Complex.abs_arg_le_pi (g ζ₀)
    linarith [hle, harg, hlog1]
  have hF0 : ‖L₁ ζ₀ / (2 * Real.pi * Complex.I)‖ ≤ 1 := by
    rw [norm_div, h2pi_norm, div_le_one h2pir]
    linarith [hL1c, Real.pi_gt_three]
  have hSn : ‖Complex.exp (L₂ ζ₀ / 2)‖ ^ 2 ≤ 1 := by
    have e : ‖Complex.exp (L₂ ζ₀ / 2)‖ ^ 2
        = ‖L₁ ζ₀ / (2 * Real.pi * Complex.I)‖ := by
      rw [← norm_pow, hS2 ζ₀ hmem]
    rw [e]
    exact hF0
  have hS0 : ‖Complex.exp (L₂ ζ₀ / 2)‖ ≤ 1 := by
    have hSq : ‖Complex.exp (L₂ ζ₀ / 2)‖ ^ 2 ≤ (1 : ℝ) ^ 2 := by
      rw [one_pow]
      exact hSn
    have h := abs_le_of_sq_le_sq hSq zero_le_one
    rwa [abs_of_nonneg (norm_nonneg _)] at h
  have hTn : ‖Complex.exp (L₃ ζ₀ / 2)‖ ^ 2 ≤ (2 : ℝ) ^ 2 := by
    have e : ‖Complex.exp (L₃ ζ₀ / 2)‖ ^ 2
        = ‖L₁ ζ₀ / (2 * Real.pi * Complex.I) - 1‖ := by
      rw [← norm_pow, hT2 ζ₀ hmem]
    have hle : ‖L₁ ζ₀ / (2 * Real.pi * Complex.I) - 1‖ ≤ 2 := by
      have hsub : ∀ x : ℂ, ‖x - 1‖ ≤ ‖x‖ + 1 := fun x => by
        simpa using norm_sub_le x 1
      calc ‖L₁ ζ₀ / (2 * ↑Real.pi * Complex.I) - 1‖ ≤ ‖L₁ ζ₀ / (2 * ↑Real.pi * Complex.I)‖ + 1 :=
            hsub _
        _ ≤ 1 + 1 := by linarith [hF0]
        _ = 2 := by norm_num
    rw [e]
    calc ‖L₁ ζ₀ / (2 * ↑Real.pi * Complex.I) - 1‖ ≤ 2 := hle
      _ ≤ 2 ^ 2 := by norm_num
  have hT0 : ‖Complex.exp (L₃ ζ₀ / 2)‖ ≤ 2 := by
    have h := abs_le_of_sq_le_sq hTn (by norm_num)
    rwa [abs_of_nonneg (norm_nonneg _)] at h
  have hG0 : ‖Complex.exp (L₂ ζ₀ / 2) - Complex.exp (L₃ ζ₀ / 2)‖ ≤ 3 := by
    calc ‖Complex.exp (L₂ ζ₀ / 2) - Complex.exp (L₃ ζ₀ / 2)‖
        ≤ ‖Complex.exp (L₂ ζ₀ / 2)‖ + ‖Complex.exp (L₃ ζ₀ / 2)‖ :=
          norm_sub_le _ _
      _ ≤ 1 + 2 := by linarith [hS0, hT0]
      _ = 3 := by norm_num
  have hGi0 : ‖(Complex.exp (L₂ ζ₀ / 2) - Complex.exp (L₃ ζ₀ / 2))⁻¹‖ ≤ 3 := by
    rw [hGinv_all ζ₀ hmem]
    calc ‖Complex.exp (L₂ ζ₀ / 2) + Complex.exp (L₃ ζ₀ / 2)‖
        ≤ ‖Complex.exp (L₂ ζ₀ / 2)‖ + ‖Complex.exp (L₃ ζ₀ / 2)‖ :=
          norm_add_le _ _
      _ ≤ 1 + 2 := by linarith [hS0, hT0]
      _ = 3 := by norm_num
  have hGpos : 0 < ‖Complex.exp (L₂ ζ₀ / 2) - Complex.exp (L₃ ζ₀ / 2)‖ :=
    norm_pos_iff.mpr (hGne ζ₀ hmem)
  have hGinv_le : (‖Complex.exp (L₂ ζ₀ / 2) - Complex.exp (L₃ ζ₀ / 2)‖)⁻¹ ≤ 3 := by
    rw [← norm_inv]
    exact hGi0
  have hGlb : 1 / 3 ≤ ‖Complex.exp (L₂ ζ₀ / 2) - Complex.exp (L₃ ζ₀ / 2)‖ := by
    have h1 : (1 : ℝ) ≤ ‖Complex.exp (L₂ ζ₀ / 2) - Complex.exp (L₃ ζ₀ / 2)‖ * 3 := by
      have h2 : (‖Complex.exp (L₂ ζ₀ / 2) - Complex.exp (L₃ ζ₀ / 2)‖)⁻¹
          * ‖Complex.exp (L₂ ζ₀ / 2) - Complex.exp (L₃ ζ₀ / 2)‖ = 1 :=
        inv_mul_cancel₀ (ne_of_gt hGpos)
      calc (1 : ℝ) = (‖Complex.exp (L₂ ζ₀ / 2) - Complex.exp (L₃ ζ₀ / 2)‖)⁻¹
            * ‖Complex.exp (L₂ ζ₀ / 2) - Complex.exp (L₃ ζ₀ / 2)‖ := h2.symm
        _ ≤ 3 * ‖Complex.exp (L₂ ζ₀ / 2) - Complex.exp (L₃ ζ₀ / 2)‖ :=
            mul_le_mul_of_nonneg_right hGinv_le hGpos.le
        _ = ‖Complex.exp (L₂ ζ₀ / 2) - Complex.exp (L₃ ζ₀ / 2)‖ * 3 := by ring
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
    exact h1
  have hlogG : |Real.log ‖Complex.exp (L₂ ζ₀ / 2) - Complex.exp (L₃ ζ₀ / 2)‖| ≤ 2 := by
    have h1 : Real.log ‖Complex.exp (L₂ ζ₀ / 2) - Complex.exp (L₃ ζ₀ / 2)‖ ≤ 2 := by
      have hle := Real.log_le_sub_one_of_pos hGpos
      linarith [hG0]
    have h2 : -2 ≤ Real.log ‖Complex.exp (L₂ ζ₀ / 2) - Complex.exp (L₃ ζ₀ / 2)‖ := by
      have h3 := Real.one_sub_inv_le_log_of_pos hGpos
      linarith [hGinv_le]
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hHc : ‖H ζ₀‖ ≤ 6 := by
    have e : H ζ₀
        = Complex.log (Complex.exp (L₂ ζ₀ / 2) - Complex.exp (L₃ ζ₀ / 2)) := hH0
    rw [e]
    have hle := Complex.norm_le_abs_re_add_abs_im
      (Complex.log (Complex.exp (L₂ ζ₀ / 2) - Complex.exp (L₃ ζ₀ / 2)))
    rw [Complex.log_re, Complex.log_im] at hle
    have harg := Complex.abs_arg_le_pi
      (Complex.exp (L₂ ζ₀ / 2) - Complex.exp (L₃ ζ₀ / 2))
    linarith [hle, harg, hlogG, Real.pi_lt_d2]
  have hcoshle : ∀ ζ ∈ Metric.ball ζ₀ ρ,
      ‖Complex.cosh (H ζ)‖ ≤ Real.exp ‖H ζ‖ := by
    intro ζ hζ
    have htc := Complex.two_cosh (H ζ)
    have e1 : ‖Complex.exp (H ζ)‖ ≤ Real.exp ‖H ζ‖ := by
      rw [Complex.norm_exp]
      exact Real.exp_le_exp.mpr (Complex.re_le_norm _)
    have e2 : ‖Complex.exp (-H ζ)‖ ≤ Real.exp ‖H ζ‖ := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      calc (-H ζ).re = -((H ζ).re) := Complex.neg_re _
        _ ≤ ‖H ζ‖ := (neg_le_abs _).trans (Complex.abs_re_le_norm _)
    have h2 : (2 : ℝ) * ‖Complex.cosh (H ζ)‖ ≤ 2 * Real.exp ‖H ζ‖ := by
      have tri := norm_add_le (Complex.exp (H ζ)) (Complex.exp (-H ζ))
      have htc2 : ‖(2 : ℂ) * Complex.cosh (H ζ)‖
          = 2 * ‖Complex.cosh (H ζ)‖ := by
        have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
        rw [norm_mul, h2n]
      rw [htc] at htc2
      linarith [tri, e1, e2, htc2]
    linarith
  have hcsq : ∀ ζ ∈ Metric.ball ζ₀ ρ,
      ‖Complex.cosh (H ζ)‖ ^ 2 ≤ Real.exp (2 * ‖H ζ‖) := by
    intro ζ hζ
    have h1 : ‖Complex.cosh (H ζ)‖ ^ 2 ≤ (Real.exp ‖H ζ‖) ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg (norm_nonneg _), abs_of_pos (Real.exp_pos _)]
      exact hcoshle ζ hζ
    have h2 : (Real.exp ‖H ζ‖) ^ 2 = Real.exp (2 * ‖H ζ‖) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [h2] at h1
    exact h1
  have hnormF : ∀ ζ ∈ Metric.ball ζ₀ ρ,
      ‖L₁ ζ / (2 * Real.pi * Complex.I)‖ = ‖Complex.cosh (H ζ)‖ ^ 2 := by
    intro ζ hζ
    rw [← hcoshF ζ hζ, norm_pow]
  have hL1norm : ∀ ζ ∈ Metric.ball ζ₀ ρ,
      ‖L₁ ζ‖ ≤ 2 * Real.pi * Real.exp (2 * ‖H ζ‖) := by
    intro ζ hζ
    have eF : L₁ ζ
        = 2 * Real.pi * Complex.I * (L₁ ζ / (2 * Real.pi * Complex.I)) := by
      rw [mul_div_cancel₀ _ h2pi]
    rw [eF, norm_mul, h2pi_norm, hnormF ζ hζ]
    exact mul_le_mul_of_nonneg_left (hcsq ζ hζ) h2pir.le
  refine ⟨H, hHdiff, hHc, ?_, ?_⟩
  · intro ζ hζ n hn
    rw [hcoshF ζ hζ] at hn
    have hFn := hFint ζ hζ (n : ℤ)
    rw [Int.cast_natCast] at hFn
    exact hFn hn
  · intro ζ hζ
    have hg1 : ‖g ζ‖ = Real.exp (L₁ ζ).re := by
      have h := hL₁exp ζ hζ
      rw [← h, Complex.norm_exp]
    calc ‖g ζ‖ = Real.exp (L₁ ζ).re := hg1
      _ ≤ Real.exp ‖L₁ ζ‖ := Real.exp_le_exp.mpr (Complex.re_le_norm _)
      _ ≤ Real.exp (2 * Real.pi * Real.exp (2 * ‖H ζ‖)) :=
          Real.exp_le_exp.mpr (hL1norm ζ hζ)

/-- Schottky estimate on half-discs via Bloch. -/
private theorem gp_schottky_core :
    ∃ M₀ : ℝ, ∀ g : ℂ → ℂ, ∀ ζ₀ : ℂ, ∀ ρ : ℝ, 0 < ρ →
      DifferentiableOn ℂ g (Metric.ball ζ₀ ρ) →
      (∀ ζ ∈ Metric.ball ζ₀ ρ, g ζ ≠ 0) →
      (∀ ζ ∈ Metric.ball ζ₀ ρ, g ζ ≠ 1) →
      1 / 2 ≤ ‖g ζ₀‖ → ‖g ζ₀‖ ≤ 3 / 2 →
      ∀ ζ ∈ Metric.closedBall ζ₀ (ρ / 2), ‖g ζ‖ ≤ M₀ := by
  obtain ⟨B, hB, hN4⟩ := gp_bloch_deriv_bound
  refine ⟨Real.exp (2 * Real.pi * Real.exp (2 * (6 + 6 / B))), ?_⟩
  intro g ζ₀ ρ hρ hg h0 h1 hlo hhi ζ hζ
  obtain ⟨H, hHdiff, hHb, hHc, hHd⟩ :=
    gp_schottky_aux g ζ₀ ρ hρ hg h0 h1 hlo hhi
  have hBne : B ≠ 0 := ne_of_gt hB
  have hρne : ρ ≠ 0 := ne_of_gt hρ
  have hno6 : ∀ p : ℂ, ¬ (Metric.ball p 6 ⊆ H '' Metric.ball ζ₀ ρ) := by
    intro p hsub
    obtain ⟨ω, n, hω6, hcosh⟩ := gp_cosh_sq_net p
    have hmemω : ω ∈ Metric.ball p 6 := by
      rw [Metric.mem_ball, dist_eq_norm]
      rwa [norm_sub_rev]
    obtain ⟨ζ', hζ'mem, hHζ'⟩ := hsub hmemω
    have hcon := hHc ζ' hζ'mem n
    rw [hHζ'] at hcon
    exact hcon hcosh
  have hderiv : ∀ z ∈ Metric.closedBall ζ₀ (ρ / 2),
      ‖deriv H z‖ ≤ 6 / (B * (ρ / 2)) := by
    intro z hzmem
    have hballsub : Metric.ball z (ρ / 2) ⊆ Metric.ball ζ₀ ρ := by
      intro w hw
      rw [Metric.mem_ball, dist_eq_norm] at hw ⊢
      have hz : ‖z - ζ₀‖ ≤ ρ / 2 := by
        have h := Metric.mem_closedBall.mp hzmem
        rwa [dist_eq_norm] at h
      calc ‖w - ζ₀‖ ≤ ‖w - z‖ + ‖z - ζ₀‖ := by
            have htri := norm_add_le (w - z) (z - ζ₀)
            rwa [sub_add_sub_cancel] at htri
        _ < ρ / 2 + ρ / 2 := by linarith [hw, hz]
        _ = ρ := by ring
    have hno : ∀ p : ℂ, ¬ (Metric.ball p 6 ⊆ H '' Metric.ball z (ρ / 2)) := by
      intro p hsub
      apply hno6 p
      exact hsub.trans (Set.image_mono hballsub)
    exact hN4 H z (ρ / 2) 6 (by linarith [hρ]) (hHdiff.mono hballsub) hno
  have hconv : Convex ℝ (Metric.closedBall ζ₀ (ρ / 2)) := convex_closedBall _ _
  have hclosedsub : Metric.closedBall ζ₀ (ρ / 2) ⊆ Metric.ball ζ₀ ρ :=
    Metric.closedBall_subset_ball (by linarith [hρ] : ρ / 2 < ρ)
  have hdiff_at : ∀ x ∈ Metric.closedBall ζ₀ (ρ / 2), DifferentiableAt ℂ H x := by
    intro x hx
    exact hHdiff.differentiableAt (Metric.isOpen_ball.mem_nhds (hclosedsub hx))
  have hζ₀mem : ζ₀ ∈ Metric.closedBall ζ₀ (ρ / 2) :=
    Metric.mem_closedBall_self (by linarith [hρ] : (0 : ℝ) ≤ ρ / 2)
  have hCeq : (6 / (B * (ρ / 2))) * (ρ / 2) = 6 / B := by
    have hρ2ne : (ρ / 2 : ℝ) ≠ 0 := div_ne_zero hρne (by norm_num)
    field_simp
  have hmv : ∀ w ∈ Metric.closedBall ζ₀ (ρ / 2), ‖H w - H ζ₀‖ ≤ 6 / B := by
    intro w hw
    have hle := Convex.norm_image_sub_le_of_norm_deriv_le hdiff_at hderiv hconv
      hζ₀mem hw
    have hnorm : ‖w - ζ₀‖ ≤ ρ / 2 := by
      have h := Metric.mem_closedBall.mp hw
      rwa [dist_eq_norm] at h
    have hCnn : (0 : ℝ) ≤ 6 / (B * (ρ / 2)) :=
      div_nonneg (by norm_num) (mul_nonneg hB.le (by linarith [hρ]))
    calc ‖H w - H ζ₀‖ ≤ (6 / (B * (ρ / 2))) * ‖w - ζ₀‖ := hle
      _ ≤ (6 / (B * (ρ / 2))) * (ρ / 2) :=
          mul_le_mul_of_nonneg_left hnorm hCnn
      _ = 6 / B := hCeq
  have hHζ : ‖H ζ‖ ≤ 6 + 6 / B := by
    have h1 : ‖H ζ‖ - ‖H ζ₀‖ ≤ ‖H ζ - H ζ₀‖ := norm_sub_norm_le _ _
    linarith [h1, hmv ζ hζ, hHb]
  have h2pir : (0 : ℝ) ≤ 2 * Real.pi :=
    (mul_pos (by norm_num) Real.pi_pos).le
  have hgd : ‖g ζ‖ ≤ Real.exp (2 * Real.pi * Real.exp (2 * ‖H ζ‖)) :=
    hHd ζ (hclosedsub hζ)
  calc ‖g ζ‖ ≤ Real.exp (2 * Real.pi * Real.exp (2 * ‖H ζ‖)) := hgd
    _ ≤ Real.exp (2 * Real.pi * Real.exp (2 * (6 + 6 / B))) := by
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_left _ h2pir
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_left hHζ (by norm_num)

/-- Full Schottky bound for `‖g ζ₀‖ ≤ 1` via the `1 - g` trick. -/
private theorem gp_schottky :
    ∃ M : ℝ, ∀ g : ℂ → ℂ, ∀ ζ₀ : ℂ, ∀ ρ : ℝ, 0 < ρ →
      DifferentiableOn ℂ g (Metric.ball ζ₀ ρ) →
      (∀ ζ ∈ Metric.ball ζ₀ ρ, g ζ ≠ 0) →
      (∀ ζ ∈ Metric.ball ζ₀ ρ, g ζ ≠ 1) →
      ‖g ζ₀‖ ≤ 1 →
      ∀ ζ ∈ Metric.closedBall ζ₀ (ρ / 2), ‖g ζ‖ ≤ M := by
  obtain ⟨M₀, hN6⟩ := gp_schottky_core
  refine ⟨1 + M₀, ?_⟩
  intro g ζ₀ ρ hρ hg h0 h1 hcen ζ hζ
  by_cases hcase : 1 / 2 ≤ ‖g ζ₀‖
  · have h := hN6 g ζ₀ ρ hρ hg h0 h1 hcase (by linarith [hcen]) ζ hζ
    linarith
  · have hlt : ‖g ζ₀‖ < 1 / 2 := lt_of_not_ge hcase
    have h1g : DifferentiableOn ℂ (fun ζ => 1 - g ζ) (Metric.ball ζ₀ ρ) :=
      hg.const_sub 1
    have h1g0 : ∀ ζ ∈ Metric.ball ζ₀ ρ, (1 : ℂ) - g ζ ≠ 0 := by
      intro ζ hζ hg1
      apply h1 ζ hζ
      linear_combination -hg1
    have h1g1 : ∀ ζ ∈ Metric.ball ζ₀ ρ, (1 : ℂ) - g ζ ≠ 1 := by
      intro ζ hζ hg1
      apply h0 ζ hζ
      linear_combination -hg1
    have hlo : 1 / 2 ≤ ‖(1 : ℂ) - g ζ₀‖ := by
      have htri := norm_sub_norm_le (1 : ℂ) (g ζ₀)
      rw [norm_one] at htri
      linarith [hlt, htri]
    have hhi : ‖(1 : ℂ) - g ζ₀‖ ≤ 3 / 2 := by
      have htri := norm_sub_le (1 : ℂ) (g ζ₀)
      rw [norm_one] at htri
      have hnn : 0 ≤ ‖g ζ₀‖ := norm_nonneg _
      linarith [hlt, htri, hnn]
    have hle : ‖(1 : ℂ) - g ζ‖ ≤ M₀ :=
      hN6 _ _ _ hρ h1g h1g0 h1g1 hlo hhi ζ hζ
    calc ‖g ζ‖ = ‖(1 : ℂ) - (1 - g ζ)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖(1 : ℂ)‖ + ‖(1 : ℂ) - g ζ‖ := norm_sub_le _ _
      _ ≤ 1 + M₀ := by rw [norm_one]; linarith [hle]

/-- Uniform bound on circles via the exponential map and Schottky. -/
private theorem gp_circle_bound (f : ℂ → ℂ) (c : ℂ) (R : ℝ)
    (hf : DifferentiableOn ℂ f (Metric.ball c R \ {c}))
    (h0 : ∀ z ∈ Metric.ball c R \ {c}, f z ≠ 0)
    (h1 : ∀ z ∈ Metric.ball c R \ {c}, f z ≠ 1) :
    ∃ M : ℝ, ∀ z₁ z : ℂ, z₁ ≠ c → ‖z₁ - c‖ * Real.exp 16 ≤ R →
      ‖f z₁‖ ≤ 1 → ‖z - c‖ = ‖z₁ - c‖ → ‖f z‖ ≤ M := by
  obtain ⟨M, hN7⟩ := gp_schottky
  refine ⟨M, ?_⟩
  intro z₁ z hz₁ hR1 hfz₁ hrr
  set r : ℝ := ‖z₁ - c‖ with hr
  set ζ₁ : ℂ := Complex.log (z₁ - c) with hζ₁
  have hrpos : 0 < r := by
    rw [hr, norm_pos_iff]
    exact sub_ne_zero.mpr hz₁
  have hz₁c : z₁ - c ≠ 0 := sub_ne_zero.mpr hz₁
  have hζ₁re : ζ₁.re = Real.log r := by
    rw [hζ₁, Complex.log_re, ← hr]
  have hmaps : Set.MapsTo (fun ζ => c + Complex.exp ζ)
      (Metric.ball ζ₁ 16) (Metric.ball c R \ {c}) := by
    intro ζ hζ
    have hζmem : ‖ζ - ζ₁‖ < 16 := by
      have h := Metric.mem_ball.mp hζ
      rwa [dist_eq_norm] at h
    have hre : ζ.re < Real.log r + 16 := by
      have h1r : (ζ - ζ₁).re ≤ ‖ζ - ζ₁‖ := Complex.re_le_norm _
      have h2r : (ζ - ζ₁).re = ζ.re - Real.log r := by
        rw [Complex.sub_re, hζ₁re]
      linarith [hζmem, h1r, h2r]
    have hexp_norm : ‖Complex.exp ζ‖ < R := by
      have e1 : ‖Complex.exp ζ‖ = Real.exp ζ.re := Complex.norm_exp _
      have e2 : Real.exp ζ.re < r * Real.exp 16 := by
        have e3 : r * Real.exp 16 = Real.exp (Real.log r + 16) := by
          rw [Real.exp_add, Real.exp_log hrpos]
        rw [e3]
        exact Real.exp_lt_exp.mpr (by linarith [hre])
      linarith [hR1, e1, e2]
    have hexp_ne : Complex.exp ζ ≠ 0 := Complex.exp_ne_zero _
    constructor
    · rw [Metric.mem_ball, dist_eq_norm]
      have e : c + Complex.exp ζ - c = Complex.exp ζ := by ring
      rw [e]
      exact hexp_norm
    · rw [Set.mem_singleton_iff]
      intro hcon
      apply hexp_ne
      linear_combination hcon
  have hinner : DifferentiableOn ℂ (fun ζ => c + Complex.exp ζ)
      (Metric.ball ζ₁ 16) :=
    (differentiableOn_const _).add differentiableOn_id.cexp
  have hgdiff : DifferentiableOn ℂ (fun ζ => f (c + Complex.exp ζ))
      (Metric.ball ζ₁ 16) :=
    hf.comp hinner hmaps
  have hg0 : ∀ ζ ∈ Metric.ball ζ₁ 16, f (c + Complex.exp ζ) ≠ 0 :=
    fun ζ hζ => h0 _ (hmaps hζ)
  have hg1 : ∀ ζ ∈ Metric.ball ζ₁ 16, f (c + Complex.exp ζ) ≠ 1 :=
    fun ζ hζ => h1 _ (hmaps hζ)
  have hgζ₁ : f (c + Complex.exp ζ₁) = f z₁ := by
    rw [hζ₁, Complex.exp_log hz₁c, add_sub_cancel]
  have hcen : ‖f (c + Complex.exp ζ₁)‖ ≤ 1 := by
    rw [hgζ₁]
    exact hfz₁
  have hM := hN7 (fun ζ => f (c + Complex.exp ζ)) ζ₁ 16 (by norm_num) hgdiff
    hg0 hg1 hcen
  have hzpos : z ≠ c := by
    intro hcon
    rw [hcon, sub_self, norm_zero] at hrr
    linarith [hrpos]
  set ζ : ℂ := Complex.log (z - c) with hζ
  have hζre : ζ.re = Real.log r := by
    rw [hζ, Complex.log_re, hrr]
  have hζim : ζ.im = Complex.arg (z - c) := by rw [hζ, Complex.log_im]
  have hζ₁im : ζ₁.im = Complex.arg (z₁ - c) := by rw [hζ₁, Complex.log_im]
  have him : |(ζ - ζ₁).im| ≤ 2 * Real.pi := by
    have e : (ζ - ζ₁).im = Complex.arg (z - c) - Complex.arg (z₁ - c) := by
      rw [Complex.sub_im, hζim, hζ₁im]
    rw [e]
    have h1 := Complex.abs_arg_le_pi (z - c)
    have h2 := Complex.abs_arg_le_pi (z₁ - c)
    calc |Complex.arg (z - c) - Complex.arg (z₁ - c)|
        = |Complex.arg (z - c) + -(Complex.arg (z₁ - c))| := by
          rw [sub_eq_add_neg]
      _ ≤ |Complex.arg (z - c)| + |-(Complex.arg (z₁ - c))| := abs_add_le _ _
      _ = |Complex.arg (z - c)| + |Complex.arg (z₁ - c)| := by rw [abs_neg]
      _ ≤ Real.pi + Real.pi := add_le_add h1 h2
      _ = 2 * Real.pi := by ring
  have hre0 : (ζ - ζ₁).re = 0 := by
    rw [Complex.sub_re, hζre, hζ₁re, sub_self]
  have hζmem : ζ ∈ Metric.closedBall ζ₁ (16 / 2) := by
    have h8 : (16 : ℝ) / 2 = 8 := by norm_num
    rw [Metric.mem_closedBall, dist_eq_norm, h8]
    calc ‖ζ - ζ₁‖ ≤ |(ζ - ζ₁).re| + |(ζ - ζ₁).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 0 + 2 * Real.pi := by
          rw [hre0, abs_zero]
          linarith [him]
      _ ≤ 8 := by linarith [Real.pi_lt_d2]
  have hMζ : ‖f (c + Complex.exp ζ)‖ ≤ M := hM ζ hζmem
  have heq : c + Complex.exp ζ = z := by
    rw [hζ, Complex.exp_log (sub_ne_zero.mpr hzpos)]
    ring
  rw [heq] at hMζ
  exact hMζ

/-- Maximum modulus on an annulus from bounds on the two circles. -/
private theorem gp_annulus_max (f : ℂ → ℂ) (c : ℂ) (R r₁ r₂ M : ℝ)
    (hf : DifferentiableOn ℂ f (Metric.ball c R \ {c}))
    (h01 : 0 < r₁) (h2R : r₂ < R)
    (hlo : ∀ z : ℂ, ‖z - c‖ = r₁ → ‖f z‖ ≤ M)
    (hhi : ∀ z : ℂ, ‖z - c‖ = r₂ → ‖f z‖ ≤ M) :
    ∀ z : ℂ, r₁ ≤ ‖z - c‖ → ‖z - c‖ ≤ r₂ → ‖f z‖ ≤ M := by
  have hcont : Continuous fun z : ℂ => ‖z - c‖ := by fun_prop
  have hUopen : IsOpen {z : ℂ | r₁ < ‖z - c‖ ∧ ‖z - c‖ < r₂} := by
    have h1 : IsOpen {z : ℂ | r₁ < ‖z - c‖} := isOpen_lt continuous_const hcont
    have h2 : IsOpen {z : ℂ | ‖z - c‖ < r₂} := isOpen_lt hcont continuous_const
    have e : {z : ℂ | r₁ < ‖z - c‖ ∧ ‖z - c‖ < r₂}
        = {z : ℂ | r₁ < ‖z - c‖} ∩ {z : ℂ | ‖z - c‖ < r₂} := rfl
    rw [e]
    exact h1.inter h2
  have hKclosed : IsClosed {z : ℂ | r₁ ≤ ‖z - c‖ ∧ ‖z - c‖ ≤ r₂} := by
    have h1 : IsClosed {z : ℂ | r₁ ≤ ‖z - c‖} := isClosed_le continuous_const hcont
    have h2 : IsClosed {z : ℂ | ‖z - c‖ ≤ r₂} := isClosed_le hcont continuous_const
    have e : {z : ℂ | r₁ ≤ ‖z - c‖ ∧ ‖z - c‖ ≤ r₂}
        = {z : ℂ | r₁ ≤ ‖z - c‖} ∩ {z : ℂ | ‖z - c‖ ≤ r₂} := rfl
    rw [e]
    exact h1.inter h2
  have hUK : closure {z : ℂ | r₁ < ‖z - c‖ ∧ ‖z - c‖ < r₂}
      ⊆ {z : ℂ | r₁ ≤ ‖z - c‖ ∧ ‖z - c‖ ≤ r₂} := by
    apply closure_minimal _ hKclosed
    intro z hz
    exact ⟨le_of_lt hz.1, le_of_lt hz.2⟩
  have hKsub : {z : ℂ | r₁ ≤ ‖z - c‖ ∧ ‖z - c‖ ≤ r₂}
      ⊆ Metric.ball c R \ {c} := by
    intro z hz
    constructor
    · rw [Metric.mem_ball, dist_eq_norm]
      linarith [hz.2, h2R]
    · rw [Set.mem_singleton_iff]
      intro hcon
      rw [hcon] at hz
      have h1 : r₁ ≤ ‖c - c‖ := hz.1
      rw [sub_self, norm_zero] at h1
      linarith [h1, h01]
  have hfdiff : DifferentiableOn ℂ f
      (closure {z : ℂ | r₁ < ‖z - c‖ ∧ ‖z - c‖ < r₂}) :=
    hf.mono (hUK.trans hKsub)
  have hdiffCl : DiffContOnCl ℂ f {z : ℂ | r₁ < ‖z - c‖ ∧ ‖z - c‖ < r₂} :=
    hfdiff.diffContOnCl
  have hbound : Bornology.IsBounded {z : ℂ | r₁ < ‖z - c‖ ∧ ‖z - c‖ < r₂} :=
    Metric.isBounded_ball.subset (fun z hz => by
      rw [Metric.mem_ball, dist_eq_norm]
      linarith [hz.2, h2R])
  have hfront : ∀ w ∈ frontier {z : ℂ | r₁ < ‖z - c‖ ∧ ‖z - c‖ < r₂},
      ‖f w‖ ≤ M := by
    intro w hw
    rw [hUopen.frontier_eq] at hw
    obtain ⟨hwK, hwU⟩ := hw
    have hwK' := hUK hwK
    have hwU' : r₁ < ‖w - c‖ → ¬ ‖w - c‖ < r₂ := fun h h2 => hwU ⟨h, h2⟩
    by_cases h : r₁ < ‖w - c‖
    · have h2 : ‖w - c‖ = r₂ := le_antisymm hwK'.2 (le_of_not_gt (hwU' h))
      exact hhi w h2
    · have h2 : ‖w - c‖ = r₁ := le_antisymm (le_of_not_gt h) hwK'.1
      exact hlo w h2
  intro z hz1 hz2
  by_cases hzU : z ∈ {z : ℂ | r₁ < ‖z - c‖ ∧ ‖z - c‖ < r₂}
  · exact Complex.norm_le_of_forall_mem_frontier_norm_le hbound hdiffCl hfront
      (subset_closure hzU)
  · have hzU' : r₁ < ‖z - c‖ → ¬ ‖z - c‖ < r₂ := fun h h2 => hzU ⟨h, h2⟩
    by_cases h : r₁ < ‖z - c‖
    · have h2 : ‖z - c‖ = r₂ := le_antisymm hz2 (le_of_not_gt (hzU' h))
      exact hhi z h2
    · have h2 : ‖z - c‖ = r₁ := le_antisymm (le_of_not_gt h) hz1
      exact hlo z h2

/-- Bounded case: frequent `‖f‖ ≤ 1` gives a finite limit. -/
private theorem gp_bounded_case (f : ℂ → ℂ) (c : ℂ) (R : ℝ)
    (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.ball c R \ {c}))
    (h0 : ∀ z ∈ Metric.ball c R \ {c}, f z ≠ 0)
    (h1 : ∀ z ∈ Metric.ball c R \ {c}, f z ≠ 1)
    (hfreq : ∃ᶠ z in 𝓝[≠] c, ‖f z‖ ≤ 1) :
    ∃ l : ℂ, Tendsto f (𝓝[≠] c) (𝓝 l) := by
  obtain ⟨M, hN8⟩ := gp_circle_bound f c R hf h0 h1
  have hexp16 : (0 : ℝ) < Real.exp 16 := Real.exp_pos _
  have hpick : ∀ s : ℝ, 0 < s → ∃ z' : ℂ, z' ≠ c ∧ ‖z' - c‖ < s ∧ ‖f z'‖ ≤ 1 := by
    intro s hs
    have hmem : Metric.ball c s \ {c} ∈ 𝓝[≠] c :=
      sdiff_mem_nhdsWithin_compl (Metric.ball_mem_nhds c hs) {c}
    obtain ⟨z', h1f, h2f⟩ := (hfreq.and_eventually hmem).exists
    obtain ⟨hmem_ball, hne⟩ := h2f
    have hne' : z' ≠ c := fun hcon => hne (Set.mem_singleton_iff.mpr hcon)
    have hnorm : ‖z' - c‖ < s := by
      have h := Metric.mem_ball.mp hmem_ball
      rwa [dist_eq_norm] at h
    exact ⟨z', hne', hnorm, h1f⟩
  have hε : 0 < R / Real.exp 16 := div_pos hR hexp16
  obtain ⟨z₁, hz₁ne, hz₁r, hfz₁⟩ := hpick (R / Real.exp 16) hε
  have hr₁pos : 0 < ‖z₁ - c‖ := by
    rw [norm_pos_iff]
    exact sub_ne_zero.mpr hz₁ne
  have hr₁R : ‖z₁ - c‖ * Real.exp 16 < R :=
    (lt_div_iff₀ hexp16).mp hz₁r
  have hcirc₁ : ∀ z : ℂ, ‖z - c‖ = ‖z₁ - c‖ → ‖f z‖ ≤ M :=
    fun z hz => hN8 z₁ z hz₁ne (le_of_lt hr₁R) hfz₁ hz
  have h1exp : (1 : ℝ) ≤ Real.exp 16 := by
    have h := Real.add_one_le_exp 16
    linarith
  have hεR : R / Real.exp 16 ≤ R := by
    have h2 : R * 1 ≤ R * Real.exp 16 := mul_le_mul_of_nonneg_left h1exp hR.le
    rw [mul_one] at h2
    rwa [div_le_iff₀ hexp16]
  have hball : ∀ z ∈ Metric.ball c ‖z₁ - c‖ \ {c}, ‖f z‖ ≤ M := by
    intro z hz
    obtain ⟨hzball, hzne⟩ := hz
    have hznorm : ‖z - c‖ < ‖z₁ - c‖ := by
      have h := Metric.mem_ball.mp hzball
      rwa [dist_eq_norm] at h
    have hzpos : 0 < ‖z - c‖ := by
      rw [norm_pos_iff]
      exact sub_ne_zero.mpr
        (fun hcon => hzne (Set.mem_singleton_iff.mpr hcon))
    obtain ⟨z₂, hz₂ne, hz₂r, hfz₂⟩ := hpick ‖z - c‖ hzpos
    have hr₂lt : ‖z₂ - c‖ < R / Real.exp 16 :=
      lt_trans hz₂r (lt_trans hznorm hz₁r)
    have hr₂R : ‖z₂ - c‖ * Real.exp 16 ≤ R :=
      le_of_lt ((lt_div_iff₀ hexp16).mp hr₂lt)
    have hcirc₂ : ∀ w : ℂ, ‖w - c‖ = ‖z₂ - c‖ → ‖f w‖ ≤ M :=
      fun w hw => hN8 z₂ w hz₂ne hr₂R hfz₂ hw
    have hr₂pos : 0 < ‖z₂ - c‖ := by
      rw [norm_pos_iff]
      exact sub_ne_zero.mpr hz₂ne
    have hr₂R' : ‖z₂ - c‖ < R := lt_of_lt_of_le hr₂lt hεR
    have hr₁R' : ‖z₁ - c‖ < R := lt_of_lt_of_le hz₁r hεR
    exact gp_annulus_max f c R ‖z₂ - c‖ ‖z₁ - c‖ M hf hr₂pos hr₁R'
      hcirc₂ hcirc₁ z (le_of_lt hz₂r) (le_of_lt hznorm)
  have hmemR : Metric.ball c R \ {c} ∈ 𝓝[≠] c :=
    sdiff_mem_nhdsWithin_compl (Metric.ball_mem_nhds c hR) {c}
  have hopenR : IsOpen (Metric.ball c R \ {c}) :=
    Metric.isOpen_ball.sdiff isClosed_singleton
  have hdiff_ev : ∀ᶠ z in 𝓝[≠] c, DifferentiableAt ℂ f z := by
    filter_upwards [hmemR] with z hz
    exact hf.differentiableAt (hopenR.mem_nhds hz)
  have hmemr₁ : Metric.ball c ‖z₁ - c‖ \ {c} ∈ 𝓝[≠] c :=
    sdiff_mem_nhdsWithin_compl (Metric.ball_mem_nhds c hr₁pos) {c}
  have hbdd : IsBoundedUnder (· ≤ ·) (𝓝[≠] c) fun z => ‖f z - f c‖ := by
    apply Filter.isBoundedUnder_of_eventually_le (a := M + ‖f c‖)
    filter_upwards [hmemr₁] with z hz
    have hle := hball z hz
    calc ‖f z - f c‖ ≤ ‖f z‖ + ‖f c‖ := norm_sub_le _ _
      _ ≤ M + ‖f c‖ := by linarith [hle]
  exact ⟨_, Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under
    hdiff_ev hbdd⟩
/-- Large case: eventually `1 < ‖f‖` gives a limit or a pole. -/
private theorem gp_large_case (f : ℂ → ℂ) (c : ℂ) (R : ℝ)
    (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.ball c R \ {c}))
    (hlarge : ∀ᶠ z in 𝓝[≠] c, 1 < ‖f z‖) :
    (∃ l : ℂ, Tendsto f (𝓝[≠] c) (𝓝 l)) ∨
      Tendsto (fun z => ‖f z‖) (𝓝[≠] c) atTop := by
  have hmemR : Metric.ball c R \ {c} ∈ 𝓝[≠] c :=
    sdiff_mem_nhdsWithin_compl (Metric.ball_mem_nhds c hR) {c}
  have hopenR : IsOpen (Metric.ball c R \ {c}) :=
    Metric.isOpen_ball.sdiff isClosed_singleton
  have hdiff_f : ∀ᶠ z in 𝓝[≠] c, DifferentiableAt ℂ f z := by
    filter_upwards [hmemR] with z hz
    exact hf.differentiableAt (hopenR.mem_nhds hz)
  have hne : ∀ᶠ z in 𝓝[≠] c, f z ≠ 0 := by
    filter_upwards [hlarge] with z hz hcon
    rw [hcon, norm_zero] at hz
    linarith
  have hdiff_h : ∀ᶠ z in 𝓝[≠] c, DifferentiableAt ℂ (fun z => (f z)⁻¹) z := by
    filter_upwards [hdiff_f, hne] with z hdf hfz
    exact hdf.inv hfz
  have hbdd_h : ∀ᶠ z in 𝓝[≠] c, ‖(f z)⁻¹‖ ≤ 1 := by
    filter_upwards [hlarge] with z hz
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ hz.le
  have hbdd : IsBoundedUnder (· ≤ ·) (𝓝[≠] c)
      fun z => ‖(f z)⁻¹ - (f c)⁻¹‖ := by
    apply Filter.isBoundedUnder_of_eventually_le (a := 1 + ‖(f c)⁻¹‖)
    filter_upwards [hbdd_h] with z hz
    calc ‖(f z)⁻¹ - (f c)⁻¹‖ ≤ ‖(f z)⁻¹‖ + ‖(f c)⁻¹‖ := norm_sub_le _ _
      _ ≤ 1 + ‖(f c)⁻¹‖ := by linarith
  have hlim : Tendsto (fun z => (f z)⁻¹) (𝓝[≠] c)
      (𝓝 (limUnder (𝓝[≠] c) fun z => (f z)⁻¹)) :=
    Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under
      hdiff_h hbdd
  by_cases hL0 : limUnder (𝓝[≠] c) (fun z => (f z)⁻¹) = 0
  · right
    rw [hL0] at hlim
    have hnorm : Tendsto (fun z => ‖(f z)⁻¹‖) (𝓝[≠] c) (𝓝 0) := by
      have h2 := hlim.norm
      rwa [norm_zero] at h2
    have hpos : ∀ᶠ z in 𝓝[≠] c, 0 < ‖(f z)⁻¹‖ := by
      filter_upwards [hne] with z hfz
      rw [norm_pos_iff]
      exact inv_ne_zero hfz
    have hwithin : Tendsto (fun z => ‖(f z)⁻¹‖) (𝓝[≠] c) (𝓝[>] 0) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨hnorm, hpos⟩
    have hinv : Tendsto (fun z => (‖(f z)⁻¹‖)⁻¹) (𝓝[≠] c) atTop :=
      tendsto_inv_nhdsGT_zero.comp hwithin
    have heq : (fun z => (‖(f z)⁻¹‖)⁻¹) = (fun z => ‖f z‖) := by
      funext z
      rw [norm_inv, inv_inv]
    rwa [heq] at hinv
  · left
    have hinv := hlim.inv₀ hL0
    have heq : (fun z => ((f z)⁻¹)⁻¹) = f := by
      funext z
      rw [inv_inv]
    rw [heq] at hinv
    exact ⟨_, hinv⟩

/-- Omitting two values forces a finite limit or a pole. -/
private theorem gp_omit_two (f : ℂ → ℂ) (c a b : ℂ) (R : ℝ)
    (hR : 0 < R) (hab : a ≠ b)
    (hf : DifferentiableOn ℂ f (Metric.ball c R \ {c}))
    (ha : ∀ z ∈ Metric.ball c R \ {c}, f z ≠ a)
    (hb : ∀ z ∈ Metric.ball c R \ {c}, f z ≠ b) :
    (∃ l : ℂ, Tendsto f (𝓝[≠] c) (𝓝 l)) ∨
      Tendsto (fun z => ‖f z‖) (𝓝[≠] c) atTop := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  set g : ℂ → ℂ := fun z => (f z - a) / (b - a) with hg
  have hgdiff : DifferentiableOn ℂ g (Metric.ball c R \ {c}) :=
    (hf.sub_const a).div_const (b - a)
  have hg0 : ∀ z ∈ Metric.ball c R \ {c}, g z ≠ 0 := by
    intro z hz hcon
    simp only [hg] at hcon
    rw [div_eq_zero_iff] at hcon
    rcases hcon with h | h
    · exact ha z hz (sub_eq_zero.mp h)
    · exact hba h
  have hg1 : ∀ z ∈ Metric.ball c R \ {c}, g z ≠ 1 := by
    intro z hz hcon
    simp only [hg] at hcon
    have h2 : f z - a = b - a := by
      rw [div_eq_iff hba] at hcon
      rwa [one_mul] at hcon
    have hfb : f z = b := by
      calc f z = (f z - a) + a := by ring
        _ = (b - a) + a := by rw [h2]
        _ = b := by ring
    exact hb z hz hfb
  have hfg : ∀ z, f z = a + (b - a) * g z := by
    intro z
    have hba' : b - a ≠ 0 := hba
    simp only [hg]
    field_simp
    ring
  have htrans_lim : ∀ l : ℂ, Tendsto g (𝓝[≠] c) (𝓝 l) →
      ∃ l' : ℂ, Tendsto f (𝓝[≠] c) (𝓝 l') := by
    intro l hl
    refine ⟨a + (b - a) * l, ?_⟩
    have h2 := (hl.const_mul (b - a)).const_add a
    have heq : (fun z => a + (b - a) * g z) = f := by
      funext z
      exact (hfg z).symm
    rwa [heq] at h2
  have htrans_top : Tendsto (fun z => ‖g z‖) (𝓝[≠] c) atTop →
      Tendsto (fun z => ‖f z‖) (𝓝[≠] c) atTop := by
    intro hgT
    have hbound : ∀ z : ℂ, ‖b - a‖ * ‖g z‖ - ‖a‖ ≤ ‖f z‖ := by
      intro z
      have h2 := norm_sub_norm_le ((b - a) * g z) (-a)
      rw [norm_neg] at h2
      have heq : (b - a) * g z - -a = a + (b - a) * g z := by ring
      rw [heq, norm_mul] at h2
      rw [hfg z]
      exact h2
    have hpos : 0 < ‖b - a‖ := norm_pos_iff.mpr hba
    have hmul : Tendsto (fun z => ‖b - a‖ * ‖g z‖) (𝓝[≠] c) atTop :=
      Filter.Tendsto.const_mul_atTop hpos hgT
    have hadd : Tendsto (fun z => ‖b - a‖ * ‖g z‖ - ‖a‖) (𝓝[≠] c) atTop := by
      have h2 := Filter.tendsto_atTop_add_const_right (𝓝[≠] c) (-‖a‖) hmul
      have heq : (fun z => ‖b - a‖ * ‖g z‖ + -‖a‖)
          = (fun z => ‖b - a‖ * ‖g z‖ - ‖a‖) := by
        funext z
        ring
      rwa [heq] at h2
    have hle : (fun z => ‖b - a‖ * ‖g z‖ - ‖a‖) ≤ᶠ[𝓝[≠] c] (fun z => ‖f z‖) :=
      Filter.Eventually.of_forall hbound
    exact Filter.tendsto_atTop_mono' (𝓝[≠] c) hle hadd
  by_cases hfreq : ∃ᶠ z in 𝓝[≠] c, ‖g z‖ ≤ 1
  · obtain ⟨l, hl⟩ := gp_bounded_case g c R hR hgdiff hg0 hg1 hfreq
    exact Or.inl (htrans_lim l hl)
  · rw [Filter.not_frequently] at hfreq
    have hlarge : ∀ᶠ z in 𝓝[≠] c, 1 < ‖g z‖ := by
      filter_upwards [hfreq] with z hz
      exact lt_of_not_ge hz
    rcases gp_large_case g c R hR hgdiff hlarge with ⟨l, hl⟩ | htop
    · exact Or.inl (htrans_lim l hl)
    · exact Or.inr (htrans_top htop)

/-- A finite fibre is omitted on a smaller punctured ball. -/
private theorem gp_eventually_omit (f : ℂ → ℂ) (c w : ℂ) (r : ℝ)
    (hr : 0 < r) (hfin : Set.Finite {z ∈ Metric.ball c r \ {c} | f z = w}) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z ∈ Metric.ball c ρ \ {c}, f z ≠ w := by
  have hcS : c ∉ {z ∈ Metric.ball c r \ {c} | f z = w} := by
    rintro ⟨⟨_, hcne⟩, _⟩
    exact hcne (Set.mem_singleton c)
  have hclosed : IsClosed {z ∈ Metric.ball c r \ {c} | f z = w} := hfin.isClosed
  have hopen : IsOpen {z ∈ Metric.ball c r \ {c} | f z = w}ᶜ := hclosed.isOpen_compl
  rw [Metric.isOpen_iff] at hopen
  obtain ⟨ε, hεpos, hεsub⟩ := hopen c hcS
  refine ⟨min r ε, lt_min hr hεpos, fun z hz hcon => ?_⟩
  obtain ⟨hzball, hzne⟩ := hz
  have hzS : z ∈ {z ∈ Metric.ball c r \ {c} | f z = w} :=
    ⟨⟨Metric.ball_subset_ball (min_le_left _ _) hzball, hzne⟩, hcon⟩
  have hzC : z ∈ {z ∈ Metric.ball c r \ {c} | f z = w}ᶜ :=
    hεsub (Metric.ball_subset_ball (min_le_right _ _) hzball)
  exact hzC hzS

/--
**Great Picard theorem.** Suppose $f : \mathbb{C} \to \mathbb{C}$ has an essential isolated
singularity at $c \in \mathbb{C}$. Then there is at most one $w \in \mathbb{C}$ for which some
$r > 0$ makes the set $\{z : 0 < |z - c| < r,\ f(z) = w\}$ finite; that is, with at most one
exception, $f$ takes every complex value infinitely often on every punctured disc around $c$.

Source: Great Picard theorem, E. Picard 1879; see Ahlfors, Complex Analysis; Lean
is essential isolated singularity version with finite-fiber exceptional set subsingleton, at most
one value finitely often near c.

Proves `Wanted` entry `greatPicard`.
-/
theorem greatPicard
    {f : ℂ → ℂ} {c : ℂ} (hf : IsEssentialIsolatedSingularityAt f c) :
    Set.Subsingleton
      {w : ℂ | ∃ r : ℝ, 0 < r ∧ Set.Finite {z ∈ Metric.ball c r \ {c} | f z = w}} := by
  intro w₁ hw₁ w₂ hw₂
  by_cases hweq : w₁ = w₂
  · exact hweq
  · exfalso
    obtain ⟨r₁, hr₁pos, hr₁fin⟩ := hw₁
    obtain ⟨r₂, hr₂pos, hr₂fin⟩ := hw₂
    obtain ⟨ρ₁, hρ₁pos, hρ₁omit⟩ := gp_eventually_omit f c w₁ r₁ hr₁pos hr₁fin
    obtain ⟨ρ₂, hρ₂pos, hρ₂omit⟩ := gp_eventually_omit f c w₂ r₂ hr₂pos hr₂fin
    obtain ⟨r₀, hr₀pos, hr₀diff⟩ := hf.1
    set R : ℝ := min r₀ (min ρ₁ ρ₂) with hR
    have hRpos : 0 < R := lt_min hr₀pos (lt_min hρ₁pos hρ₂pos)
    have hsub₀ : Metric.ball c R \ {c} ⊆ Metric.ball c r₀ \ {c} := by
      intro z hz
      obtain ⟨hzball, hzne⟩ := hz
      exact ⟨Metric.ball_subset_ball (min_le_left _ _) hzball, hzne⟩
    have hsub₁ : Metric.ball c R \ {c} ⊆ Metric.ball c ρ₁ \ {c} := by
      intro z hz
      obtain ⟨hzball, hzne⟩ := hz
      exact ⟨Metric.ball_subset_ball
        ((min_le_right _ _).trans (min_le_left _ _)) hzball, hzne⟩
    have hsub₂ : Metric.ball c R \ {c} ⊆ Metric.ball c ρ₂ \ {c} := by
      intro z hz
      obtain ⟨hzball, hzne⟩ := hz
      exact ⟨Metric.ball_subset_ball
        ((min_le_right _ _).trans (min_le_right _ _)) hzball, hzne⟩
    have hfR : DifferentiableOn ℂ f (Metric.ball c R \ {c}) :=
      hr₀diff.mono hsub₀
    have hom₁ : ∀ z ∈ Metric.ball c R \ {c}, f z ≠ w₁ :=
      fun z hz => hρ₁omit z (hsub₁ hz)
    have hom₂ : ∀ z ∈ Metric.ball c R \ {c}, f z ≠ w₂ :=
      fun z hz => hρ₂omit z (hsub₂ hz)
    have hcon2 := gp_omit_two f c w₁ w₂ R hRpos hweq hfR hom₁ hom₂
    rcases hcon2 with ⟨l, hl⟩ | hpole
    · exact absurd ⟨l, hl⟩ hf.2.1
    · exact absurd hpole hf.2.2

end MathlibExt.Analysis.Complex.GreatPicardWanted
