/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.Wiman.CumulantMoments
public import MathlibExt.Analysis.Complex.Wiman.MaximumTermTendsToInfinity
public import Mathlib.Analysis.Convex.Deriv

@[expose] public section

namespace Complex

open Filter MeasureTheory Set

noncomputable section

/-- **Eventual regularity of the logarithmic majorant.** Let $f$ be a transcendental entire
function with Taylor coefficients $a_n$ at the origin, and let
$\Phi(x) = \log \sum_{n \ge 0} |a_n| e^{nx}$. Then $\Phi$ is twice continuously differentiable
on $\mathbb{R}$, $\Phi'(x) \to \infty$ as $x \to \infty$, and there is a real $x_0$ such that
$\Phi(x) > 0$ for every $x \ge x_0$ and both $\Phi$ and $\Phi'$ are nondecreasing on
$[x_0, \infty)$. -/
theorem eventually_wimanGrowth_regular
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (htrans : IsTranscendental f) :
    ∃ x₀ : ℝ,
      (∀ x, x₀ ≤ x → 0 < wimanGrowth f x) ∧
      MonotoneOn (wimanGrowth f) (Set.Ici x₀) ∧
      MonotoneOn (deriv (wimanGrowth f)) (Set.Ici x₀) ∧
      ContDiff ℝ 2 (wimanGrowth f) ∧
      Tendsto (deriv (wimanGrowth f)) atTop atTop := by
  have hsupport := infinite_support_wimanTaylorCoefficient f hf htrans
  have hne : ∃ n, wimanTaylorCoefficient f n ≠ 0 := by
    obtain ⟨n, hn⟩ := hsupport.nonempty
    exact ⟨n, by simpa only [Function.mem_support] using hn⟩
  have hC2 : ContDiff ℝ 2 (wimanGrowth f) := contDiff_two_wimanGrowth f hf
  have hDiff : Differentiable ℝ (wimanGrowth f) :=
    hC2.differentiable two_ne_zero
  have hDerivNonneg : ∀ x, 0 ≤ deriv (wimanGrowth f) x := by
    intro x
    rw [deriv_wimanGrowth_eq_expectation f hf hne x]
    exact integral_nonneg fun n : ℕ => Nat.cast_nonneg n
  have hGrowthMono : Monotone (wimanGrowth f) :=
    monotone_of_deriv_nonneg hDiff hDerivNonneg
  have hDiffDeriv : Differentiable ℝ (deriv (wimanGrowth f)) :=
    hC2.differentiable_deriv_two
  have hSecondDeriv :
      deriv (deriv (wimanGrowth f)) = iteratedDeriv 2 (wimanGrowth f) := by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
  have hDerivMono : Monotone (deriv (wimanGrowth f)) := by
    apply monotone_of_deriv_nonneg hDiffDeriv
    intro x
    rw [hSecondDeriv]
    exact iteratedDeriv_two_wimanGrowth_nonneg f hf hne x
  have hConvex : ConvexOn ℝ Set.univ (wimanGrowth f) :=
    Monotone.convexOn_univ_of_deriv hDiff hDerivMono
  have hDerivAtTop : Tendsto (deriv (wimanGrowth f)) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    obtain ⟨N : ℕ, hbN⟩ := exists_nat_gt b
    obtain ⟨n, hnmem, hNn⟩ := hsupport.exists_gt N
    have hncoeff : wimanTaylorCoefficient f n ≠ 0 := by
      simpa only [Function.mem_support] using hnmem
    have hNn' : (N : ℝ) < (n : ℝ) := by exact_mod_cast hNn
    have hbn : b < (n : ℝ) := hbN.trans hNn'
    have hgap : 0 < (n : ℝ) - b := sub_pos.mpr hbn
    filter_upwards [eventually_ge_atTop
      (max 1 ((wimanGrowth f 0 - Real.log ‖wimanTaylorCoefficient f n‖) /
        ((n : ℝ) - b)))] with y hy
    have hypos : 0 < y :=
      zero_lt_one.trans_le ((le_max_left 1 _).trans hy)
    have hthreshold :
        (wimanGrowth f 0 - Real.log ‖wimanTaylorCoefficient f n‖) /
            ((n : ℝ) - b) ≤ y :=
      (le_max_right 1 _).trans hy
    have hprod :
        wimanGrowth f 0 - Real.log ‖wimanTaylorCoefficient f n‖ ≤
          y * ((n : ℝ) - b) :=
      (div_le_iff₀ hgap).mp hthreshold
    have htermpos : 0 < wimanTerm f (Real.exp y) n := by
      rw [wimanTerm, abs_of_pos (Real.exp_pos y)]
      exact mul_pos (norm_pos_iff.mpr hncoeff) (pow_pos (Real.exp_pos y) n)
    have hlinear :
        Real.log ‖wimanTaylorCoefficient f n‖ + (n : ℝ) * y ≤
          wimanGrowth f y := by
      calc
        Real.log ‖wimanTaylorCoefficient f n‖ + (n : ℝ) * y =
            Real.log (wimanTerm f (Real.exp y) n) := by
          rw [wimanTerm, abs_of_pos (Real.exp_pos y),
            Real.log_mul (norm_ne_zero_iff.mpr hncoeff)
              (pow_ne_zero n (Real.exp_ne_zero y)),
            Real.log_pow, Real.log_exp]
        _ ≤ wimanGrowth f y := by
          rw [wimanGrowth]
          exact Real.log_le_log htermpos
            (wimanTerm_le_wimanMajorant f hf (Real.exp y) n)
    have hbnum : b * y ≤ wimanGrowth f y - wimanGrowth f 0 := by
      nlinarith
    have hbslope : b ≤ slope (wimanGrowth f) 0 y := by
      rw [slope_def_field, sub_zero]
      exact (le_div_iff₀ hypos).2 hbnum
    exact hbslope.trans
      (hConvex.slope_le_deriv (by simp) (by simp) hypos (hDiff y))
  have hMaximumAtTop :
      Tendsto (fun x : ℝ => wimanMaximumTerm f (Real.exp x)) atTop atTop :=
    (tendsto_wimanMaximumTerm_atTop f hf htrans).comp Real.tendsto_exp_atTop
  have hEventuallyPos : ∀ᶠ x : ℝ in atTop, 0 < wimanGrowth f x := by
    filter_upwards [hMaximumAtTop.eventually (eventually_gt_atTop 1)] with x hx
    rw [wimanGrowth]
    apply Real.log_pos
    exact hx.trans_le <| (wimanMaximumTerm_le_iff f hf (Real.exp x) _).2 fun n =>
      wimanTerm_le_wimanMajorant f hf (Real.exp x) n
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 hEventuallyPos
  exact ⟨x₀, hx₀, hGrowthMono.monotoneOn (Set.Ici x₀),
    hDerivMono.monotoneOn (Set.Ici x₀), hC2, hDerivAtTop⟩

end

end Complex
