/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.Wiman.CorrectedEstimateAbsorption
public import MathlibExt.Analysis.Complex.Wiman.CorrectedMajorantBoundOffExceptionalSet
public import MathlibExt.MeasureTheory.Measure.Lebesgue.Finite
public import MathlibExt.Analysis.Complex.Wiman.MaximumModulusLeMajorant
public import MathlibExt.Analysis.Complex.Wiman.MaximumTermLeModulus
public import MathlibExt.Analysis.Complex.Wiman.MaximumTermTendsToInfinity

/-!
# An unbounded-radius Wiman corollary

This file proves a strict corollary of the classical theorem quoted in
P. Filevych, *The Baire categories and Wiman's inequality for entire functions*,
Matematychni Studii 20(2) (2003), 215–221, DOI: 10.30970/ms.20.2.215-221.

The cited theorem applies to every entire function and every exponent greater
than `1 / 2`, and states that the exceptional radii have finite logarithmic
measure. The result below instead assumes transcendence, fixes the exponent to
`2 / 3`, and concludes only that suitable radii are unbounded.
-/

@[expose] public section

namespace Complex

open Filter MeasureTheory Set

noncomputable section

/-- **The maximum term tends to infinity along logarithmic radii.** Let $f$ be a transcendental
entire function with Taylor coefficients $a_n$ at the origin and maximum term
$\mu(r) = \sup_{n \ge 0} |a_n| |r|^n$. Then $\mu(e^x) \to \infty$ as $x \to \infty$. -/
theorem tendsto_wimanMaximumTerm_exp_atTop
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (htrans : IsTranscendental f) :
    Tendsto (fun x : ℝ => wimanMaximumTerm f (Real.exp x)) atTop atTop :=
  (tendsto_wimanMaximumTerm_atTop f hf htrans).comp Real.tendsto_exp_atTop

/-- **Wiman's inequality with exponent $2/3$ at arbitrarily large radii.** Let $f$ be a
transcendental entire function with Taylor coefficients $a_n$ at the origin, maximum modulus
$M(r) = \sup_{|z| = |r|} |f(z)|$ and maximum term $\mu(r) = \sup_{n \ge 0} |a_n| |r|^n$. Then
for every real $R$ there is a real $r > R$ with $M(r) \le \mu(r) (\log \mu(r))^{2/3}$.

Source: Filevych (2003), Matematychni Studii 20(2), 215–221. This is a strict corollary of,
not the full theorem stated in, that paper. -/
theorem exists_wiman_radius_two_thirds
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (htrans : IsTranscendental f) (R : ℝ) :
    ∃ r : ℝ, R < r ∧ wimanMaximumModulus f r ≤
        wimanMaximumTerm f r *
          Real.log (wimanMaximumTerm f r) ^ (2 / 3 : ℝ) := by
  obtain ⟨C, x₀, hC, hfinite, hmajorant⟩ :=
    wimanMajorant_bound_off_exceptionalSet f hf htrans
  obtain ⟨U, _hU, habsorb⟩ :=
    eventually_absorb_corrected_wiman_exponent C hC
  have hrequirements :
      ∀ᶠ x : ℝ in atTop,
        x₀ ≤ x ∧ R < Real.exp x ∧
          U ≤ wimanMaximumTerm f (Real.exp x) := by
    filter_upwards [eventually_ge_atTop x₀,
      Real.tendsto_exp_atTop.eventually (eventually_gt_atTop R),
      (tendsto_wimanMaximumTerm_exp_atTop f hf htrans).eventually
        (eventually_ge_atTop U)] with x hx₀ hR hU
    exact ⟨hx₀, hR, hU⟩
  obtain ⟨X, hX⟩ := eventually_atTop.1 hrequirements
  obtain ⟨x, hXx, hxgood⟩ :=
    MeasureTheory.exists_gt_not_mem_of_volume_lt_top
      (wimanExceptionalSet f x₀) hfinite X
  rcases hX x hXx.le with ⟨hx₀, hR, hU⟩
  let r : ℝ := Real.exp x
  have hr : 0 < r := by
    simpa only [r] using Real.exp_pos x
  have hUterm : U ≤ wimanMaximumTerm f r := by
    simpa only [r] using hU
  have htermModulus :
      wimanMaximumTerm f r ≤ wimanMaximumModulus f r :=
    wimanMaximumTerm_le_wimanMaximumModulus f hf hr
  have hmodulusMajorant :
      wimanMaximumModulus f r ≤ wimanMajorant f r :=
    wimanMaximumModulus_le_wimanMajorant f hf hr.le
  have htermMajorant :
      wimanMaximumTerm f r ≤ wimanMajorant f r :=
    htermModulus.trans hmodulusMajorant
  have hcorrected :
      wimanMajorant f r ≤
        C * wimanMaximumTerm f r *
          (1 + Real.log (wimanMajorant f r) ^ (81 / 128 : ℝ)) := by
    simpa only [r, wimanGrowth] using hmajorant x hx₀ hxgood
  have habsorbed :
      wimanMajorant f r ≤
        wimanMaximumTerm f r *
          Real.log (wimanMaximumTerm f r) ^ (2 / 3 : ℝ) :=
    habsorb (wimanMaximumTerm f r) (wimanMajorant f r)
      hUterm htermMajorant hcorrected
  exact ⟨r, by simpa only [r] using hR, hmodulusMajorant.trans habsorbed⟩

end

end Complex
