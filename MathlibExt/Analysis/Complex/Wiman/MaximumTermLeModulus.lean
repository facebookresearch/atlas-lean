/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.Wiman.MaximumModulusAttained
public import MathlibExt.Analysis.Complex.Wiman.MaximumTermAttained
public import Mathlib.Analysis.Complex.Liouville

@[expose] public section

namespace Complex

noncomputable section

open Set

/-- **Cauchy's inequality for the maximum term.** Let $f$ be an entire function with Taylor
coefficients $a_n$ at the origin, maximum term $\mu(r) = \sup_n |a_n|\,|r|^n$ and maximum modulus
$M(r) = \sup_{|z| = |r|} |f(z)|$. Then $\mu(r) \le M(r)$ for every real $r > 0$. -/
theorem wimanMaximumTerm_le_wimanMaximumModulus
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    {r : ℝ} (hr : 0 < r) :
    wimanMaximumTerm f r ≤ wimanMaximumModulus f r := by
  obtain ⟨z, hz, hzmax, hmax⟩ :=
    exists_mem_sphere_eq_wimanMaximumModulus f hf hr.le
  apply (wimanMaximumTerm_le_iff f hf r _).2
  intro n
  have hcircle :
      ∀ w ∈ Metric.sphere (0 : ℂ) r, ‖f w‖ ≤ wimanMaximumModulus f r := by
    intro w hw
    rw [hzmax]
    exact hmax w hw
  have hcauchy :=
    Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
      n hr hf.diffContOnCl hcircle
  have hfac : 0 < (n.factorial : ℝ) := by positivity
  have hrpow : 0 < r ^ n := pow_pos hr n
  rw [wimanTerm, abs_of_pos hr, wimanTaylorCoefficient, norm_div]
  simp only [Complex.norm_natCast]
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hfac).2
  have hscaled := (le_div_iff₀ hrpow).1 hcauchy
  simpa only [mul_comm] using hscaled

end

end Complex
