/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.Wiman.MaximumModulusAttained
public import MathlibExt.Analysis.Complex.Wiman.RadialMajorant

@[expose] public section

namespace Complex

noncomputable section

/-- **The maximum modulus is at most the radial Taylor majorant.** Let $f$ be an entire function
with Taylor coefficients $a_n$ at the origin and let $r \ge 0$. Then the maximum modulus
$M(r) = \sup_{|z| = r} |f(z)|$ satisfies $M(r) \le \sum_{n \ge 0} |a_n| r^n$. -/
theorem wimanMaximumModulus_le_wimanMajorant
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    {r : ℝ} (hr : 0 ≤ r) :
    wimanMaximumModulus f r ≤ wimanMajorant f r := by
  obtain ⟨z, hz, hmax, _⟩ :=
    exists_mem_sphere_eq_wimanMaximumModulus f hf hr
  rw [hmax]
  have hs := hasSum_wimanTaylorCoefficient_mul_pow f hf z
  calc
    ‖f z‖ = ‖∑' n : ℕ, wimanTaylorCoefficient f n * z ^ n‖ := by
      rw [hs.tsum_eq]
    _ ≤ ∑' n : ℕ, ‖wimanTaylorCoefficient f n * z ^ n‖ :=
      norm_tsum_le_tsum_norm hs.summable.norm
    _ = wimanMajorant f r := by
      rw [wimanMajorant]
      apply tsum_congr
      intro n
      rw [norm_mul, norm_pow, mem_sphere_zero_iff_norm.mp hz, wimanTerm,
        abs_of_nonneg hr]

end

end Complex
