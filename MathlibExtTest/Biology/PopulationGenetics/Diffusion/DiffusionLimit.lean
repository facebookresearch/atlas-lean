/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.PopulationGenetics.Diffusion.DiffusionLimit

/-! Tests for the Wright–Fisher diffusion limit: the one-generation expectation as a Bernstein
approximation, and the generator limit for the heterozygosity test function, which recovers
`L_0 H = -H`. -/

open Filter
open scoped unitInterval Topology

namespace MathlibExtTest.Biology.PopulationGenetics.Diffusion.DiffusionLimit

open MathlibExt.Biology.PopulationGenetics.Diffusion

/-- One generation from a fixed allele keeps it fixed: `E_1[f(X₁)] = f(1)` for `M ≠ 0`. -/
example (M : ℕ) (hM : M ≠ 0) (f : ℝ → ℝ) (hf : Continuous f) :
    ∫ k, f (k / M) ∂(ProbabilityTheory.binomial M 1) = f 1 := by
  rw [integral_binomial_eq_bernsteinApproximation M hf, bernsteinApproximation.apply_one hM]
  rfl

/-- The heterozygosity `H(y) = 2y(1 - y)` decays at rate `1` in the diffusion limit:
`M (E_x[H(X₁)] - H(x)) → -H(x)`. -/
example (x : I) :
    Tendsto (fun M : ℕ => (M : ℝ) * (∫ k, 2 * ((k : ℝ) / M) * (1 - (k : ℝ) / M)
        ∂(ProbabilityTheory.binomial M x) - 2 * x * (1 - x))) atTop
      (𝓝 (-(2 * (x : ℝ) * (1 - x)))) := by
  have h := tendsto_wfGenerator (f := fun y : ℝ => 2 * y * (1 - y)) (by fun_prop) x
  rwa [generator_heterozygosity] at h

end MathlibExtTest.Biology.PopulationGenetics.Diffusion.DiffusionLimit
