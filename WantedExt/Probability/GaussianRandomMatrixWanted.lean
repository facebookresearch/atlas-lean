/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Data.Matrix.Mul

/-!
# Largest singular value of a Gaussian random matrix: wishlist

For an `n × d` matrix `X` with independent standard normal entries, the largest singular value
satisfies `σ_max(X) ≤ √n (1 + δ) + √d` with probability at least `1 - exp (-n δ² / 2)`
(Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University
Press, 2019, §6.2, with `Σ = I`; R. Vershynin, arXiv:1011.3027, Theorem 5.32 and
Proposition 5.34 with `t = δ √n`). It is the basic estimate behind
covariance estimation and the restricted eigenvalue property of Gaussian designs. The proof uses
Gordon's comparison inequality and Gaussian Lipschitz concentration, neither formalized here.

The event `σ_max(X) ≥ t`, for `t ≥ 0`, is written without operator norms: some nonzero
`u : Fin d → ℝ` has `‖X u‖₂² ≥ t² ‖u‖₂²`.
-/

open MeasureTheory ProbabilityTheory Matrix

namespace MathlibExt.Probability.GaussianRandomMatrixWanted

@[expose] public section

/-- **Largest singular value of a standard Gaussian matrix** (Wainwright, *High-Dimensional
Statistics*, 2019, §6.2, with `Σ = I`; Vershynin, arXiv:1011.3027, Theorem 5.32 and
Proposition 5.34): if `X` is an `n × d` matrix with independent
`N(0, 1)` entries and `δ ≥ 0`, then
`P(σ_max(X) ≥ √n (1 + δ) + √d) ≤ exp (-n δ² / 2)`. -/
public theorem_wanted measureReal_sigmaMax_ge_le (n d : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (Measure.pi fun _ : Fin n × Fin d => gaussianReal 0 1).real
        {x | ∃ u : Fin d → ℝ, u ≠ 0 ∧
          (Real.sqrt n * (1 + δ) + Real.sqrt d) ^ 2 * ∑ j, u j ^ 2 ≤
            ∑ i, (Matrix.of (fun i j => x (i, j)) *ᵥ u) i ^ 2} ≤
      Real.exp (-(n : ℝ) * δ ^ 2 / 2)

end

end MathlibExt.Probability.GaussianRandomMatrixWanted
