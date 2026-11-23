/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Analysis.Convex.NesterovSmoothing
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Convex.Strong
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Smoothness of Nesterov's smoothed max-type function (wanted)

Theorem 1 of Yu. Nesterov, *Smooth minimization of non-smooth functions*, Math. Program. 103
(2005) 127-152, for Euclidean norms.
-/

@[expose] public section

open MathlibExt.Analysis.Convex.NesterovSmoothing

namespace WantedExt.Analysis.Convex.NesterovSmoothingWanted

/-- **The smoothed max-type function has a Lipschitz gradient.** Let `E`, `F` be
finite-dimensional real inner product spaces, `A : E →L[ℝ] F`, `Q ⊆ F` nonempty, compact and
convex, `φ` continuous and convex on `Q`, `d` continuous and `σ`-strongly convex on `Q` with
`σ > 0`, and `μ > 0`. Then `f_μ = smoothedMax A φ d Q μ` is convex and differentiable on `E`,
and its gradient is Lipschitz with constant `‖A‖ ^ 2 / (μ σ)`.

This is Theorem 1 of Yu. Nesterov, *Smooth minimization of non-smooth functions*, Math.
Program. 103 (2005) 127-152, specialised to Euclidean norms on both spaces, for which the norm
`‖A‖_{1,2}` of the source is the operator norm; the source also gives the gradient
`∇f_μ(x) = A* u_μ(x)`, with `u_μ(x)` the unique maximiser, which is not stated here. -/
theorem_wanted smoothedMax_convex_differentiable_lipschitz {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (A : E →L[ℝ] F) {φ d : F → ℝ} {Q : Set F} (hQ : IsCompact Q) (hQne : Q.Nonempty)
    (hQc : Convex ℝ Q) (hφ : ContinuousOn φ Q) (hφc : ConvexOn ℝ Q φ) (hd : ContinuousOn d Q)
    {σ : ℝ} (hσ : 0 < σ) (hdσ : StrongConvexOn Q σ d) {μ : ℝ} (hμ : 0 < μ) :
    ConvexOn ℝ Set.univ (smoothedMax A φ d Q μ) ∧ Differentiable ℝ (smoothedMax A φ d Q μ) ∧
      LipschitzWith ⟨‖A‖ ^ 2 / (μ * σ), div_nonneg (sq_nonneg _) (mul_pos hμ hσ).le⟩
        (gradient (smoothedMax A φ d Q μ))

end WantedExt.Analysis.Convex.NesterovSmoothingWanted
