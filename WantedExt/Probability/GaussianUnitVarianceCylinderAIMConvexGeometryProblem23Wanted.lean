/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Unit directional variance of a restricted Gaussian forces a cylinder (AIM, O'Donnell's Problem 4)

AIM workshop on algorithmic convex geometry, Problem 4 (R. O'Donnell): let `K ⊆ ℝⁿ` be convex and
`X` a Gaussian conditioned to lie in `K`; does `Var(X_θ) = 1` imply that `K` is a cylinder in
direction `θ`? The list remarks that `Var(X_θ) ≤ 1` always holds. Vempala's monotonicity lemma
answers the first question; the second (stability) question is not formalized.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

@[expose] public section

namespace MathlibExt.Probability.GaussianUnitVarianceCylinderAIMConvexGeometryProblem23Wanted

/-!
Source: Problems from the AIM Workshop on Algorithmic Convex Geometry (compiled by N. Goyal),
Problem 4 (R. O'Donnell), https://aimath.org/WWN/convexgeometry/convexgeometry.pdf. UnsolvedMath
record UM-20001291 (`AIM-CONVEX_GEOMETRY-0023`), dataset ulamai/UnsolvedMath v1.8.0.

`X` is the standard Gaussian of `ℝⁿ` (Mathlib's `stdGaussian`) conditioned on `K` (`cond`), which
needs positive Gaussian measure, `θ` is a unit vector and `X_θ = ⟪X, θ⟫`; a cylinder in direction
`θ` is a set with `x + s θ ∈ K` for all `x ∈ K` and `s ∈ ℝ`. The set is taken closed: for an
arbitrary convex set the conclusion holds only up to the boundary (the open half-plane `{x₂ > 0}`
with the ray `{(x₁, 0) | x₁ > 0}` added is convex, has the same conditioned Gaussian as the
half-plane, `Var(X_{e₁}) = 1`, and is not invariant under `e₁`-translations).
-/

open MeasureTheory ProbabilityTheory

/-- O'Donnell's question (AIM algorithmic convex geometry list, Problem 4), first part, for closed
convex sets: if `K ⊆ ℝⁿ` is closed and convex with positive standard Gaussian measure, `θ` is a unit
vector, and the standard Gaussian conditioned on `K` has variance `1` in the direction `θ`, then `K`
is a cylinder in the direction `θ`: `x + s θ ∈ K` for all `x ∈ K` and `s ∈ ℝ`. -/
def unitDirectionalVarianceImpliesCylinder : Prop :=
  ∀ (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))) (θ : EuclideanSpace ℝ (Fin n)),
    IsClosed K → Convex ℝ K → 0 < stdGaussian (EuclideanSpace ℝ (Fin n)) K → ‖θ‖ = 1 →
    variance (fun x => inner ℝ x θ) (stdGaussian (EuclideanSpace ℝ (Fin n)))[|K] = 1 →
      ∀ x ∈ K, ∀ s : ℝ, x + s • θ ∈ K

/--
Resolved true: if the standard Gaussian conditioned on a closed convex set `K` of positive Gaussian
measure has variance `1` in a unit direction `θ`, then `K` is a cylinder in direction `θ`. Vempala,
§1: 'restricting a Gaussian to any convex set decreases the variance in any direction along which
the convex set imposes a nontrivial restriction ... Our monotonicity lemma settles an open question
posed by O'Donnell [Goy]' ([Goy] is this problem list); Lemma 4.8 is the one-dimensional statement
(for logconcave f, the normalized second moment of e^{-(x - μ)²/2} f(x) about its mean is at most 1,
with equality only if f is constant on ℝ), applied as in the proof of Theorem 4.10 to the marginal
of X along θ, whose density is e^{-z²/2} times the logconcave Gaussian measure of the section of K
orthogonal to θ at height z; variance 1 forces these section measures to be constant. Source:
Problems from the AIM Workshop on Algorithmic Convex Geometry (compiled by N. Goyal), Problem 4 (R.
O'Donnell), https://aimath.org/WWN/convexgeometry/convexgeometry.pdf; resolution: S. Vempala,
Learning convex concepts from Gaussian distributions with PCA, 51st Annual IEEE Symposium on
Foundations of Computer Science (FOCS 2010), 124-130, §1 (monotonicity of the variance under convex
restriction; settles O'Donnell's question [Goy]) and Lemma 4.8 (equality only for constant f), as
numbered in the author's PDF https://faculty.cc.gatech.edu/~vempala/papers/kplanes-pca.pdf,
https://doi.org/10.1109/FOCS.2010.19.
-/
public theorem_wanted unitDirectionalVarianceImpliesCylinder_holds :
    unitDirectionalVarianceImpliesCylinder

end MathlibExt.Probability.GaussianUnitVarianceCylinderAIMConvexGeometryProblem23Wanted
