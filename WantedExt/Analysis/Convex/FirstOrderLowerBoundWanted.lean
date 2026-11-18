/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Convex.Strong
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Lower complexity bound for strongly convex first-order minimisation (wanted)

The strongly convex lower complexity bound of Section 2.1.4 of Yu. Nesterov, *Introductory
Lectures on Convex Programming, Volume I: Basic course* (lecture notes, July 2, 1998): no method
whose iterates stay in `x 0 + span {∇f (x 0), …, ∇f (x (j - 1))}` (Assumption 2.1.4 there) can
contract faster than `((√Q - 1) / (√Q + 1)) ^ (2 k)`. The span condition is stated for every `j`;
for `j = 0` it only says `x 0 = x₀`. The smooth convex bound, Theorem 2.1.6 there, is proved in
`MathlibExt.Analysis.Convex.FirstOrderLowerBound`.
-/

@[expose] public section

open scoped ContDiff

namespace WantedExt.Analysis.Convex.FirstOrderLowerBoundWanted

/-- **Lower complexity bound for smooth strongly convex minimisation.** Let `μ > 0` and `Q > 1`.
For every `x₀ ∈ ℓ²` there is a `μ`-strongly convex `C^∞` function `f` on `ℓ²` with
`μ Q`-Lipschitz gradient and a minimiser `x⋆` such that every sequence with `x 0 = x₀` and
`x j - x₀ ∈ span {∇f (x i) : i < j}` for all `j` satisfies, for every `k`,
`‖x k - x⋆‖ ^ 2 ≥ ((√Q - 1) / (√Q + 1)) ^ (2 k) ‖x₀ - x⋆‖ ^ 2` and
`f (x k) - f x⋆ ≥ μ / 2 ((√Q - 1) / (√Q + 1)) ^ (2 k) ‖x₀ - x⋆‖ ^ 2`.

This is Theorem 2.1.12 of Yu. Nesterov, *Introductory Lectures on Convex Programming, Volume I:
Basic course* (lecture notes, July 2, 1998), stated there on `R^∞`, the space `ℓ²` of
square-summable sequences, for the class `S^{∞,1}_{μ, μ Q}`. -/
theorem_wanted exists_lower_bound_strongly_convex {μ Q : ℝ} (hμ : 0 < μ) (hQ : 1 < Q)
    (x₀ : lp (fun _ : ℕ => ℝ) 2) :
    ∃ f : lp (fun _ : ℕ => ℝ) 2 → ℝ, ContDiff ℝ ∞ f ∧ StrongConvexOn Set.univ μ f ∧
      LipschitzWith ⟨μ * Q, by positivity⟩ (gradient f) ∧
      ∃ xstar : lp (fun _ : ℕ => ℝ) 2, (∀ z, f xstar ≤ f z) ∧
        ∀ x : ℕ → lp (fun _ : ℕ => ℝ) 2, x 0 = x₀ →
          (∀ j, x j - x₀ ∈ Submodule.span ℝ ((fun i => gradient f (x i)) '' Set.Iio j)) →
          ∀ k : ℕ,
            ((√Q - 1) / (√Q + 1)) ^ (2 * k) * ‖x₀ - xstar‖ ^ 2 ≤ ‖x k - xstar‖ ^ 2 ∧
              μ / 2 * ((√Q - 1) / (√Q + 1)) ^ (2 * k) * ‖x₀ - xstar‖ ^ 2 ≤ f (x k) - f xstar

end WantedExt.Analysis.Convex.FirstOrderLowerBoundWanted
