/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Global convergence of Newton's method for increasing convex functions

D. Levy, *Introduction to Numerical Analysis*, lecture notes, Department of Mathematics,
University of Maryland, Section 2.4, Theorem 2.8 and its proof ([author copy][levy]). Levy
states the hypotheses as "monotonically increasing, convex", and his proof uses them as
`f' x > 0` and `f'' x > 0` for every `x`, the form stated here.

The local quadratic convergence near a simple root is
`MetaMathlibExt.newton_method_local_quadratic_convergence`.

[levy]: https://www.math.umd.edu/~dlevy/resources/notes.pdf
-/

@[expose] public section

namespace MetaMathlibExt

/-- **Global convergence of Newton's method for increasing convex functions** (Levy,
*Introduction to Numerical Analysis*, Theorem 2.8). Let `f : ℝ → ℝ` be twice continuously
differentiable with `f' x > 0` and `f'' x > 0` for every `x`, and let `r` be a zero of `f`.
Then `r` is the only zero of `f`, and every sequence of Newton iterates
`X (n + 1) = X n - f (X n) / f' (X n)`, whatever its starting point `X 0`, converges to `r`;
moreover `X n ≥ r` and `X (n + 1) ≤ X n` for every `n ≥ 1`. -/
theorem_wanted newton_method_global_convergence {f : ℝ → ℝ} {r : ℝ} (hf : ContDiff ℝ 2 f)
    (hf' : ∀ x, 0 < deriv f x) (hf'' : ∀ x, 0 < deriv (deriv f) x) (hr : f r = 0) :
    (∀ s, f s = 0 → s = r) ∧
      ∀ X : ℕ → ℝ, (∀ n, X (n + 1) = X n - f (X n) / deriv f (X n)) →
        Filter.Tendsto X Filter.atTop (nhds r) ∧ (∀ n ≥ 1, r ≤ X n) ∧
          ∀ n ≥ 1, X (n + 1) ≤ X n

end MetaMathlibExt
