/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Convex.Cocoercivity
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace MathlibExt.Analysis.Convex.Cocoercivity

private theorem gradient_half_sq : gradient (fun x : ℝ => x ^ 2 / 2) = id := by
  funext x
  have h : HasDerivAt (fun x : ℝ => x ^ 2 / 2) x x := by
    have := ((hasDerivAt_pow 2 x).div_const 2)
    convert this using 1
    simp
  simpa using h.hasGradientAt.gradient

private theorem convexOn_half_sq : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2 / 2) := by
  have h := (Even.convexOn_pow (n := 2) even_two).smul (c := (1 / 2 : ℝ)) (by norm_num)
  convert h using 1
  funext x
  simp [div_eq_inv_mul]

-- Co-coercivity for `f(x) = x² / 2` on `ℝ` (`β = 1`), where it holds with equality.
example (v w : ℝ) : 1 / 1 * ‖gradient (fun x : ℝ => x ^ 2 / 2) v -
    gradient (fun x : ℝ => x ^ 2 / 2) w‖ ^ 2 ≤
      inner ℝ (gradient (fun x : ℝ => x ^ 2 / 2) v - gradient (fun x : ℝ => x ^ 2 / 2) w)
        (v - w) :=
  inner_gradient_sub_ge one_pos convexOn_half_sq (by fun_prop)
    (by rw [gradient_half_sq]; exact LipschitzWith.id) v w

-- For `f(x) = x² / 2` and the largest admissible step `α = 2`, the gradient update `x ↦ -x` is
-- non-expansive.
example (v w : ℝ) :
    ‖(v - (2 : ℝ) • gradient (fun x : ℝ => x ^ 2 / 2) v) -
      (w - (2 : ℝ) • gradient (fun x : ℝ => x ^ 2 / 2) w)‖ ≤ ‖v - w‖ :=
  norm_gradientStep_sub_le one_pos convexOn_half_sq (by fun_prop)
    (by rw [gradient_half_sq]; exact LipschitzWith.id) (by norm_num) (by norm_num) v w

-- The gradient update of a `1`-Lipschitz function moves each point by at most the step.
example (α : ℝ) (hα : 0 ≤ α) (w : ℝ) : ‖α • gradient (fun x : ℝ => x) w‖ ≤ α * (1 : NNReal) :=
  norm_smul_gradient_le LipschitzWith.id hα w

end MathlibExt.Analysis.Convex.Cocoercivity
