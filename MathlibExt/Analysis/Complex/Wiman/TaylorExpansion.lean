/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.Wiman
public import Mathlib.Analysis.Complex.TaylorSeries

@[expose] public section

namespace Complex

noncomputable section

/-- **Taylor expansion of an entire function.** Let $f$ be an entire function with Taylor
coefficients $a_n = f^{(n)}(0) / n!$ at the origin. For every $z \in \mathbb{C}$, the series
$\sum_{n \ge 0} a_n z^n$ converges unconditionally to $f(z)$. -/
theorem hasSum_wimanTaylorCoefficient_mul_pow
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (z : ℂ) :
    HasSum (fun n : ℕ => wimanTaylorCoefficient f n * z ^ n) (f z) := by
  simpa only [sub_zero, smul_eq_mul, wimanTaylorCoefficient, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc] using
    (Complex.hasSum_taylorSeries_of_entire hf 0 z)

end

end Complex
