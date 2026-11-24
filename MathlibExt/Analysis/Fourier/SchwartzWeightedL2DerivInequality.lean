/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level2/ma_proofbench_l2_40.lean` (openbmb/ma-proofbench, commit
31bab4c78fd1b0c464e767d62e9202163d1e9029), which supplies the theorem statement and its problem
description (MA-ProofBench, arXiv:2606.13782):
Copyright (c) 2026 OpenBMB. Licensed under the MIT License, reproduced below.
Authors: L. Pu et al. (MA-ProofBench)

Changes made: the source's `theorem ma_proofbench_l2_40 … := by sorry` was renamed to
`integral_sq_le_two_mul_sqrt_integral_mul_sq_mul_sqrt_integral_deriv_sq` and placed in namespace
`MathlibExt.Analysis.Fourier.SchwartzWeightedL2DerivInequalityWanted`, the informal problem
statement became its docstring, `import Mathlib` was replaced by a narrower import, and a proof
was supplied.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import MathlibExt.Analysis.Fourier.HeisenbergUncertainty

/-!
# A weighted `L²` inequality for real Schwartz functions

For a real-valued Schwartz function `f` on `ℝ`, the main result
`integral_sq_le_two_mul_sqrt_integral_mul_sq_mul_sqrt_integral_deriv_sq` states
`∫ ‖f x‖² ≤ 2 * √(∫ ‖x * f x‖²) * √(∫ ‖f' x‖²)`, that is, `‖f‖₂² ≤ 2 ‖x f‖₂ ‖f'‖₂`.

It is the square root of the real form of Heisenberg's uncertainty principle,
`HeisenbergUncertainty.heisenberg_uncertainty_real`:
`(∫ f²)² ≤ 4 * (∫ x² f²) * (∫ f'²)`. That inequality comes from the integration by parts
`∫ f² = -2 * ∫ x f f'` and the bound `2 |x f f'| ≤ ε x² f² + f'² / ε`, optimized over `ε > 0`.
-/

public section

open MeasureTheory

namespace MathlibExt.Analysis.Fourier.SchwartzWeightedL2DerivInequalityWanted

/-- **Weighted $L^2$ inequality for real Schwartz functions.** For every real-valued Schwartz
function $f : \mathbb{R} \to \mathbb{R}$,
$$
\int_{\mathbb{R}} f(x)^2 \, dx \le 2 \left( \int_{\mathbb{R}} x^2 f(x)^2 \, dx \right)^{1/2}
\left( \int_{\mathbb{R}} f'(x)^2 \, dx \right)^{1/2},
$$
that is, $\|f\|_{L^2}^2 \le 2 \, \|x f\|_{L^2} \, \|f'\|_{L^2}$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Real functions; Inequalities
in real analysis), `benchmark/level2/ma_proofbench_l2_40.lean` at openbmb/ma-proofbench@31bab4c.
-/
theorem integral_sq_le_two_mul_sqrt_integral_mul_sq_mul_sqrt_integral_deriv_sq
    (f : SchwartzMap ℝ ℝ) :
    (∫ x : ℝ, ‖f x‖ ^ 2) ≤
      2 * Real.sqrt (∫ x : ℝ, ‖x * f x‖ ^ 2) *
        Real.sqrt (∫ x : ℝ, ‖deriv (fun y : ℝ => f y) x‖ ^ 2) := by
  have hX : 0 ≤ ∫ x, x ^ 2 * f x ^ 2 := integral_nonneg fun x => by positivity
  have hD : 0 ≤ ∫ x, deriv f x ^ 2 := integral_nonneg fun x => sq_nonneg _
  simp only [Real.norm_eq_abs, sq_abs, mul_pow]
  calc ∫ x, f x ^ 2
      ≤ Real.sqrt (4 * (∫ x, x ^ 2 * f x ^ 2) * ∫ x, deriv f x ^ 2) :=
        Real.le_sqrt_of_sq_le (HeisenbergUncertainty.heisenberg_uncertainty_real f)
    _ = 2 * Real.sqrt (∫ x, x ^ 2 * f x ^ 2) * Real.sqrt (∫ x, deriv f x ^ 2) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num),
          show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

end MathlibExt.Analysis.Fourier.SchwartzWeightedL2DerivInequalityWanted
