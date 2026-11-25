/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level1/ma_proofbench_l1_05.lean` (openbmb/ma-proofbench, commit 31bab4c).
The theorem statement is adapted from MA-ProofBench by L. Pu et al., under the MIT License.

Copyright (c) 2026 OpenBMB

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

public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.PSeries

/-!
# Uniform convergence of the series of cosine differences

On a bounded interval the quadratic cosine bound gives a summable majorant for the series.
-/

namespace MathlibExt.Analysis.SpecificLimits.OneSubCosDivSeriesUniformWanted

/-- **Uniform convergence of $\sum (1 - \cos(x/n))$ on compact intervals.** For all real numbers
$a < b$ there is a function $g : \mathbb{R} \to \mathbb{R}$ such that the partial sums
$\sum_{n=1}^{N} \bigl(1 - \cos(x/n)\bigr)$ converge to $g(x)$ uniformly for $x \in [a, b]$ as
$N \to \infty$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Sequences, series, summability;
Convergence and divergence of infinite limiting processes),
`benchmark/level1/ma_proofbench_l1_05.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem tendstoUniformlyOn_sum_one_sub_cos_div
    (f : ℕ → ℝ → ℝ) (hf : ∀ n x, f n x = 1 - Real.cos (x / (n + 1))) :
    ∀ a b : ℝ, a < b → ∃ g : ℝ → ℝ,
        TendstoUniformlyOn
          (fun N x => ∑ n ∈ Finset.range N, f n x) g Filter.atTop (Set.Icc a b) := by
  intro a b _
  let R := max |a| |b|
  have hsum : Summable (fun n : ℕ => (R ^ 2 / 2) / ((n : ℝ) + 1) ^ 2) := by
    apply Summable.of_norm
    simpa only [Nat.cast_one] using summable_pow_div_add (R ^ 2 / 2) 2 1 Nat.one_lt_two
  refine ⟨fun x => ∑' n, f n x, tendstoUniformlyOn_tsum_nat hsum ?_⟩
  intro n x hx
  have hxR : |x| ≤ R := abs_le_max_abs_abs hx.1 hx.2
  have hsq : x ^ 2 ≤ R ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg x) hxR 2
  rw [hf, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one _))]
  calc
    1 - Real.cos (x / (n + 1)) ≤ (x / (n + 1)) ^ 2 / 2 := by
      linarith only [Real.one_sub_sq_div_two_le_cos (x := x / (n + 1))]
    _ = (x ^ 2 / 2) / ((n : ℝ) + 1) ^ 2 := by rw [div_pow, div_right_comm]
    _ ≤ (R ^ 2 / 2) / ((n : ℝ) + 1) ^ 2 := by gcongr

end MathlibExt.Analysis.SpecificLimits.OneSubCosDivSeriesUniformWanted
