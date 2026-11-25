/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level1/ma_proofbench_l1_01.lean` (openbmb/ma-proofbench, commit
31bab4c78fd1b0c464e767d62e9202163d1e9029), by L. Pu et al. The main theorem's statement and
informal description are adapted from that problem, distributed under the MIT License.

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

public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# A bound on a difference of reciprocals

For real `a > 1` and `x ≥ 1`, the difference `1 / (1 + x) - 1 / (1 + a * x)` is at most
`(√a - 1) / (√a + 1)`. Clearing denominators reduces the bound to the nonnegativity of
`(√a - 1) * (√a * x - 1) ^ 2`.
-/

namespace MathlibExt.Analysis.Calculus.ReciprocalDifferenceSqrtBoundWanted

/-- **A bound on a difference of reciprocals.** For all real numbers $a > 1$ and $x \ge 1$,

$$
\frac{1}{1+x}-\frac{1}{1+ax}\le \frac{\sqrt{a}-1}{\sqrt{a}+1}.
$$

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Inequalities in
real analysis), `benchmark/level1/ma_proofbench_l1_01.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem one_div_one_add_sub_one_div_one_add_mul_le
    {a x : ℝ} (ha : 1 < a) (hx : 1 ≤ x) :
    (1 / (1 + x) - 1 / (1 + a * x)) ≤ (Real.sqrt a - 1) / (Real.sqrt a + 1) := by
  set s := Real.sqrt a
  have hs : 1 ≤ s := Real.one_le_sqrt.mpr ha.le
  have hs_sq : s ^ 2 = a := Real.sq_sqrt (zero_le_one.trans ha.le)
  have hx_pos : 0 < x := zero_lt_one.trans_le hx
  rw [← hs_sq]
  field_simp
  linear_combination mul_nonneg (sub_nonneg.mpr hs) (sq_nonneg (s * x - 1))

end MathlibExt.Analysis.Calculus.ReciprocalDifferenceSqrtBoundWanted
