/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level1/ma_proofbench_l1_73.lean` (openbmb/ma-proofbench, commit 31bab4c).
MA-ProofBench supplies the theorem statement and problem description.
Copyright (c) 2026 OpenBMB
Licensed under the MIT License.
Authors: Lushi Pu, Weiming Zhang, Xinheng Xie, Zixuan Fu, Bingxiang He, Hongya Lyu,
Xin Li, Jie Zhou, Yudong Wang

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

public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith

/-!
# Error bound for the partial sums of the series for $e$

The remainder after the term $1/n!$ is positive and strictly less than $1/(n \cdot n!)$
for every positive integer $n$.
-/

public section

namespace MathlibExt.Analysis.SpecificLimits.ExpOneTaylorRemainderBoundWanted

/-- **Error bound for the partial sums of the series for $e$.** For every integer $n \ge 1$,

$$0 < e - \sum_{k=0}^{n} \frac{1}{k!} < \frac{1}{n \cdot n!}.$$

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Functions of
one variable), `benchmark/level1/ma_proofbench_l1_73.lean` at openbmb/ma-proofbench@31bab4c.
-/
theorem exp_one_sub_sum_inv_factorial_pos_and_lt (n : ℕ) (hn : 0 < n) :
    0 < Real.exp 1 - (∑ k ∈ Finset.range (n + 1), (1 : ℝ) / (Nat.factorial k)) ∧
    Real.exp 1 - (∑ k ∈ Finset.range (n + 1), (1 : ℝ) / (Nat.factorial k)) <
      (1 : ℝ) / (n * Nat.factorial n) := by
  constructor
  · have h := Real.sum_le_exp_of_nonneg (x := 1) zero_le_one (n + 1 + 1)
    rw [Finset.sum_range_succ] at h
    simp only [one_pow] at h
    exact sub_pos.mpr ((lt_add_of_pos_right _ (by positivity)).trans_le h)
  · have h := Real.exp_bound' (x := 1) zero_le_one le_rfl (Nat.succ_pos n)
    simp only [one_pow, one_mul] at h
    apply lt_of_le_of_lt (sub_le_iff_le_add'.mpr h)
    -- After cancelling the factorials, strictness is n(n + 2) < (n + 1)².
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hf : (0 : ℝ) < n.factorial := by positivity
    field_simp
    nlinarith

end MathlibExt.Analysis.SpecificLimits.ExpOneTaylorRemainderBoundWanted
