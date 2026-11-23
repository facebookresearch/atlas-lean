/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level1/ma_proofbench_l1_18.lean` (openbmb/ma-proofbench, commit 31bab4c).
MA-ProofBench supplies the partial-sum definition, theorem statement, and problem description.
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

public import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic.Linarith

/-!
# Reciprocals of partial sums of a positive sequence and its reciprocal

Each term satisfies $a_k + 1/a_k ≥ 2$, so the partial sums grow at least as fast as $2(n+1)$.
-/

@[expose] public section

open Filter Topology

namespace MathlibExt.Analysis.SpecificLimits.ReciprocalSumAddInvNullWanted

/-- **Partial sums of $a_k + 1/a_k$.** For a real sequence $(a_k)_{k \in \mathbb{N}}$, the sequence
$(x_n)_{n \in \mathbb{N}}$ is given by $x_n = \sum_{k=0}^{n} (a_k + 1/a_k)$ for $n \in \mathbb{N}$,
with the convention $1/0 = 0$. -/
noncomputable def xSeq (a : ℕ → ℝ) : ℕ → ℝ :=
  fun n ↦ ∑ k ∈ Finset.range (n + 1), (a k + (1 / a k))

/-- **The reciprocals of $\sum_{k=0}^{n} (a_k + 1/a_k)$ tend to zero.** Let
$(a_n)_{n \in \mathbb{N}}$ be a sequence of positive real numbers, and for $n \in \mathbb{N}$ let
$x_n = \sum_{k=0}^{n} (a_k + 1/a_k)$. Then $1/x_n \to 0$ as $n \to \infty$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Sequences, series, summability;
Convergence and divergence of infinite limiting processes),
`benchmark/level1/ma_proofbench_l1_18.lean` at openbmb/ma-proofbench@31bab4c.
-/
theorem tendsto_one_div_sum_add_inv_zero (a : ℕ → ℝ) (ha : ∀ n : ℕ, 0 < a n) :
    Tendsto (fun n ↦ 1 / xSeq a n) atTop (𝓝 0) := by
  have hterm (k : ℕ) : 2 ≤ a k + 1 / a k := by
    apply sub_le_iff_le_add'.mp
    apply (le_div_iff₀ (ha k)).mpr
    nlinarith [sq_nonneg (a k - 1)]
  have hbound (n : ℕ) : ((n + 1 : ℕ) : ℝ) * 2 ≤ xSeq a n := by
    simpa only [xSeq, Finset.card_range, nsmul_eq_mul] using
      (Finset.range (n + 1)).card_nsmul_le_sum _ 2 (fun k _ ↦ hterm k)
  have htop : Tendsto (xSeq a) atTop atTop := tendsto_atTop_mono hbound
    ((tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).atTop_mul_const zero_lt_two)
  simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp htop

end MathlibExt.Analysis.SpecificLimits.ReciprocalSumAddInvNullWanted
