/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level1/ma_proofbench_l1_46.lean` (openbmb/ma-proofbench, commit 31bab4c).
The theorem statement and problem description are adapted from MA-ProofBench.
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

public import Mathlib.Analysis.PSeries
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Convergence of an alternating weighted series in the plane

Swapping the coordinates preserves the product norm, so the norms of the weighted terms
form a constant multiple of the summable inverse-square series.
-/

public section

open Filter Topology

namespace MathlibExt.Analysis.SpecificLimits.AlternatingPairWeightedSeriesConvergesWanted

/-- **Convergence of an alternating weighted series in the plane.** Let $\alpha$ and $\beta$ be
real numbers. For $k \in \mathbb{N}$ let $x_k = (\alpha, \beta) \in \mathbb{R} \times \mathbb{R}$
if $k$ is even and $x_k = (\beta, \alpha)$ if $k$ is odd. For $n \in \mathbb{N}$ let
$s_n = \sum_{k=1}^{n} k^{-2} x_k$ (so $s_0 = 0$). Then the sequence $(s_n)$ converges in
$\mathbb{R} \times \mathbb{R}$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Sequences, series, summability;
Convergence and divergence of infinite limiting processes),
`benchmark/level1/ma_proofbench_l1_46.lean` at openbmb/ma-proofbench@31bab4c.
-/
theorem exists_tendsto_sum_inv_sq_smul_alternating_pair
    (α β : ℝ) (x s : ℕ → (ℝ × ℝ))
    (hx : ∀ k : ℕ, x k = if Even k then (α, β) else (β, α))
    (hs : ∀ n : ℕ, s n = ∑ k ∈ Finset.Icc (1 : ℕ) n,
        (1 / ((k : ℝ) ^ 2)) • x k) :
    ∃ L : (ℝ × ℝ), Tendsto s atTop (𝓝 L) := by
  have hweight := Real.summable_one_div_nat_pow.mpr (one_lt_two : 1 < 2)
  let term (k : ℕ) := (1 / (k : ℝ) ^ 2) • x k
  have hseries : Summable term := by
    apply (hweight.mul_right (max ‖α‖ ‖β‖)).of_norm_bounded
    intro k
    dsimp only [term]
    rw [norm_smul, Real.norm_of_nonneg (by positivity), hx k]
    split <;> simp [max_comm]
  have hshift := (summable_nat_add_iff 1).mpr hseries
  refine ⟨_, hshift.hasSum.tendsto_sum_nat.congr fun n ↦ ?_⟩
  rw [hs, Finset.range_eq_Ico, Finset.sum_Ico_add' term 0 n 1]
  simp only [zero_add, Finset.Ico_add_one_right_eq_Icc, term]

end MathlibExt.Analysis.SpecificLimits.AlternatingPairWeightedSeriesConvergesWanted
