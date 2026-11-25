/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level2/ma_proofbench_l2_68.lean` (openbmb/ma-proofbench, commit 31bab4c):
Copyright (c) 2026 OpenBMB. Licensed under the MIT License, reproduced below.
Authors: L. Pu et al. (MA-ProofBench)

The theorem statement uses the extended nonnegative Hilbert–Schmidt norm to include divergence.

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

public import MathlibExt.Analysis.OperatorTheory.HilbertSchmidtNorm

public section

open scoped BigOperators

namespace MathlibExt.Analysis.OperatorTheory.NormApplyLeHilbertSchmidtNormWanted

/-- **The Hilbert–Schmidt norm bounds an operator on unit vectors.** Let $H$ be a real Hilbert
space, let $T : H \to H$ be a bounded linear operator, and let $(u_n)_{n \in \mathbb{N}}$ be an
orthonormal basis of $H$ indexed by the natural numbers. Let
$\|T\|_{\mathrm{HS}} = \bigl(\sum_{n} \|T u_n\|^2\bigr)^{1/2} \in [0, \infty]$ be the
Hilbert–Schmidt norm of $T$ computed in this basis; it is $\infty$ when the series diverges.
Then $\|Tx\| \le \|T\|_{\mathrm{HS}}$ for every $x \in H$ with $\|x\| = 1$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Operator theory; Special
classes of linear operators), `benchmark/level2/ma_proofbench_l2_68.lean` at
openbmb/ma-proofbench@31bab4c.
-/
theorem norm_apply_le_hsNorm_of_norm_eq_one
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H →L[ℝ] H)
    (u : HilbertBasis ℕ ℝ H) :
    ∀ x : H, ‖x‖ = 1 → ENNReal.ofReal ‖T x‖ ≤ HilbertSchmidtNorm.hsENNNorm T u := by
  intro x hx
  have hsum : HasSum (fun i => u.repr x i • T (u i)) (T x) := by
    simpa only [map_smul] using (u.hasSum_repr x).mapL T
  rw [HilbertSchmidtNorm.hsENNNorm, one_div, ENNReal.le_rpow_inv_iff (by norm_num),
    ENNReal.rpow_two, ← ENNReal.ofReal_pow (norm_nonneg _) 2]
  apply le_of_tendsto'
    ((ENNReal.continuous_ofReal.tendsto _).comp ((Filter.Tendsto.norm hsum).pow 2))
  intro s
  have hcoeff : ∑ i ∈ s, ‖u.repr x i‖ ^ 2 ≤ 1 := by
    simpa only [u.repr_apply_apply, hx, one_pow] using
      u.orthonormal.sum_inner_products_le (s := s) x
  have hpartial : ‖∑ i ∈ s, u.repr x i • T (u i)‖ ^ 2 ≤ ∑ i ∈ s, ‖T (u i)‖ ^ 2 := calc
    _ ≤ (∑ i ∈ s, ‖u.repr x i‖ * ‖T (u i)‖) ^ 2 := by
      gcongr
      simpa only [norm_smul] using norm_sum_le s (fun i => u.repr x i • T (u i))
    _ ≤ (∑ i ∈ s, ‖u.repr x i‖ ^ 2) * ∑ i ∈ s, ‖T (u i)‖ ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq s _ _
    _ ≤ 1 * ∑ i ∈ s, ‖T (u i)‖ ^ 2 := by gcongr
    _ = _ := one_mul _
  refine (ENNReal.ofReal_le_ofReal hpartial).trans ?_
  rw [ENNReal.ofReal_sum_of_nonneg fun i _ => sq_nonneg _]
  exact ENNReal.sum_le_tsum s

end MathlibExt.Analysis.OperatorTheory.NormApplyLeHilbertSchmidtNormWanted
