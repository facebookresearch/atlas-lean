/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level2/ma_proofbench_l2_98.lean` (openbmb/ma-proofbench,
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029), by L. Pu et al.
The theorem statement and its informal description are adapted from that file under the MIT
License, using the extended nonnegative Hilbert–Schmidt norm.

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

public import MathlibExt.Analysis.OperatorTheory.HilbertSchmidtNorm

/-!
# The Hilbert–Schmidt norm of a finite-rank operator

Expand the images of the Hilbert basis in an orthonormal basis of the range. Bessel's inequality
for the adjoint applied to each range basis vector bounds the squared Hilbert–Schmidt norm by
the rank times the squared operator norm.
-/

public section

open scoped RealInnerProductSpace

namespace MathlibExt.Analysis.OperatorTheory.HilbertSchmidtFiniteRankBoundWanted

private theorem hsNormSq_le_rank_mul_sq {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H →L[ℝ] H) (b : HilbertBasis ℕ ℝ H) [FiniteDimensional ℝ (H ⧸ T.ker)] :
    HilbertSchmidtNorm.hsNormSq T b ≤ ENNReal.ofReal (Module.finrank ℝ (H ⧸ T.ker) * ‖T‖ ^ 2) := by
  classical
  let e := T.toLinearMap.quotKerEquivRange
  let : FiniteDimensional ℝ T.range := e.finiteDimensional
  let v := stdOrthonormalBasis ℝ T.range
  have hcoords (i : ℕ) :
      ‖T (b i)‖ ^ 2 = ∑ j, ‖⟪b i, T.adjoint (v j : H)⟫‖ ^ 2 := by
    simp_rw [T.adjoint_inner_right]
    exact (v.sum_sq_norm_inner_left (T.rangeRestrict (b i))).symm
  have hnorm (j) : ‖T.adjoint (v j : H)‖ ≤ ‖T‖ := by
    have hv : ‖(v j : H)‖ = 1 := v.orthonormal.norm_eq_one j
    simpa only [LinearIsometryEquiv.norm_map, hv, mul_one] using T.adjoint.le_opNorm (v j : H)
  rw [HilbertSchmidtNorm.hsNormSq, ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  calc
    ∑ i ∈ s, ‖T (b i)‖ ^ 2 = ∑ j, ∑ i ∈ s, ‖⟪b i, T.adjoint (v j : H)⟫‖ ^ 2 := by
      simp_rw [hcoords]
      rw [Finset.sum_comm]
    _ ≤ ∑ j : Fin (Module.finrank ℝ T.range), ‖T‖ ^ 2 := by
      refine Finset.sum_le_sum fun j _ => ?_
      exact (b.orthonormal.sum_inner_products_le (T.adjoint (v j : H))).trans
        (pow_le_pow_left₀ (norm_nonneg _) (hnorm j) 2)
    _ = _ := by simp [e.finrank_eq]

/-- **The Hilbert–Schmidt norm of a finite-rank operator is controlled by its operator norm.**
There is a function $C$ from the natural numbers to the positive reals with the following
property. Let $H$ be an infinite-dimensional separable real Hilbert space, let
$(u_i)_{i \in \mathbb{N}}$ be a Hilbert basis of $H$, and let $T : H \to H$ be a bounded linear
operator such that the quotient $H/\ker T$ is finite-dimensional, of dimension $n$. Then the
Hilbert–Schmidt norm of $T$ computed in the basis $(u_i)$, taken in $[0,\infty]$, satisfies
$$\Big(\sum_{i \in \mathbb{N}} \|Tu_i\|^2\Big)^{1/2} \le C(n)\,\|T\|,$$
where $\|T\|$ is the operator norm of $T$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Operator theory; General
theory of linear operators), `benchmark/level2/ma_proofbench_l2_98.lean` at
openbmb/ma-proofbench@31bab4c.
-/
theorem exists_hsNorm_le_mul_opNorm_of_finiteDimensional_quotient_ker :
    ∃ C : ℕ → ℝ, (∀ n : ℕ, 0 < C n) ∧
      ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        [TopologicalSpace.SeparableSpace H] (_hH : ¬ FiniteDimensional ℝ H)
        (T : H →L[ℝ] H) (b : HilbertBasis ℕ ℝ H)
        [FiniteDimensional ℝ (H ⧸ T.ker)],
        HilbertSchmidtNorm.hsENNNorm T (⇑b) ≤
          ENNReal.ofReal (C (Module.finrank ℝ (H ⧸ T.ker)) * ‖T‖) := by
  refine ⟨fun n => max 1 (Real.sqrt n), fun n => lt_max_of_lt_left zero_lt_one, ?_⟩
  intro H _ _ _ _ _ T b _
  unfold HilbertSchmidtNorm.hsENNNorm
  refine (ENNReal.rpow_le_rpow (hsNormSq_le_rank_mul_sq T b) (by norm_num)).trans ?_
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
    Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

end MathlibExt.Analysis.OperatorTheory.HilbertSchmidtFiniteRankBoundWanted
