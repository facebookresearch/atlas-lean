/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level1/ma_proofbench_l1_14.lean` (openbmb/ma-proofbench, commit
31bab4c78fd1b0c464e767d62e9202163d1e9029). The statement and its description are adapted
from the Level I problem `ma_proofbench_l1_14`.
Authors: L. Pu et al. (MA-ProofBench)
Licensed under the MIT License.

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

-- Preserve the complex topology instance in the original statement.
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# A nonzero entire power series with infinitely many zeros

The Taylor series of the complex sine at zero has linear coefficient one and vanishes
at each natural multiple of π.
-/

public section

namespace MathlibExt.Analysis.Complex.EntireSeriesInfiniteZerosWanted

/-- **A nonzero entire power series with infinitely many zeros.** There is a sequence
$(a_k)_{k \ge 0}$ of complex numbers, not all zero, such that the power series
$\sum_{k=0}^{\infty} a_k z^k$ converges absolutely for every $z \in \mathbb{C}$ and its sum
vanishes at infinitely many points $z \in \mathbb{C}$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Functions of a complex
variable; Entire and meromorphic functions of one complex variable, and related topics),
`benchmark/level1/ma_proofbench_l1_14.lean` at openbmb/ma-proofbench@31bab4c.
-/
theorem exists_entire_powerSeries_infinite_zeros : ∃ a : ℕ → ℂ,
      (∀ z : ℂ, Summable (fun k : ℕ => a k * z ^ k)) ∧
      Set.Infinite {z : ℂ | (∑' k : ℕ, a k * z ^ k) = 0} ∧
      (∃ k : ℕ, a k ≠ 0) := by
  let a (k : ℕ) : ℂ := (k.factorial : ℂ)⁻¹ * iteratedDeriv k Complex.sin 0
  have hs (z : ℂ) : HasSum (fun k : ℕ => a k * z ^ k) (Complex.sin z) := by
    simpa only [a, sub_zero, smul_eq_mul, mul_left_comm, mul_comm, mul_assoc] using
      Complex.hasSum_taylorSeries_of_entire Complex.differentiable_sin 0 z
  refine ⟨a, fun z => (hs z).summable, ?_, 1, ?_⟩
  · apply Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (n : ℂ) * Real.pi)
    · exact (mul_left_injective₀ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)).comp
        Nat.cast_injective
    · exact fun n => (hs _).tsum_eq.trans (Complex.sin_nat_mul_pi n)
  · simp [a, Complex.deriv_sin]

end MathlibExt.Analysis.Complex.EntireSeriesInfiniteZerosWanted
