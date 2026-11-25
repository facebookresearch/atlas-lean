/-
# Characterization of the unilateral shift on a separable Hilbert space

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

Attribution and modification notice: the statement below is taken from openbmb/ma-proofbench at
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_33.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_33 … := by sorry` into the Batteries `theorem_wanted`
`isShift_iff_isometry_iInf_range_pow_eq_bot_finrank_orthogonal_eq_one`; moved the informal
problem statement docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.OperatorTheory.UnilateralShiftCharacterizationWanted`; replaced `import
Mathlib` by `public import Mathlib` under the module system; added docstrings to helper
definitions; dropped the unused `CompleteSpace` instance argument of the helper `IsShift` (the
theorem keeps its own).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.OperatorTheory.UnilateralShiftCharacterizationWanted

/-- **Unilateral shift operator.** A bounded linear operator $T$ on a complex inner product
space $H$ is a unilateral shift if there is a Hilbert basis $(b_n)_{n \in \mathbb{N}}$ of $H$
such that $T b_n = b_{n+1}$ for every $n \in \mathbb{N}$. -/
def IsShift
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) : Prop :=
  ∃ b : HilbertBasis ℕ ℂ H, ∀ n : ℕ, T (b n) = b (n + 1)

/-- **Isometric characterization of the unilateral shift.** Let $H$ be a separable complex
Hilbert space, and call a bounded linear operator $T : H \to H$ a shift if there is an
orthonormal basis $(e_n)_{n \in \mathbb{N}}$ of $H$ with $T e_n = e_{n+1}$ for every
$n \in \mathbb{N}$. Then a bounded linear operator $T : H \to H$ is a shift if and only if the
following three conditions hold: $T$ is an isometry, that is,
$\langle T x, T y \rangle = \langle x, y \rangle$ for all $x, y \in H$; the ranges of the powers
of $T$ satisfy $\bigcap_{n \ge 1} \mathrm{Ran}(T^n) = \{0\}$; and the orthogonal complement
$(\mathrm{Ran}\, T)^\perp$ of the range of $T$ has dimension $1$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Operator theory; Special
classes of linear operators), `benchmark/level2/ma_proofbench_l2_33.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted isShift_iff_isometry_iInf_range_pow_eq_bot_finrank_orthogonal_eq_one
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (T : H →L[ℂ] H) :
    IsShift T ↔
      (∀ x y : H, inner ℂ (T x) (T y) = inner ℂ x y) ∧
        (⨅ n : ℕ, LinearMap.range (T.toLinearMap ^ (n + 1))) = ⊥ ∧
        Module.rank ℂ (T.rangeᗮ) = 1

end MathlibExt.Analysis.OperatorTheory.UnilateralShiftCharacterizationWanted
