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

/-- `T` is a unilateral shift: it maps some Hilbert basis `b` by `b n ↦ b (n + 1)`. -/
def IsShift
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) : Prop :=
  ∃ b : HilbertBasis ℕ ℂ H, ∀ n : ℕ, T (b n) = b (n + 1)

/-- Let $H$ be a separable Hilbert space. We say that a bounded linear operator $T : H \to H$ is a
shift if there exists an orthonormal basis $\{e_n\}_{n=1}^{\infty}$ of $H$ such that $T(e_n) =
e_{n+1}$ for every $n \in \mathbb{Z}_{\ge 1}$.
Prove that a linear operator $T : H \to H$ is a shift if and only if $T$ is a Hilbert space
isomorphism (i.e., $\langle T x, T y\rangle = \langle x, y\rangle$ for all $x, y \in H$) satisfying
$\bigcap_{n=1}^{\infty} \mathrm{Ran}(T^n) = \{0\}$ and $\dim(\mathrm{Ran}(T))^\perp = 1$.

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
