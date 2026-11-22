/-
# The Hilbert–Schmidt norm as an extended nonnegative real

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

Attribution and modification notice: factored out of the helper definitions of
openbmb/ma-proofbench at commit 31bab4c78fd1b0c464e767d62e9202163d1e9029,
`benchmark/level2/ma_proofbench_l2_68.lean` and `benchmark/level2/ma_proofbench_l2_98.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: the two files
shared a real-valued helper `hsNorm T u = Real.sqrt (∑' n, ‖T (u n)‖ ^ 2)`, which takes the
value `0` when the series diverges (so, for example, it assigned the identity operator
Hilbert–Schmidt norm `0`); it is replaced here by the single `ℝ≥0∞`-valued definition
`hsENNNorm` below, which is `⊤` exactly when the series of squares diverges, and both wanted
statements are phrased with it.
-/
module

public import Mathlib

@[expose] public section

open scoped BigOperators ENNReal

namespace MathlibExt.Analysis.OperatorTheory.HilbertSchmidtNorm

/-- The squared Hilbert–Schmidt norm of `T` computed in the family `u`, as an extended
nonnegative real: `∑' n, ‖T (u n)‖ ^ 2` in `ℝ≥0∞`. It is `⊤` exactly when the series of
squares diverges. -/
noncomputable def hsNormSq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H →L[ℝ] H) (u : ℕ → H) : ℝ≥0∞ :=
  ∑' n : ℕ, ENNReal.ofReal (‖T (u n)‖ ^ 2)

/-- The Hilbert–Schmidt norm of `T` computed in the family `u`, as an extended nonnegative
real: the square root of `hsNormSq T u` in `ℝ≥0∞`. In particular it is `⊤` for operators
that are not Hilbert–Schmidt in the family `u` (for example the identity operator with `u`
an orthonormal basis indexed by `ℕ`), never `0` by default of summability. -/
noncomputable def hsENNNorm
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H →L[ℝ] H) (u : ℕ → H) : ℝ≥0∞ :=
  hsNormSq T u ^ (1 / 2 : ℝ)

end MathlibExt.Analysis.OperatorTheory.HilbertSchmidtNorm
