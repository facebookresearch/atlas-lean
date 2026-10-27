/-
# ‖(T−z)ψ‖ ≥ d(z, N(T))‖ψ‖ for the numerical range N(T)

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_55.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_55 … := by sorry` into the Batteries `theorem_wanted`
`infDist_numericalRange_mul_norm_le_norm_sub_smul_apply`; moved the informal problem statement
docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.OperatorTheory.NumericalRangeDistanceLowerBoundWanted`; replaced `import
Mathlib` by `public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.OperatorTheory.NumericalRangeDistanceLowerBoundWanted

/-- Let $H$ be a complex Hilbert space, $T:H\to H$ be a bounded linear operator,
$\sigma(T)$ be the spectrum of $T$. We also define the numerical range of $T$ to be
\[
N(T):=\{(\psi,T\psi)\mid \psi\in H,\ \|\psi\|=1\}\subset\mathbb{C}
\]
where $(\cdot,\cdot)$ and $\|\cdot\|$ denote the inner product and the norm on $H$, respectively.

For any $\psi\in H$ and $z\in\mathbb{C}$, show that
\[
\|(T-z)\psi\|\ge d(z,N(T))\|\psi\|.
\]
Here $d(z,N(T))$ is the distance from $z$ to $N(T)$ in $\mathbb{C}$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Operator theory; General
theory of linear operators), `benchmark/level2/ma_proofbench_l2_55.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted infDist_numericalRange_mul_norm_le_norm_sub_smul_apply
  (H : Type*)
  [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]
  [CompleteSpace H]
  (T : H →L[ℂ] H)
  (N : Set ℂ)
  (hN : N = {w : ℂ | ∃ ψ : H, ‖ψ‖ = 1 ∧ inner ℂ ψ (T ψ) = w}) :
  ∀ ψ : H, ∀ z : ℂ,
    ‖(T - z • ContinuousLinearMap.id ℂ H) ψ‖ ≥ Metric.infDist z N * ‖ψ‖

end MathlibExt.Analysis.OperatorTheory.NumericalRangeDistanceLowerBoundWanted
