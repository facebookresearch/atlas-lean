/-
# f(x-y)g(y) is integrable on ℝ^{2d} for integrable f, g

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_72.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l1_72 … := by sorry` into the Batteries `theorem_wanted`
`integrable_comp_sub_mul_of_integrable_fin_append`; moved the informal problem statement
docstring onto it and placed the declarations in namespace
`MathlibExt.MeasureTheory.ConvolutionIntegrandIntegrableEuclideanWanted`; replaced `import
Mathlib` by `public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open MeasureTheory

namespace MathlibExt.MeasureTheory.ConvolutionIntegrandIntegrableEuclideanWanted

/-- **Integrability of the convolution integrand.** Let $d \in \mathbb{N}$ and let
$f, g : \mathbb{R}^d \to \mathbb{R}$ be Lebesgue integrable. Identify $\mathbb{R}^{2d}$ with
$\mathbb{R}^d \times \mathbb{R}^d$ by writing a point as $(x, y)$, where $x$ consists of its first
$d$ coordinates and $y$ of its last $d$ coordinates. Then the function
$(x, y) \mapsto f(x - y)\, g(y)$ is Lebesgue integrable on $\mathbb{R}^{2d}$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Measure and integration;
Classical measure theory), `benchmark/level1/ma_proofbench_l1_72.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted integrable_comp_sub_mul_of_integrable_fin_append
    {d : ℕ} {f g : (Fin d → ℝ) → ℝ}
    (hf : Integrable f) (hg : Integrable g) :
    Integrable (fun p : Fin (d + d) → ℝ =>
        f (fun i : Fin d => p (Fin.castAdd d i) - p (Fin.natAdd d i)) *
        g (fun i : Fin d => p (Fin.natAdd d i)))

end MathlibExt.MeasureTheory.ConvolutionIntegrandIntegrableEuclideanWanted
