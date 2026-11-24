/-
# Convolution of two L^2 functions is continuous and vanishes at infinity

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_17.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_17 … := by sorry` into the Batteries `theorem_wanted`
`continuous_and_tendsto_cocompact_convolution_of_memLp_two`; moved the informal problem
statement docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.Fourier.L2ConvolutionContinuousVanishingWanted`; replaced `import Mathlib`
by `public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open MeasureTheory Filter

namespace MathlibExt.Analysis.Fourier.L2ConvolutionContinuousVanishingWanted

/-- **Convolution of two square-integrable functions is continuous and vanishes at infinity.**
Let $n$ be a natural number and let $f, g : \mathbb{R}^n \to \mathbb{C}$ be square-integrable.
Then the convolution $(f \ast g)(x) = \int_{\mathbb{R}^n} f(x - y) \, g(y) \, dy$ is a continuous
function of $x \in \mathbb{R}^n$, and $(f \ast g)(x) \to 0$ as $|x| \to \infty$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis; Linear
function spaces and their duals), `benchmark/level2/ma_proofbench_l2_17.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted continuous_and_tendsto_cocompact_convolution_of_memLp_two
    (n : ℕ) (f g : (Fin n → ℝ) → ℂ)
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    Continuous (fun x : Fin n → ℝ => ∫ y, f (x - y) * g y) ∧
    Filter.Tendsto (fun x : Fin n → ℝ => ∫ y, f (x - y) * g y)
      (Filter.cocompact (Fin n → ℝ)) (nhds 0)

end MathlibExt.Analysis.Fourier.L2ConvolutionContinuousVanishingWanted
