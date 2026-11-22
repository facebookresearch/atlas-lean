/-
# n∬f(x)f(y)e^{−2n|x−y|} → ∫f² for f ∈ L²

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_96.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_96 … := by sorry` into the Batteries `theorem_wanted`
`tendsto_mul_integral_integral_exp_neg_two_mul_abs_sub`; moved the informal problem statement
docstring onto it and placed the declarations in namespace
`MathlibExt.MeasureTheory.ExponentialKernelApproxIdentityWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.MeasureTheory.ExponentialKernelApproxIdentityWanted

/-- **Exponential kernel approximate identity.** For every function $f : \mathbb{R} \to \mathbb{R}$
in $L^2(\mathbb{R})$,
$$
\lim_{n\to\infty} n\int_{\mathbb{R}}\int_{\mathbb{R}} f(x)f(y)e^{-2n|x-y|}\,dy\,dx
= \int_{\mathbb{R}} f(x)^2\,dx,
$$
where $n$ runs through the natural numbers and the integrals are with respect to Lebesgue measure.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Measure and integration;
Classical measure theory), `benchmark/level2/ma_proofbench_l2_96.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted tendsto_mul_integral_integral_exp_neg_two_mul_abs_sub
  (f : ℝ → ℝ)
  (hf : MeasureTheory.MemLp f 2 MeasureTheory.volume) :
  Filter.Tendsto
    (fun n : ℕ =>
      (n : ℝ) * (∫ x : ℝ, ∫ y : ℝ, f x * f y * Real.exp (-2 * (n : ℝ) * |x - y|)))
    Filter.atTop
    (nhds (∫ x : ℝ, f x ^ (2 : ℕ)))

end MathlibExt.MeasureTheory.ExponentialKernelApproxIdentityWanted
