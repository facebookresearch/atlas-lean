/-
# sum of sin^2(n delta)/(n^2 delta) equals (pi - delta)/2

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_03.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l1_03 … := by sorry` into the Batteries `theorem_wanted`
`tsum_sin_sq_mul_div_sq_mul`; moved the informal problem statement docstring onto it and placed
the declarations in namespace `MathlibExt.Analysis.SpecificLimits.SumSinSqDivSqWanted`; replaced
`import Mathlib` by `public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.SpecificLimits.SumSinSqDivSqWanted

/-- **A closed form for $\sum \sin^2(n\delta)/(n^2\delta)$.** For every real $\delta$ with
$0 < \delta < \pi$,

$$\sum_{n=1}^{\infty} \frac{\sin^2(n\delta)}{n^2\delta} = \frac{\pi - \delta}{2}.$$

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Sequences, series, summability;
Convergence and divergence of infinite limiting processes),
`benchmark/level1/ma_proofbench_l1_03.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted tsum_sin_sq_mul_div_sq_mul
    {δ : ℝ} (hδ0 : 0 < δ) (hδpi : δ < Real.pi) :
    (∑' n : ℕ,
        (Real.sin ((n + 1 : ℕ) * δ)) ^ 2 / (((n + 1 : ℕ) ^ 2) * δ))
      = (Real.pi - δ) / 2

end MathlibExt.Analysis.SpecificLimits.SumSinSqDivSqWanted
