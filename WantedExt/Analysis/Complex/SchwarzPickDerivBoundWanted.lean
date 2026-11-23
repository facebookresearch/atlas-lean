/-
# Schwarz-Pick derivative inequality on the unit disc

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_86.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l1_86 … := by sorry` into the Batteries `theorem_wanted`
`norm_deriv_div_one_sub_sq_le_of_mapsTo_unitBall`; moved the informal problem statement
docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.Complex.SchwarzPickDerivBoundWanted`; replaced `import Mathlib` by `public
import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.Complex.SchwarzPickDerivBoundWanted

/-- **Schwarz–Pick lemma, derivative form.** Let $\mathbb{D}=\{z\in\mathbb{C}:|z|<1\}$ be the open
unit disc. If $f:\mathbb{D}\to\mathbb{D}$ is holomorphic, then

\[
\frac{|f'(z)|}{1-|f(z)|^2}\le \frac{1}{1-|z|^2}\qquad\text{for all } z\in\mathbb{D}.
\]

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Functions of a complex
variable; Geometric function theory), `benchmark/level1/ma_proofbench_l1_86.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted norm_deriv_div_one_sub_sq_le_of_mapsTo_unitBall (f : ℂ → ℂ)
    (hf_holo : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hf_maps : Set.MapsTo f (Metric.ball 0 1) (Metric.ball 0 1)) :
    ∀ z : ℂ, z ∈ Metric.ball 0 1 →
      norm (deriv f z) / (1 - (norm (f z)) ^ 2)
        ≤ 1 / (1 - (norm z) ^ 2)

end MathlibExt.Analysis.Complex.SchwarzPickDerivBoundWanted
