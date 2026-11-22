/-
# Self-convolution asymptotics of exp(−√|x|) on ℝ^2

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_90.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_90 … := by sorry` into the Batteries `theorem_wanted`
`tendsto_convolution_self_div_atTop_norm`; moved the informal problem statement docstring onto
it and placed the declarations in namespace
`MathlibExt.Analysis.SpecificLimits.ExpNegSqrtNormSelfConvolutionLimitWanted`; replaced `import
Mathlib` by `public import Mathlib` under the module system; added docstrings to helper
definitions.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open scoped Convolution

namespace MathlibExt.Analysis.SpecificLimits.ExpNegSqrtNormSelfConvolutionLimitWanted

/-- `f x = exp (-√‖x‖)` on the plane. -/
noncomputable def f : EuclideanSpace ℝ (Fin 2) → ℝ := fun x =>
  Real.exp (-(Real.sqrt ‖x‖))

/-- Define $f:\mathbb{R}^2\to\mathbb{R}$ as
\[
f(x)=e^{-\sqrt{\|x\|}},\qquad x\in\mathbb{R}^2
\]
where $\|x\|$ is the Euclidean norm of $x$ in $\mathbb{R}^2$. Prove
\[
\lim_{\|a\|\to+\infty}\frac{(f*f)(a)}{f(a)}=2\int_{\mathbb{R}^2}e^{-\sqrt{\|x\|}}\,dx,\qquad
x\in\mathbb{R}^2,\qquad a\in\mathbb{R}^2.
\]
Here the $*$ operation stands for the convolution.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis; Measures,
integration, derivative, holomorphy), `benchmark/level2/ma_proofbench_l2_90.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted tendsto_convolution_self_div_atTop_norm :
    Filter.Tendsto
      (fun a : EuclideanSpace ℝ (Fin 2) => ((f ⋆ f) a) / f a)
      (Filter.comap (fun a : EuclideanSpace ℝ (Fin 2) => ‖a‖) Filter.atTop)
      (nhds (2 * ∫ x : EuclideanSpace ℝ (Fin 2), f x))

end MathlibExt.Analysis.SpecificLimits.ExpNegSqrtNormSelfConvolutionLimitWanted
