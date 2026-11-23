/-
# Iterates of an H->H self-map fixing i, with f(2i)=15i/8, converge to i

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_34.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_34 … := by sorry` into the Batteries `theorem_wanted`
`tendsto_iterate_two_mul_I_of_fixed_I`; moved the informal problem statement docstring onto it
and placed the declarations in namespace
`MathlibExt.Analysis.Complex.UpperHalfPlaneSelfMapIterateConvergesWanted`; replaced `import
Mathlib` by `public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.Complex.UpperHalfPlaneSelfMapIterateConvergesWanted

/-- **Iterates of a self-map of the upper half-plane fixing $i$.** Let
$\mathbb{H}=\{z\in\mathbb{C} : \mathrm{Im}\,z>0\}$ be the upper half-plane, and let $f$ be a
complex function that is holomorphic on $\mathbb{H}$, maps $\mathbb{H}$ into $\mathbb{H}$, and
satisfies $f(i)=i$ and $f(2i)=\frac{15}{8}i$. Then the iterates $f^{\circ n}(2i)$ converge to $i$
as $n\to\infty$, where $f^{\circ n}$ is the $n$-fold composite of $f$ with itself.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functions of a complex
variable; Geometric function theory), `benchmark/level2/ma_proofbench_l2_34.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted tendsto_iterate_two_mul_I_of_fixed_I
    (f : ℂ → ℂ)
    (hf_maps : ∀ z : ℂ, 0 < z.im → 0 < (f z).im)
    (hf_holo : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (hfi : f Complex.I = Complex.I)
    (hf2i : f (2 * Complex.I) = ((15 / (8 : ℂ)) * Complex.I)) :
    Filter.Tendsto (fun n : ℕ => (f^[n]) (2 * Complex.I)) Filter.atTop (nhds Complex.I)

end MathlibExt.Analysis.Complex.UpperHalfPlaneSelfMapIterateConvergesWanted
