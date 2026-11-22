/-
# Linear maps on 𝒮(ℝ) commuting with x· and d/dx are scalars

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_54.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_54 … := by sorry` into the Batteries `theorem_wanted`
`exists_eq_smul_of_comp_mul_eq_of_comp_deriv_eq`; moved the informal problem statement docstring
onto it and placed the declarations in namespace
`MathlibExt.Analysis.Distribution.SchwartzCommutantMulDerivWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open MeasureTheory Filter

namespace MathlibExt.Analysis.Distribution.SchwartzCommutantMulDerivWanted

/-- Let $M:\mathcal{S}(\mathbb{R})\to\mathcal{S}(\mathbb{R})$ denote the map $(Mf)(x)=x f(x)$.
Suppose $T:\mathcal{S}(\mathbb{R})\to\mathcal{S}(\mathbb{R})$ is a linear map (with no boundedness
assumed) satisfying $TM=MT$ and $T\frac{d}{dx}=\frac{d}{dx}T$. Prove that there exists $c\in
\mathbb{C}$ such that $Tf=cf$ for all $f\in \mathcal{S}(\mathbb{R})$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Operator theory; General
theory of linear operators), `benchmark/level2/ma_proofbench_l2_54.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted exists_eq_smul_of_comp_mul_eq_of_comp_deriv_eq
    (T : SchwartzMap ℝ ℂ →ₗ[ℂ] SchwartzMap ℝ ℂ)
    (M : SchwartzMap ℝ ℂ →ₗ[ℂ] SchwartzMap ℝ ℂ)
    (hM : ∀ f : SchwartzMap ℝ ℂ, ∀ x : ℝ, M f x = (x : ℂ) * f x)
    (hTM : T.comp M = M.comp T)
    (hTd :
      T.comp (SchwartzMap.derivCLM ℂ ℂ).toLinearMap =
        (SchwartzMap.derivCLM ℂ ℂ).toLinearMap.comp T) :
    ∃ c : ℂ, ∀ f : SchwartzMap ℝ ℂ, T f = c • f

end MathlibExt.Analysis.Distribution.SchwartzCommutantMulDerivWanted
