/-
# Entire f, g with f^3 + g^3 = 1 are constant

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_61.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_61 … := by sorry` into the Batteries `theorem_wanted`
`entire_cube_add_cube_eq_one_const`; moved the informal problem statement docstring onto it and
placed the declarations in namespace
`MathlibExt.Analysis.Complex.EntireFermatCubicConstantWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.Complex.EntireFermatCubicConstantWanted

/-- Let $f$ and $g$ be entire functions such that
\[
f^3+g^3=1\quad \text{on } \mathbb{C}.
\]
Show that $f$ and $g$ are constant.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functions of a complex
variable; Entire and meromorphic functions of one complex variable, and related topics),
`benchmark/level2/ma_proofbench_l2_61.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted entire_cube_add_cube_eq_one_const
    (f g : ℂ → ℂ)
    (hf_entire : Differentiable ℂ f)
    (hg_entire : Differentiable ℂ g)
    (hfg : ∀ z : ℂ, f z ^ (3 : ℕ) + g z ^ (3 : ℕ) = 1) :
    ∃ a b : ℂ, (∀ z : ℂ, f z = a) ∧ (∀ z : ℂ, g z = b)

end MathlibExt.Analysis.Complex.EntireFermatCubicConstantWanted
