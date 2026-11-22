/-
# Schwarz lemma on the upper half-plane with a zero at i

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_20.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l1_20 … := by sorry` into the Batteries `theorem_wanted`
`norm_le_norm_cayley_of_upperHalfPlane_bounded_vanishing_at_I`; moved the informal problem
statement docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.Complex.UpperHalfPlaneSchwarzLemmaWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.Complex.UpperHalfPlaneSchwarzLemmaWanted

/-- **Schwarz lemma on the upper half-plane.** Let
$\mathbb{H}=\{z\in\mathbb{C} : \mathrm{Im}\,z>0\}$ be the upper half-plane, and let $F$ be a
complex function that is holomorphic on $\mathbb{H}$, satisfies $|F(z)|\le 1$ for every
$z\in\mathbb{H}$, and vanishes at $i$. Then for every $z\in\mathbb{H}$,
$$|F(z)|\le\left|\frac{z-i}{z+i}\right|.$$

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Functions of a complex
variable; Geometric function theory), `benchmark/level1/ma_proofbench_l1_20.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted norm_le_norm_cayley_of_upperHalfPlane_bounded_vanishing_at_I (F : ℂ → ℂ)
    (hHolo : DifferentiableOn ℂ F {z : ℂ | 0 < z.im})
    (hBound : ∀ z, 0 < z.im → norm (F z) ≤ 1)
    (hFi : F Complex.I = 0) :
    ∀ z : ℂ, 0 < z.im →
      norm (F z) ≤ norm ((z - Complex.I) / (z + Complex.I))

end MathlibExt.Analysis.Complex.UpperHalfPlaneSchwarzLemmaWanted
