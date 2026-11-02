/-
# Even C^2 function on [-a,a] is a C^1 function of x^2

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_11.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l1_11 … := by sorry` into the Batteries `theorem_wanted`
`exists_contDiffOn_comp_sq_of_even`; moved the informal problem statement docstring onto it and
placed the declarations in namespace `MathlibExt.Analysis.Calculus.EvenC2SquareFactorWanted`;
replaced `import Mathlib` by `public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open Set

namespace MathlibExt.Analysis.Calculus.EvenC2SquareFactorWanted

/-- **An even $C^2$ function is a $C^1$ function of $x^2$.** Let $a>0$ and let
$f : \mathbb{R} \to \mathbb{R}$ be twice continuously differentiable on $[-a,a]$ with $f(x)=f(-x)$
for all $x\in[-a,a]$. Then there is $g : \mathbb{R} \to \mathbb{R}$, continuously differentiable on
$[0,a^2]$, with $f(x)=g(x^2)$ for all $x\in[-a,a]$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Functions of
one variable), `benchmark/level1/ma_proofbench_l1_11.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted exists_contDiffOn_comp_sq_of_even (a : ℝ) (ha : 0 < a)
    (f : ℝ → ℝ)
    (hf_C2 : ContDiffOn ℝ 2 f (Icc (-a) a))
    (hf_even : ∀ x : ℝ, x ∈ Icc (-a) a → f x = f (-x)) :
    ∃ g : ℝ → ℝ,
      ContDiffOn ℝ 1 g (Icc 0 (a ^ (2 : ℕ))) ∧
      ∀ x : ℝ, x ∈ Icc (-a) a → f x = g (x ^ (2 : ℕ))

end MathlibExt.Analysis.Calculus.EvenC2SquareFactorWanted
