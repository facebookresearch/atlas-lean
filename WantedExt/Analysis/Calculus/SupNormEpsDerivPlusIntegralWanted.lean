/-
# max|f| ≤ ε max|f'| + C_ε ∫|f| on [0,1]

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_49.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_49 … := by sorry` into the Batteries `theorem_wanted`
`exists_const_sSup_norm_le_mul_sSup_norm_deriv_add_mul_integral`; moved the informal problem
statement docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.Calculus.SupNormEpsDerivPlusIntegralWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.Calculus.SupNormEpsDerivPlusIntegralWanted

/-- **Sup norm on $[0,1]$ bounded by the derivative and the $L^1$ norm.** For every
$\varepsilon > 0$ there is a constant $C_\varepsilon > 0$ such that every function
$f : \mathbb{R} \to \mathbb{R}$ that is continuously differentiable on $[0,1]$ satisfies
$$\sup_{x \in [0,1]} |f(x)| \le
\varepsilon \sup_{x \in [0,1]} |f'(x)| + C_\varepsilon \int_0^1 |f(x)|\,dx.$$

At $x = 0$ and $x = 1$, $f'(x)$ is the two-sided derivative of $f$ on $\mathbb{R}$, taken to be $0$
where it does not exist; this does not change the supremum.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Real functions; Inequalities
in real analysis), `benchmark/level2/ma_proofbench_l2_49.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted exists_const_sSup_norm_le_mul_sSup_norm_deriv_add_mul_integral :
    ∀ ε > 0, ∃ Cε > 0, ∀ f : ℝ → ℝ,
      ContDiffOn ℝ 1 f (Set.Icc (0 : ℝ) 1) →
      sSup (Set.image (fun x => ‖f x‖) (Set.Icc (0 : ℝ) 1))
        ≤ ε * sSup (Set.image (fun x => ‖deriv f x‖) (Set.Icc (0 : ℝ) 1))
            + Cε * ∫ x in (0 : ℝ)..1, ‖f x‖

end MathlibExt.Analysis.Calculus.SupNormEpsDerivPlusIntegralWanted
