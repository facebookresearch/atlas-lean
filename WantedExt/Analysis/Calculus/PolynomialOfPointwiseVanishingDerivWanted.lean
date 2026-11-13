/-
# Smooth function with some vanishing derivative at each point is polynomial

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_81.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_81 … := by sorry` into the Batteries `theorem_wanted`
`exists_polynomial_eq_of_forall_exists_iteratedDerivWithin_eq_zero`; moved the informal problem
statement docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.Calculus.PolynomialOfPointwiseVanishingDerivWanted`; replaced `import
Mathlib` by `public import Mathlib` under the module system; corrected the statement: replaced
`ContDiffOn ℝ ⊤` (analytic in current Mathlib) by `ContDiffOn ℝ ∞` and `iteratedDeriv` by
`iteratedDerivWithin … (Icc 0 1)`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open Set
open scoped ContDiff

namespace MathlibExt.Analysis.Calculus.PolynomialOfPointwiseVanishingDerivWanted

/-- **A smooth function on the unit interval with some vanishing derivative at each point is a
polynomial there.** Let $f : \mathbb{R} \to \mathbb{R}$ be infinitely differentiable on $[0, 1]$,
and suppose that for every $x \in [0, 1]$ there is an integer $n \ge 0$ such that the $n$-th
derivative of $f$ within $[0, 1]$ vanishes at $x$ (at the endpoints these derivatives are
one-sided). Then there is a polynomial $p$ with real coefficients such that $f(x) = p(x)$ for
every $x \in [0, 1]$.

Smoothness means infinite differentiability here, not real analyticity: the source's formal
statement assumed real analyticity, which reduces the problem to the identity theorem.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Real functions; Functions of
one variable), `benchmark/level2/ma_proofbench_l2_81.lean` at openbmb/ma-proofbench@31bab4c,
with the change above.
-/
public theorem_wanted exists_polynomial_eq_of_forall_exists_iteratedDerivWithin_eq_zero (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ ∞ f (Icc (0 : ℝ) 1))
    (hvanish : ∀ x ∈ Icc (0 : ℝ) 1, ∃ n : ℕ, iteratedDerivWithin n f (Icc (0 : ℝ) 1) x = 0) :
    ∃ p : Polynomial ℝ, ∀ x ∈ Icc (0 : ℝ) 1, f x = p.eval x

end MathlibExt.Analysis.Calculus.PolynomialOfPointwiseVanishingDerivWanted
