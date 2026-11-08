/-
# Implicit function for x²y₁ + eˣ + y₂ = 0 near (1,-1)

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_43.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l1_43 … := by sorry` into the Batteries `theorem_wanted`
`exists_implicit_function_sq_mul_add_exp_add`; moved the informal problem statement docstring
onto it and placed the declarations in namespace
`MathlibExt.Analysis.Calculus.ImplicitFunctionExpExampleWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.Calculus.ImplicitFunctionExpExampleWanted

/-- Define $f$ in $R^3$ by

\[
f(x,y_1,y_2)=x^2y_1+e^x+y_2.
\]
Show that there exists a differentiable function $g$ in some neighborhood of $(1,-1)$ in $R^2$, such
that $g(1,-1)=0$ and
\[
f(g(y_1,y_2),y_1,y_2)=0.
\]

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Functions of
several variables), `benchmark/level1/ma_proofbench_l1_43.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted exists_implicit_function_sq_mul_add_exp_add
    (f : ℝ → ℝ → ℝ → ℝ) (hf : f = fun x y₁ y₂ => x ^ 2 * y₁ + Real.exp x + y₂) :
    ∃ (U : Set (ℝ × ℝ)), IsOpen U ∧ ((1, -1) ∈ U) ∧
      ∃ g : (ℝ × ℝ) → ℝ,
        DifferentiableOn ℝ g U ∧ g (1, -1) = 0 ∧ ∀ y ∈ U, f (g y) y.1 y.2 = 0

end MathlibExt.Analysis.Calculus.ImplicitFunctionExpExampleWanted
