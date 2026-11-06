/-
# H¹(ℝ³) bounded sequence has L²-bounded traces on z = 0

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_56.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_56 … := by sorry` into the Batteries `theorem_wanted`
`exists_bound_integral_sq_trace_of_integral_sq_add_fderiv_sq_le_one`; moved the informal problem
statement docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.FunctionalAnalysis.SobolevTraceR3PlaneBoundedWanted`; replaced `import
Mathlib` by `public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.SobolevTraceR3PlaneBoundedWanted

/-- **Sobolev trace bound on the plane $z = 0$ in $\mathbb{R}^3$.** Let $(f_n)_{n \in \mathbb{N}}$
be a sequence of continuously differentiable functions $\mathbb{R}^3 \to \mathbb{R}$, where
$\mathbb{R}^3$ has coordinates $(x, y, z)$ and the max norm. For $p \in \mathbb{R}^3$ write
$\|Df_n(p)\|$ for the operator norm of the derivative of $f_n$ at $p$, which equals
$|\partial_x f_n(p)| + |\partial_y f_n(p)| + |\partial_z f_n(p)|$, the sum of the absolute values
of the partial derivatives. Suppose that for every $n$ the function
$p \mapsto |f_n(p)|^2 + \|Df_n(p)\|^2$ is Lebesgue integrable on $\mathbb{R}^3$ with integral at
most $1$. Then there is a constant $C \ge 0$ such that for every $n$ the function
$(x, y) \mapsto |f_n(x, y, 0)|^2$ is Lebesgue integrable on $\mathbb{R}^2$ with integral at most
$C$.

Since $\|Df_n(p)\|$ is at least the Euclidean length $|\nabla f_n(p)|$ of the gradient, the
hypothesis implies the bound $\int_{\mathbb{R}^3} (|\nabla f_n|^2 + |f_n|^2) \le 1$ of the source
problem; conversely, if $f_n$ satisfies that bound, then $f_n / \sqrt{3}$ satisfies the hypothesis.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis; Linear
function spaces and their duals), `benchmark/level2/ma_proofbench_l2_56.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted exists_bound_integral_sq_trace_of_integral_sq_add_fderiv_sq_le_one
    (f : ℕ → ℝ × ℝ × ℝ → ℝ)
    (hC1 : ∀ n : ℕ, ContDiff ℝ 1 (f n))
    (henergy : ∀ n : ℕ,
      MeasureTheory.Integrable
      (fun x : ℝ × ℝ × ℝ => ‖f n x‖ ^ 2 + ‖fderiv ℝ (f n) x‖ ^ 2) MeasureTheory.volume ∧
      (∫ x : ℝ × ℝ × ℝ,
        (‖f n x‖ ^ 2 + ‖fderiv ℝ (f n) x‖ ^ 2) ∂MeasureTheory.volume) ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ,
        MeasureTheory.Integrable
        (fun p : ℝ × ℝ => ‖f n (p.1, p.2, 0)‖ ^ 2) MeasureTheory.volume ∧
        (∫ p : ℝ × ℝ, ‖f n (p.1, p.2, 0)‖ ^ 2 ∂MeasureTheory.volume) ≤ C

end MathlibExt.Analysis.FunctionalAnalysis.SobolevTraceR3PlaneBoundedWanted
