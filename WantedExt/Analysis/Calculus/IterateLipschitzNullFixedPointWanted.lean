/-
# Fixed point when iterate Lipschitz constants tend to zero

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_74.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l1_74 … := by sorry` into the Batteries `theorem_wanted`
`exists_fixedPoint_of_iterate_lipschitz_tendsto_zero`; moved the informal problem statement
docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.Calculus.IterateLipschitzNullFixedPointWanted`; replaced `import Mathlib`
by `public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open Filter Topology

namespace MathlibExt.Analysis.Calculus.IterateLipschitzNullFixedPointWanted

/-- **Fixed points of maps whose iterates have null Lipschitz constants.** Let $X$ be a nonempty
complete metric space, let $f : X \to X$, and write $f^n$ for the $n$-th iterate of $f$. Let
$(q_n)_{n \in \mathbb{N}}$ be a sequence of nonnegative real numbers with $q_n \to 0$ such that
$d(f^n(x), f^n(y)) \le q_n \, d(x, y)$ for every $n \ge 1$ and all $x, y \in X$. Then $f$ has a
fixed point: there is $x \in X$ with $f(x) = x$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Operator theory; Nonlinear
operators and their properties), `benchmark/level1/ma_proofbench_l1_74.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted exists_fixedPoint_of_iterate_lipschitz_tendsto_zero
    (X : Type*) [MetricSpace X] [CompleteSpace X] [Nonempty X] (f : X → X) (q : ℕ → ℝ)
    (hq_nonneg : ∀ n : ℕ, 0 ≤ q n)
    (hLip : ∀ n : ℕ+, ∀ x y : X, dist ((f^[n]) x) ((f^[n]) y) ≤ q n * dist x y)
    (hq_null : Tendsto q atTop (𝓝 (0 : ℝ))) :
    ∃ x : X, f x = x

end MathlibExt.Analysis.Calculus.IterateLipschitzNullFixedPointWanted
