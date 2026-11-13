/-
# SOT convergence iff WOT convergence of T_n and T_n*T_n

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_59.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_59 … := by sorry` into the Batteries `theorem_wanted`
`tendsto_apply_iff_tendsto_inner_and_tendsto_inner_adjoint_comp`; moved the informal problem
statement docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.OperatorTheory.StrongOperatorConvergenceIffWeakAndAdjointWanted`; replaced
`import Mathlib` by `public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open scoped Topology

namespace MathlibExt.Analysis.OperatorTheory.StrongOperatorConvergenceIffWeakAndAdjointWanted

/-- **Strong operator convergence characterized by weak operator convergence.** Let $H$ be a real
or complex Hilbert space with inner product $\langle \cdot, \cdot \rangle$, let
$(T_n)_{n \in \mathbb{N}}$ be a sequence of bounded linear operators on $H$, let $T$ be a bounded
linear operator on $H$, and write $S^*$ for the adjoint of an operator $S$. Then $T_n \to T$ in
the strong operator topology, that is, $T_n x \to T x$ for every $x \in H$, if and only if both
$T_n \to T$ in the weak operator topology, that is, $\langle y, T_n x \rangle \to
\langle y, T x \rangle$ for all $x, y \in H$, and $T_n^* T_n \to T^* T$ in the weak operator
topology, that is, $\langle y, T_n^* T_n x \rangle \to \langle y, T^* T x \rangle$ for all
$x, y \in H$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Operator theory; General
theory of linear operators), `benchmark/level2/ma_proofbench_l2_59.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted tendsto_apply_iff_tendsto_inner_and_tendsto_inner_adjoint_comp
    {𝕜 H : Type*}
    [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (Tn : ℕ → H →L[𝕜] H)
    (T : H →L[𝕜] H) :
    (∀ x : H, Filter.Tendsto (fun n => Tn n x) Filter.atTop (𝓝 (T x))) ↔
      (∀ x y : H, Filter.Tendsto (fun n => inner 𝕜 y (Tn n x)) Filter.atTop (𝓝 (inner 𝕜 y (T x)))) ∧
        (∀ x y : H, Filter.Tendsto (fun n => inner 𝕜 y (((Tn n).adjoint.comp (Tn n)) x))
            Filter.atTop (𝓝 (inner 𝕜 y ((T.adjoint.comp T) x))))

end MathlibExt.Analysis.OperatorTheory.StrongOperatorConvergenceIffWeakAndAdjointWanted
