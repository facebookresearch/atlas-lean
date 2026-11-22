/-
# Convolutions and translates of f have the same L^1(T) closure

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_12.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_12 … := by sorry` into the Batteries `theorem_wanted`
`closure_convolution_set_eq_closure_translate_span`; moved the informal problem statement
docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.Fourier.ConvolutionTranslateClosureCircleWanted`; replaced `import Mathlib`
by `public import Mathlib` under the module system; added docstrings to helper definitions; made
the source's `Fact (0 < 2π)` instance file-local.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open MeasureTheory Topology
open scoped BigOperators Convolution

namespace MathlibExt.Analysis.Fourier.ConvolutionTranslateClosureCircleWanted

local instance : Fact (0 < (2 * Real.pi : ℝ)) := ⟨by nlinarith [Real.pi_pos]⟩

/-- The circle `ℝ / 2πℤ`. -/
abbrev T := AddCircle (2 * Real.pi)

/-- Fix $f \in L^1(T)$, where $T = \mathbb{R}/2\pi\mathbb{Z}$. For each $\tau \in T$, define
$f_\tau$, a translate of $f$ by $\tau$, using
\[
f_\tau(x) = f(x - \tau).
\]
Consider the sets $B_f$ and $M_f$ defined by
\[
B_f = \left\{ \sum_{i=1}^N a_i f_{\tau_i}(x) : N \in \mathbb{N}, a_i \in \mathbb{R}, \tau_i \in T
\right\}, \quad M_f = \{f * g : g \in L^1(T)\}.
\]
Show that $\overline{M_f} = \overline{B_f}$, where the overlines denote the $L^1(T)$-closures.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis;
Commutative Banach algebras and commutative topological algebras),
`benchmark/level2/ma_proofbench_l2_12.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted closure_convolution_set_eq_closure_translate_span
    (f : T → ℝ)
    (hf : MemLp f 1 (volume : Measure T))
    (Bf Mf : Set (Lp ℝ 1 (volume : Measure T)))
    (hBf : Bf =
      {u : Lp ℝ 1 (volume : Measure T) | ∃ N : ℕ, ∃ a : Fin N → ℝ, ∃ τ : Fin N → T,
          (u : T → ℝ) =ᵐ[(volume : Measure T)]
            (fun x : T => ∑ i : Fin N, a i * f (x - τ i))})
    (hMf : Mf =
      {u : Lp ℝ 1 (volume : Measure T) | ∃ g : T → ℝ, MemLp g 1 (volume : Measure T) ∧
          (u : T → ℝ) =ᵐ[(volume : Measure T)] (f ⋆ g)}) :
    closure Mf = closure Bf

end MathlibExt.Analysis.Fourier.ConvolutionTranslateClosureCircleWanted
