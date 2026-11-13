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

/-- **The circle $\mathbb{R}/2\pi\mathbb{Z}$.** The circle $T = \mathbb{R}/2\pi\mathbb{Z}$, the
quotient of the additive group $\mathbb{R}$ by its subgroup $2\pi\mathbb{Z}$. -/
abbrev T := AddCircle (2 * Real.pi)

/-- **Convolutions and linear combinations of translates have the same closure.** Let
$T = \mathbb{R}/2\pi\mathbb{Z}$ with the measure induced by Lebesgue measure on $[0, 2\pi)$, and
let $L^1(T)$ be the space of real-valued integrable functions on $T$ modulo equality almost
everywhere. Fix a real-valued integrable $f$ on $T$. Let $B_f \subseteq L^1(T)$ be the set of
classes of the finite linear combinations of translates
$x \mapsto \sum_{i=1}^N a_i f(x - \tau_i)$ with $N \in \mathbb{N}$, $a_i \in \mathbb{R}$ and
$\tau_i \in T$, and let $M_f \subseteq L^1(T)$ be the set of classes of the convolutions
$(f * g)(x) = \int_T f(y)\, g(x - y)\,dy$ with $g$ real-valued and integrable on $T$. Then $M_f$
and $B_f$ have the same closure in $L^1(T)$.

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
