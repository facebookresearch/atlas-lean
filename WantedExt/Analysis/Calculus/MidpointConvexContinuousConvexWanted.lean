/-
# Continuous midpoint-convex functions on an open interval are convex

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_61.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l1_61 … := by sorry` into the Batteries `theorem_wanted`
`convexOn_Ioo_of_continuousOn_of_midpoint_le`; moved the informal problem statement docstring
onto it and placed the declarations in namespace
`MathlibExt.Analysis.Calculus.MidpointConvexContinuousConvexWanted`; replaced `import Mathlib`
by `public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.Calculus.MidpointConvexContinuousConvexWanted

/-- **Continuous midpoint-convex functions are convex.** Let $a < b$ be real numbers and let
$\varphi : \mathbb{R} \to \mathbb{R}$ be continuous on $(a, b)$ and satisfy
$\varphi\bigl(\frac{x+y}{2}\bigr) \le \frac{\varphi(x) + \varphi(y)}{2}$ for all $x, y \in (a, b)$.
Then $\varphi$ is convex on $(a, b)$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Functions of
one variable), `benchmark/level1/ma_proofbench_l1_61.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted convexOn_Ioo_of_continuousOn_of_midpoint_le
    {a b : ℝ} (hab : a < b) (φ : ℝ → ℝ)
    (hcont : ContinuousOn φ (Set.Ioo a b))
    (hmiddle :
      ∀ ⦃x⦄, x ∈ Set.Ioo a b → ∀ ⦃y⦄, y ∈ Set.Ioo a b →
        φ ((x + y) / 2) ≤ (φ x + φ y) / 2) :
    ConvexOn ℝ (Set.Ioo a b) φ

end MathlibExt.Analysis.Calculus.MidpointConvexContinuousConvexWanted
