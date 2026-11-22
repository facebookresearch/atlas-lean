/-
# Nonconstant holomorphic f with |f| = 1 on the circle covers the disc

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_25.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l1_25 … := by sorry` into the Batteries `theorem_wanted`
`ball_subset_image_of_norm_eq_one_on_sphere`; moved the informal problem statement docstring
onto it and placed the declarations in namespace
`MathlibExt.Analysis.Complex.UnimodularBoundaryImageContainsDiscWanted`; replaced `import
Mathlib` by `public import Mathlib` under the module system; corrected the statement: added the
hypothesis `IsPreconnected U`, without which the statement is false.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.Complex.UnimodularBoundaryImageContainsDiscWanted

/-- Let $f$ be non-constant and holomorphic in an open set containing the closed unit disc.

Show that if $|f(z)|=1$ whenever $|z|=1$, then the image of $f$ contains the unit disc.

Lean variant: the source statement is false for a disconnected `U` (take `U = ball 0 2 ∪ ball 10 1`
with `f = 1` on the first component and `f z = z` on the second), so the hypothesis `IsPreconnected
U`, the intended reading of `U` as a domain, is added.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Functions of a complex
variable; General properties of functions of one complex variable),
`benchmark/level1/ma_proofbench_l1_25.lean` at openbmb/ma-proofbench@31bab4c, with the change
above.
-/
public theorem_wanted ball_subset_image_of_norm_eq_one_on_sphere {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hUconn : IsPreconnected U)
    (hclosed : Metric.closedBall (0 : ℂ) 1 ⊆ U)
    (hf : DifferentiableOn ℂ f U)
    (hnonconst : ∃ z₁ ∈ U, ∃ z₂ ∈ U, f z₁ ≠ f z₂)
    (hboundary : ∀ z, z ∈ Metric.sphere (0 : ℂ) 1 → ‖f z‖ = 1) :
    Metric.ball (0 : ℂ) 1 ⊆ f '' U

end MathlibExt.Analysis.Complex.UnimodularBoundaryImageContainsDiscWanted
