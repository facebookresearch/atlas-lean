/-
# Derivative bound at i for a self-map of the upper half plane

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_62.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_62 … := by sorry` into the Batteries `theorem_wanted`
`norm_deriv_I_le_sqrt_three_halves_of_mapsTo_upperHalfPlane`; moved the informal problem
statement docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.Complex.UpperHalfPlaneSelfMapDerivBoundWanted`; replaced `import Mathlib`
by `public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.Complex.UpperHalfPlaneSelfMapDerivBoundWanted

/-- Let $H=\{z\in\mathbb{C}\mid \mathrm{Im}(z)>0\}$ be the upper half plane, and let
$\zeta_n=\exp(2\pi i/n)$. Suppose $f:H\to H$ is analytic, and $f(\zeta_4)=\zeta_3$. Prove that
$|f'(\zeta_4)|\le \sqrt{3/2}$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functions of a complex
variable; Geometric function theory), `benchmark/level2/ma_proofbench_l2_62.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted norm_deriv_I_le_sqrt_three_halves_of_mapsTo_upperHalfPlane
    (f : ℂ → ℂ)
    (hf_holo : DifferentiableOn ℂ f UpperHalfPlane.upperHalfPlaneSet)
    (hf_maps : Set.MapsTo f UpperHalfPlane.upperHalfPlaneSet UpperHalfPlane.upperHalfPlaneSet)
    (hpoint : f Complex.I = Complex.exp ((2 * Real.pi * Complex.I) / 3)) :
    ‖deriv f Complex.I‖ ≤ Real.sqrt (3 / 2 : ℝ)

end MathlibExt.Analysis.Complex.UpperHalfPlaneSelfMapDerivBoundWanted
