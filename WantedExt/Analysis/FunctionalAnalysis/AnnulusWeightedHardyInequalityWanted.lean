/-
# Weighted Hardy-type inequality on the annulus 1 < |x| < 3

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_77.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_77 … := by sorry` into the Batteries `theorem_wanted`
`exists_eLpNorm_le_weighted_grad_add_outer_annulus`; moved the informal problem statement
docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.FunctionalAnalysis.AnnulusWeightedHardyInequalityWanted`; replaced `import
Mathlib` by `public import Mathlib` under the module system; added docstrings to helper
definitions.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open MeasureTheory

namespace MathlibExt.Analysis.FunctionalAnalysis.AnnulusWeightedHardyInequalityWanted

/-- The Euclidean plane. -/
abbrev R2 : Type := EuclideanSpace ℝ (Fin 2)

/-- The open ball of radius `r` about the origin of the plane. -/
abbrev B (r : ℝ) : Set R2 := Metric.ball (0 : R2) r

/-- The annulus `B 3 \ closure (B 1)`. -/
abbrev Omega1 : Set R2 := B 3 \ closure (B 1)

/-- The annulus `B 3 \ closure (B 2)`. -/
abbrev Omega2 : Set R2 := B 3 \ closure (B 2)

/-- `phi x = max (‖x‖ - 1) 0`. -/
noncomputable def phi (x : R2) : ℝ := max (‖x‖ - 1) 0

/-- Let $B_r$ denote the ball $B(0,r)$ in $\mathbb{R}^2$ centered at the origin with radius $r>0$.
Let $\phi(x)=\max\{|x|-1,0\}$ for $x\in\mathbb{R}^2$ be the distance function from the unit ball
$B_1$.

Let $1\le p<\infty$. Prove that there is a finite number $C>0$ so that
\[
\|u\|_{L^p(B_3\setminus \overline{B}_1)}\le C\|\phi\nabla u\|_{L^p(B_3\setminus
\overline{B}_1)}+C\|u\|_{L^p(B_3\setminus \overline{B}_2)}
\]
for all $u\in C^1(B_3\setminus \overline{B}_1)$ as long as the right hand side is finite.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis; Linear
function spaces and their duals), `benchmark/level2/ma_proofbench_l2_77.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted exists_eLpNorm_le_weighted_grad_add_outer_annulus
  (p : ℝ)
  (hp : 1 ≤ p) :
  ∃ C : ℝ, 0 < C ∧
    ∀ u : R2 → ℝ,
      ContDiffOn ℝ 1 u Omega1 →
      eLpNorm (fun x : R2 => phi x * ‖fderivWithin ℝ u Omega1 x‖)
          (ENNReal.ofReal p) (volume.restrict Omega1) ≠ ⊤ →
      eLpNorm u (ENNReal.ofReal p) (volume.restrict Omega2) ≠ ⊤ →
      eLpNorm u (ENNReal.ofReal p) (volume.restrict Omega1) ≤
        ENNReal.ofReal C *
            eLpNorm (fun x : R2 => phi x * ‖fderivWithin ℝ u Omega1 x‖)
              (ENNReal.ofReal p) (volume.restrict Omega1) +
          ENNReal.ofReal C * eLpNorm u (ENNReal.ofReal p) (volume.restrict Omega2)

end MathlibExt.Analysis.FunctionalAnalysis.AnnulusWeightedHardyInequalityWanted
