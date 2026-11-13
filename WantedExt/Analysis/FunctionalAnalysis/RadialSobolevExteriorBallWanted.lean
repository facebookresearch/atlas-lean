/-
# Radial Sobolev embedding W^{1,p} into L^q outside the unit ball

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_80.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_80 … := by sorry` into the Batteries `theorem_wanted`
`exists_eLpNorm_le_sobolev_of_radial_of_tsupport_subset_compl_closedBall`; moved the informal
problem statement docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.FunctionalAnalysis.RadialSobolevExteriorBallWanted`; replaced `import
Mathlib` by `public import Mathlib` under the module system; added docstrings to helper
definitions; corrected the statement: replaced `ContDiffOn ℝ ⊤` by `ContDiffOn ℝ ∞`; in current
Mathlib `⊤ = ω` means analytic, which made the statement vacuous for compactly supported radial
functions.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open MeasureTheory
open scoped ContDiff

namespace MathlibExt.Analysis.FunctionalAnalysis.RadialSobolevExteriorBallWanted

/-- **Real $n$-space with the Euclidean norm.** For a natural number $n$, $\mathbb{R}^n$ denotes the
$n$-dimensional real Euclidean space: real $n$-tuples with the Euclidean inner product and norm. -/
abbrev Rn (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

/-- **Closed unit ball of $\mathbb{R}^n$.** For a natural number $n$, the closed unit ball of
$\mathbb{R}^n$ is the set $\{x \in \mathbb{R}^n : \|x\| \le 1\}$, where $\|\cdot\|$ is the Euclidean
norm. -/
def ClosedUnitBall (n : ℕ) : Set (Rn n) := {x : Rn n | ‖x‖ ≤ 1}

/-- **Radial functions on $\mathbb{R}^n$.** A function $f \colon \mathbb{R}^n \to \mathbb{R}$ is
radial if $f(x) = f(y)$ for all $x, y \in \mathbb{R}^n$ with $\|x\| = \|y\|$, where $\|\cdot\|$ is
the Euclidean norm. -/
def IsRadial {n : ℕ} (f : Rn n → ℝ) : Prop :=
  ∀ x y : Rn n, ‖x‖ = ‖y‖ → f x = f y

/-- **Radial Sobolev embedding outside the unit ball.** Let $n \ge 2$, let $B$ be the closed unit
ball of $\mathbb{R}^n$, and let $1 < p < 2$ and $p \le q \le \infty$. Then there is a constant
$C > 0$ such that every radial function $f \colon \mathbb{R}^n \to \mathbb{R}$ that has compact
support, whose closed support is contained in $\mathbb{R}^n \setminus B$, and which is $C^\infty$
on $\mathbb{R}^n \setminus B$, satisfies

$$\|f\|_{L^q} \le C \left( \|f\|_{L^p} + \big\| |Df| \big\|_{L^p} \right),$$

where the norms are taken with respect to Lebesgue measure and $|Df(x)|$ is the operator norm of
the derivative of $f$ at $x$.

Smoothness here means $C^\infty$. The source's formal statement asked for real-analyticity
instead, which makes the claim vacuous: an analytic, radial, compactly supported $f$ vanishes
outside the ball.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis; Linear
function spaces and their duals), `benchmark/level2/ma_proofbench_l2_80.lean` at
openbmb/ma-proofbench@31bab4c, with the change above.
-/
public theorem_wanted exists_eLpNorm_le_sobolev_of_radial_of_tsupport_subset_compl_closedBall
  (n : ℕ)
  (hn : 2 ≤ n)
  (p q : ENNReal)
  (hp1 : 1 < p)
  (hp2 : p < 2)
  (hpq : p ≤ q) :
  ∃ C : ℝ, 0 < C ∧
    ∀ f : Rn n → ℝ,
      ContDiffOn ℝ ∞ f ((ClosedUnitBall n)ᶜ) →
      HasCompactSupport f →
      tsupport f ⊆ (ClosedUnitBall n)ᶜ →
      IsRadial f →
      eLpNorm f q volume ≤
        ENNReal.ofReal C *
          (eLpNorm f p volume +
            eLpNorm (fun x : Rn n => ‖fderiv ℝ f x‖) p volume)

end MathlibExt.Analysis.FunctionalAnalysis.RadialSobolevExteriorBallWanted
