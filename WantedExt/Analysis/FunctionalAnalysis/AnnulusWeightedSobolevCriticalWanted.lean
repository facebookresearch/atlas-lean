/-
# Weighted Sobolev inequality on the annulus 1 < |x| < 3

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_65.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_65 … := by sorry` into the Batteries `theorem_wanted`
`exists_eLpNorm_phi_mul_le_weighted_grad_add_outer_annulus`; moved the informal problem
statement docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.FunctionalAnalysis.AnnulusWeightedSobolevCriticalWanted`; replaced `import
Mathlib` by `public import Mathlib` under the module system; added docstrings to helper
definitions.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open MeasureTheory

namespace MathlibExt.Analysis.FunctionalAnalysis.AnnulusWeightedSobolevCriticalWanted

/-- **The plane of the critical weighted Sobolev inequality.** $\mathbb{R}^2$ denotes the Euclidean
plane, the space of pairs of real numbers with the Euclidean norm. -/
abbrev R2 : Type := EuclideanSpace ℝ (Fin 2)

/-- **Discs about the origin for the critical weighted Sobolev inequality.** For a real number $r$,
$B_r$ is the open disc $\{x \in \mathbb{R}^2 : |x| < r\}$ of radius $r$ about the origin of the
Euclidean plane $\mathbb{R}^2$. -/
abbrev B (r : ℝ) : Set R2 := Metric.ball (0 : R2) r

/-- **The annulus of the critical weighted Sobolev inequality.** Let $B_r$ denote the open disc of
radius $r$ about the origin of the Euclidean plane $\mathbb{R}^2$. The annulus $\Omega_1$ is
$B_3 \setminus \overline{B}_1$, the set of points of $B_3$ outside the closure of $B_1$, that is,
$\Omega_1 = \{x \in \mathbb{R}^2 : 1 < |x| < 3\}$. -/
abbrev Omega1 : Set R2 := B 3 \ closure (B 1)

/-- **The outer annulus of the critical weighted Sobolev inequality.** Let $B_r$ denote the open
disc of radius $r$ about the origin of the Euclidean plane $\mathbb{R}^2$. The outer annulus
$\Omega_2$ is $B_3 \setminus \overline{B}_2$, the set of points of $B_3$ outside the closure of
$B_2$, that is, $\Omega_2 = \{x \in \mathbb{R}^2 : 2 < |x| < 3\}$. -/
abbrev Omega2 : Set R2 := B 3 \ closure (B 2)

/-- **The weight of the critical weighted Sobolev inequality.** For $x$ in the Euclidean plane
$\mathbb{R}^2$, the weight is $\phi(x) = \max\{|x| - 1, 0\}$, the distance from $x$ to the closed
unit disc. -/
noncomputable def phi (x : R2) : ℝ := max (‖x‖ - 1) 0

/-- **Sobolev conjugate exponent in dimension two.** For a real number $p$, the Sobolev conjugate
exponent is $p^* = 2p/(2 - p)$ (at $p = 2$, where the denominator vanishes, this is $0$ by the
convention that division by zero gives zero). -/
noncomputable def pStar (p : ℝ) : ℝ := 2 * p / (2 - p)

/-- **Critical weighted Sobolev inequality on an annulus.** For $r > 0$ let $B_r$ be the open disc
of radius $r$ about the origin in the Euclidean plane $\mathbb{R}^2$, let
$\Omega_1 = B_3 \setminus \overline{B}_1$ and $\Omega_2 = B_3 \setminus \overline{B}_2$, and let
$\phi(x) = \max\{|x| - 1, 0\}$, the distance from $x$ to the closed unit disc. Let $1 \le p < 2$
and $p^* = 2p/(2-p)$. Then there is a real number $C > 0$ such that every function
$u \colon \mathbb{R}^2 \to \mathbb{R}$ that is continuously differentiable on $\Omega_1$ and for
which $\|\phi \nabla u\|_{L^p(\Omega_1)}$ and $\|u\|_{L^p(\Omega_2)}$ are finite satisfies

$$\|\phi u\|_{L^{p^*}(\Omega_1)} \le C\|\phi \nabla u\|_{L^p(\Omega_1)} + C\|u\|_{L^p(\Omega_2)}.$$

Here the norms are taken with respect to Lebesgue measure, $\|\phi \nabla u\|_{L^p(\Omega_1)}$ is
the $L^p(\Omega_1)$ norm of $x \mapsto \phi(x)\,|\nabla u(x)|$, and $\nabla u(x)$ is the derivative
of $u$ at $x$ within $\Omega_1$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis; Linear
function spaces and their duals), `benchmark/level2/ma_proofbench_l2_65.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted exists_eLpNorm_phi_mul_le_weighted_grad_add_outer_annulus
  (p : ℝ)
  (hp₁ : 1 ≤ p)
  (hp₂ : p < 2) :
  ∃ C : ℝ, 0 < C ∧
    ∀ u : R2 → ℝ,
      ContDiffOn ℝ 1 u Omega1 →
      eLpNorm (fun x : R2 => phi x * ‖fderivWithin ℝ u Omega1 x‖)
          (ENNReal.ofReal p) (volume.restrict Omega1) ≠ ⊤ →
      eLpNorm u (ENNReal.ofReal p) (volume.restrict Omega2) ≠ ⊤ →
      eLpNorm (fun x : R2 => phi x * u x) (ENNReal.ofReal (pStar p))
          (volume.restrict Omega1) ≤
        ENNReal.ofReal C *
            eLpNorm (fun x : R2 => phi x * ‖fderivWithin ℝ u Omega1 x‖)
              (ENNReal.ofReal p) (volume.restrict Omega1) +
          ENNReal.ofReal C * eLpNorm u (ENNReal.ofReal p) (volume.restrict Omega2)

end MathlibExt.Analysis.FunctionalAnalysis.AnnulusWeightedSobolevCriticalWanted
