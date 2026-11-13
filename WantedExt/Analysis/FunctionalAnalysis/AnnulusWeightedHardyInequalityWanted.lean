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

/-- **Open discs about the origin for the annulus Hardy inequality.** For a real number $r$,
$B_r = \{x \in \mathbb{R}^2 : |x| < r\}$ is the open disc of radius $r$ about the origin of the
Euclidean plane $\mathbb{R}^2$, where $|x|$ is the Euclidean norm. -/
abbrev B (r : ℝ) : Set R2 := Metric.ball (0 : R2) r

/-- **Full annulus of the weighted Hardy inequality.** $\Omega_1 = B_3 \setminus \overline{B}_1$,
where $B_r$ is the open disc of radius $r$ about the origin of the Euclidean plane $\mathbb{R}^2$
and $\overline{B}_1$ is the closure of $B_1$; that is, writing $|x|$ for the Euclidean norm,
$\Omega_1$ is the annulus $\{x \in \mathbb{R}^2 : 1 < |x| < 3\}$. -/
abbrev Omega1 : Set R2 := B 3 \ closure (B 1)

/-- **Outer annulus of the weighted Hardy inequality.** $\Omega_2 = B_3 \setminus \overline{B}_2$,
where $B_r$ is the open disc of radius $r$ about the origin of the Euclidean plane $\mathbb{R}^2$
and $\overline{B}_2$ is the closure of $B_2$; that is, writing $|x|$ for the Euclidean norm,
$\Omega_2$ is the annulus $\{x \in \mathbb{R}^2 : 2 < |x| < 3\}$. -/
abbrev Omega2 : Set R2 := B 3 \ closure (B 2)

/-- **Weight of the annulus Hardy inequality.** For $x$ in the Euclidean plane $\mathbb{R}^2$,
$\phi(x) = \max\{|x| - 1, 0\}$, where $|x|$ is the Euclidean norm; this is the distance from $x$
to the closed unit disc. -/
noncomputable def phi (x : R2) : ℝ := max (‖x‖ - 1) 0

/-- **Weighted Hardy inequality on the annulus.** For $r > 0$ let $B_r$ be the open disc of
radius $r$ about the origin of $\mathbb{R}^2$, let $|x|$ be the Euclidean norm, and let
$\phi(x) = \max\{|x| - 1, 0\}$ be the distance from $x$ to the closed unit disc. Let
$\Omega_1 = B_3 \setminus \overline{B}_1$ and $\Omega_2 = B_3 \setminus \overline{B}_2$, with
Lebesgue measure. For every real number $p \ge 1$ there is a constant $C > 0$ such that every
function $u \colon \mathbb{R}^2 \to \mathbb{R}$ that is continuously differentiable on $\Omega_1$,
and for which $\|\phi \, |\nabla u|\|_{L^p(\Omega_1)}$ and $\|u\|_{L^p(\Omega_2)}$ are finite,
satisfies
$$\|u\|_{L^p(\Omega_1)} \le C \|\phi \, |\nabla u|\|_{L^p(\Omega_1)} + C \|u\|_{L^p(\Omega_2)}.$$

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
