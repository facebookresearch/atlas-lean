/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level1/ma_proofbench_l1_09.lean` (openbmb/ma-proofbench, commit
31bab4c78fd1b0c464e767d62e9202163d1e9029): the definition of the lacunary series and
the statement of its regularity theorem.
Authors: L. Pu et al. (MA-ProofBench)
Licensed under the MIT License.

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
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Regularity of a lacunary series on the unit disc

On the closed unit disc, the terms are bounded in norm by the summable geometric
sequence `(1 / 2) ^ j`. Thus the monomials sum uniformly there and their sum is
holomorphic on the open disc.
-/

@[expose] public section

namespace MathlibExt.Analysis.Complex.LacunarySeriesDiscWanted

/-- **A lacunary power series.** For $z \in \mathbb{C}$, let
$f(z) = \sum_{j=0}^{\infty} 2^{-j} z^{2^j}$, where $f(z)$ is taken to be $0$ when the series is
not summable. -/
noncomputable def f (z : ℂ) : ℂ :=
  ∑' j : ℕ, ((1 / (2 : ℂ)) ^ j) * z ^ (2 ^ j)

/-- **Regularity of a lacunary series on the unit disc.** Let $f$ be the lacunary series
$f(z) = \sum_{j=0}^{\infty} 2^{-j} z^{2^j}$. Then $f$ is holomorphic on the open unit disc
$\{z \in \mathbb{C} : |z| < 1\}$ and continuous on its closure, the closed unit disc
$\{z \in \mathbb{C} : |z| \le 1\}$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Functions of a complex
variable; Series expansions of functions of one complex variable),
`benchmark/level1/ma_proofbench_l1_09.lean` at openbmb/ma-proofbench@31bab4c.
-/
theorem differentiableOn_ball_continuousOn_closedBall_lacunary :
    DifferentiableOn ℂ f (Metric.ball 0 1) ∧
      ContinuousOn f (closure (Metric.ball 0 1)) := by
  let term (j : ℕ) (z : ℂ) := (1 / (2 : ℂ)) ^ j * z ^ (2 ^ j)
  have hdiff (j : ℕ) : Differentiable ℂ (term j) :=
    (differentiable_id.pow (2 ^ j)).const_mul _
  have hbound (j : ℕ) (z : ℂ) (hz : z ∈ Metric.closedBall 0 1) :
      ‖term j z‖ ≤ (1 / (2 : ℝ)) ^ j := by
    simp only [term, norm_mul, norm_pow, norm_div, norm_one, Complex.norm_two]
    exact mul_le_of_le_one_right (by positivity)
      (pow_le_one₀ (norm_nonneg z) (mem_closedBall_zero_iff.mp hz))
  constructor
  · exact Complex.differentiableOn_tsum_of_summable_norm summable_geometric_two
      (fun j => (hdiff j).differentiableOn) Metric.isOpen_ball
      (fun j z hz => hbound j z (Metric.ball_subset_closedBall hz))
  · rw [closure_ball 0 one_ne_zero]
    exact continuousOn_tsum (fun j => (hdiff j).continuous.continuousOn)
      summable_geometric_two hbound

end MathlibExt.Analysis.Complex.LacunarySeriesDiscWanted
