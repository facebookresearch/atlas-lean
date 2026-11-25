/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level1/ma_proofbench_l1_26.lean` (openbmb/ma-proofbench, commit
31bab4c78fd1b0c464e767d62e9202163d1e9029): the statement of the finite zeros theorem.
Authors: L. Pu et al. (MA-ProofBench)
MIT License

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
public import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Finitely many zeros in a disc

The isolated zeros principle applies on the closed disc, including its boundary.
Compactness then gives finiteness on the closed disc and hence on the open disc.
-/

namespace MathlibExt.Analysis.Complex.FiniteZerosInDiscOfHolomorphicWanted

/-- **A holomorphic function not identically zero has finitely many zeros in a disc.** Let
$P \in \mathbb{C}$ and $r > 0$, write $D(P,r)$ for the open disc and $\overline{D}(P,r)$ for the
closed disc of center $P$ and radius $r$, and let $f : \mathbb{C} \to \mathbb{C}$ be holomorphic
on some open set containing $\overline{D}(P,r)$. If $f$ does not vanish identically on $D(P,r)$,
then $f$ has only finitely many zeros in $D(P,r)$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Functions of a complex
variable; General properties of functions of one complex variable),
`benchmark/level1/ma_proofbench_l1_26.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem finite_zeros_in_ball_of_not_identically_zero
    (f : ℂ → ℂ) (P : ℂ) (r : ℝ) (hr : 0 < r)
    (hhol : ∃ U : Set ℂ, IsOpen U ∧ Metric.closedBall P r ⊆ U ∧ DifferentiableOn ℂ f U)
    (hnot : ¬ ∀ z ∈ Metric.ball P r, f z = 0) :
    (Set.Finite {z : ℂ | z ∈ Metric.ball P r ∧ f z = 0}) := by
  obtain ⟨U, hU, hsub, hf⟩ := hhol
  have ha : AnalyticOnNhd ℂ f (Metric.closedBall P r) := (hf.analyticOnNhd hU).mono hsub
  push Not at hnot
  obtain ⟨w, hw, hfw⟩ := hnot
  have hne := ha.preimage_zero_mem_codiscreteWithin hfw (Metric.ball_subset_closedBall hw)
    (Metric.isConnected_closedBall hr.le)
  apply ((isCompact_closedBall P r).finite_sdiff_of_mem_codiscreteWithin hne).subset
  rintro z ⟨hz, hfz⟩
  exact ⟨Metric.ball_subset_closedBall hz, fun h => h hfz⟩

end MathlibExt.Analysis.Complex.FiniteZerosInDiscOfHolomorphicWanted
