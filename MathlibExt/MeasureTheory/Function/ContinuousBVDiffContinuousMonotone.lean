/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
# Continuous BV function is a difference of continuous monotone functions

The following OpenBMB notice applies to the adapted statement and its documentation.

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_33.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782), distributed under the MIT License above.
See also the Hugging Face dataset openbmb/MA-ProofBench. Changes made: converted
`theorem ma_proofbench_l1_33 … := by sorry` into the Batteries `theorem_wanted`
`exists_continuous_monotone_sub_of_boundedVariationOn`; moved the informal problem statement
docstring onto it and placed the declarations in namespace
`MathlibExt.MeasureTheory.ContinuousBVDiffContinuousMonotoneWanted`; replaced `import Mathlib`
by `public import Mathlib` under the module system.
This move supplies a proof and narrows the imports to the modules used.
-/
module

public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.EMetricSpace.VariationOnFromTo

/-! # The Jordan decomposition of continuous functions of bounded variation -/

@[expose] public section

open Set

namespace MathlibExt.MeasureTheory.ContinuousBVDiffContinuousMonotoneWanted

/-- **Jordan decomposition of a continuous function of bounded variation.** Let
$F : \mathbb{R} \to \mathbb{R}$ be continuous and of bounded variation on all of $\mathbb{R}$.
Then there are continuous non-decreasing functions $F_1, F_2 : \mathbb{R} \to \mathbb{R}$ such
that $F = F_1 - F_2$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Functions of
one variable), `benchmark/level1/ma_proofbench_l1_33.lean` at openbmb/ma-proofbench@31bab4c.
-/
theorem exists_continuous_monotone_sub_of_boundedVariationOn
    {F : ℝ → ℝ} (hF_bv : BoundedVariationOn F (Set.univ : Set ℝ))
    (hF_cont : Continuous F) :
    ∃ F₁ F₂ : ℝ → ℝ, Monotone F₁ ∧ Continuous F₁ ∧ Monotone F₂ ∧ Continuous F₂ ∧ F = F₁ - F₂ := by
  let V := variationOnFromTo F univ 0
  have hloc := hF_bv.locallyBoundedVariationOn
  have hV_cont : Continuous V :=
    continuous_iff_continuousAt.mpr fun x =>
      (hF_bv.continuousAt_variationOnFromTo_iff 0 x).mpr hF_cont.continuousAt
  have hV_mono : Monotone V :=
    monotoneOn_univ.mp (variationOnFromTo.monotoneOn hloc (mem_univ (0 : ℝ)))
  have hVF_mono : Monotone (V - F) :=
    monotoneOn_univ.mp (variationOnFromTo.sub_self_monotoneOn hloc (mem_univ (0 : ℝ)))
  refine ⟨V, V - F, hV_mono, hV_cont, hVF_mono, hV_cont.sub hF_cont, ?_⟩
  funext x
  exact (sub_sub_cancel (V x) (F x)).symm

end MathlibExt.MeasureTheory.ContinuousBVDiffContinuousMonotoneWanted
