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
import Mathlib.Tactic.Linarith

/-! # The Jordan decomposition of continuous functions of bounded variation -/

@[expose] public section

open Set Filter
open scoped ENNReal Topology

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
  let V (x : ℝ) := (eVariationOn F (Iic x)).toReal
  have hfinite (s : Set ℝ) : eVariationOn F s ≠ ∞ := hF_bv.mono (subset_univ s)
  -- The two intervals meet at x, so variation is additive across this split.
  have hstep {x y : ℝ} (hxy : x ≤ y) :
      V y = V x + (eVariationOn F (Icc x y)).toReal := by
    have hsplit : Iic x ∪ Icc x y = Iic y := by
      ext z
      simp only [mem_union, mem_Iic, mem_Icc]
      exact ⟨fun h => h.elim (fun hz => hz.trans hxy) And.right,
        fun hz => (le_total z x).imp_right (fun h => ⟨h, hz⟩)⟩
    have huv := eVariationOn.union F
      (show IsGreatest (Iic x) x from ⟨le_rfl, fun _ hz => hz⟩)
      (show IsLeast (Icc x y) x from ⟨⟨le_rfl, hxy⟩, fun _ hz => hz.1⟩)
    rw [hsplit] at huv
    change (eVariationOn F (Iic y)).toReal = _
    rw [huv, ENNReal.toReal_add (hfinite _) (hfinite _)]
  have hV_mono : Monotone V := by
    intro x y hxy
    rw [hstep hxy]
    exact le_add_of_nonneg_right ENNReal.toReal_nonneg
  -- The variation over a shrinking interval tends to zero from either side.
  have hV_cont : Continuous V := by
    refine continuous_iff_continuousAt.mpr fun x => continuousAt_iff_continuous_left_right.mpr ?_
    have hleft : Tendsto (fun y => eVariationOn F (Icc y x)) (𝓝 x) (𝓝 0) := by
      simpa only [univ_inter, nhdsWithin_univ] using
        hF_bv.tendsto_eVariationOn_Icc_zero_left (x := x)
          hF_cont.continuousAt.continuousWithinAt
    have hright : Tendsto (fun y => eVariationOn F (Icc x y)) (𝓝 x) (𝓝 0) := by
      simpa only [univ_inter, nhdsWithin_univ] using
        hF_bv.tendsto_eVariationOn_Icc_zero_right (x := x)
          hF_cont.continuousAt.continuousWithinAt
    have htoReal := (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto
    constructor
    · have hh : Tendsto (fun y => V x - (eVariationOn F (Icc y x)).toReal)
          (𝓝[Iic x] x) (𝓝 (V x)) := by
        simpa only [Function.comp_apply, ENNReal.toReal_zero, sub_zero] using
          tendsto_const_nhds.sub ((htoReal.comp hleft).mono_left nhdsWithin_le_nhds)
      apply hh.congr'
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact sub_eq_iff_eq_add.mpr (hstep (show y ≤ x from hy))
    · have hh : Tendsto (fun y => V x + (eVariationOn F (Icc x y)).toReal)
          (𝓝[Ici x] x) (𝓝 (V x)) := by
        simpa only [Function.comp_apply, ENNReal.toReal_zero, add_zero] using
          tendsto_const_nhds.add ((htoReal.comp hright).mono_left nhdsWithin_le_nhds)
      apply hh.congr'
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (hstep (show x ≤ y from hy)).symm
  refine ⟨V, V - F, hV_mono, hV_cont, ?_, hV_cont.sub hF_cont, ?_⟩
  · intro x y hxy
    change V x - F x ≤ V y - F y
    have hdist := eVariationOn.edist_le F
      (show y ∈ Icc x y from ⟨hxy, le_rfl⟩) (show x ∈ Icc x y from ⟨le_rfl, hxy⟩)
    rw [edist_dist, ← ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (hfinite _),
      ENNReal.toReal_ofReal dist_nonneg, Real.dist_eq] at hdist
    rw [hstep hxy]
    linarith [le_abs_self (F y - F x)]
  · funext x
    change F x = V x - (V x - F x)
    exact (sub_sub_cancel _ _).symm

end MathlibExt.MeasureTheory.ContinuousBVDiffContinuousMonotoneWanted
