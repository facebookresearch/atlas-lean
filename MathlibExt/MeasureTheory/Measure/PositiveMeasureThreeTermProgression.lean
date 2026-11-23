/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
# Sets of positive measure contain three-term arithmetic progressions

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_75.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782), distributed under the MIT License above.
See also the Hugging Face dataset openbmb/MA-ProofBench. Changes made: converted
`theorem ma_proofbench_l2_75 … := by sorry` into the Batteries `theorem_wanted`
`exists_add_mem_and_sub_mem_of_volume_pos`; moved the informal problem statement docstring onto it
and placed the declarations in namespace
`MathlibExt.MeasureTheory.PositiveMeasureThreeTermProgressionWanted`; replaced `import Mathlib`
by `public import Mathlib` under the module system. This move supplies a proof using Lebesgue
density and measure-preserving reflection, without changing the ATLAS name or statement.
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Tactic.Ring

/-! # Three-term progressions in sets of positive measure -/

@[expose] public section

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology

namespace MathlibExt.MeasureTheory.PositiveMeasureThreeTermProgressionWanted

/-- **Sets of positive measure contain three-term arithmetic progressions.** For every Borel set
$A \subseteq \mathbb{R}$ of positive Lebesgue measure there exist $x \in A$ and $y > 0$ such that
$x + y \in A$ and $x - y \in A$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Measure and integration;
Classical measure theory), `benchmark/level2/ma_proofbench_l2_75.lean` at
openbmb/ma-proofbench@31bab4c.
-/
theorem exists_add_mem_and_sub_mem_of_volume_pos
    (A : Set ℝ) (hAmeas : MeasurableSet A) (hApos : (0 : ENNReal) < volume A) :
    ∃ x ∈ A, ∃ y : ℝ, 0 < y ∧ x + y ∈ A ∧ x - y ∈ A := by
  have hμ : ((volume : Measure ℝ).restrict A) ≠ 0 := by
    intro hzero
    apply hApos.ne'
    rw [← Measure.restrict_apply_univ, hzero]
    simp
  have hneBot : (ae ((volume : Measure ℝ).restrict A)).NeBot := ae_neBot.mpr hμ
  obtain ⟨x, hxA, hx⟩ := ((ae_restrict_mem hAmeas).and
    (Besicovitch.ae_tendsto_measure_inter_div (volume : Measure ℝ) A)).exists
  have hhalf : (2 : ℝ≥0∞)⁻¹ < 1 := by
    simpa only [inv_one] using ENNReal.inv_lt_inv.mpr ENNReal.one_lt_two
  have hpos : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := self_mem_nhdsWithin
  obtain ⟨r, hr, hratio⟩ := (hpos.and (hx.eventually_const_lt hhalf)).exists
  let B := closedBall x r
  let C := A ∩ B
  have hB0 : volume B ≠ 0 := by
    change volume (closedBall x r) ≠ 0
    rw [Real.volume_closedBall]
    exact (ENNReal.ofReal_pos.mpr (mul_pos zero_lt_two hr)).ne'
  have hBtop : volume B ≠ ∞ := by
    change volume (closedBall x r) ≠ ∞
    rw [Real.volume_closedBall]
    exact ENNReal.ofReal_ne_top
  have hlarge : volume B < volume C + volume C := by
    have hlt : (2 : ℝ≥0∞)⁻¹ * volume B < volume C :=
      (ENNReal.lt_div_iff_mul_lt (Or.inl hB0) (Or.inl hBtop)).mp hratio
    calc
      volume B = 2 * ((2 : ℝ≥0∞)⁻¹ * volume B) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]
      _ < 2 * volume C := ENNReal.mul_lt_mul_right (by simp) (by simp) hlt
      _ = volume C + volume C := two_mul _
  let R (z : ℝ) := 2 * x - z
  have hR : MeasurePreserving R volume volume := by
    simpa only [R, Function.comp_def, sub_eq_add_neg] using
      (measurePreserving_add_left (volume : Measure ℝ) (2 * x)).comp
        ((volume : Measure ℝ).measurePreserving_neg)
  have hRB (z : ℝ) : R z ∈ B ↔ z ∈ B := by
    simp only [R, B, Metric.mem_closedBall, Real.dist_eq]
    rw [show 2 * x - z - x = -(z - x) by ring, abs_neg]
  have hC : MeasurableSet C := hAmeas.inter measurableSet_closedBall
  have hRC : MeasurableSet (R ⁻¹' C) := hC.preimage hR.measurable
  -- Both C and its reflection occupy more than half of B. Their overlap cannot be a singleton.
  by_contra h
  have hsub : C ∩ R ⁻¹' C ⊆ {x} := by
    rintro z ⟨hz, hRz⟩
    rw [mem_singleton_iff]
    by_contra hzx
    have hzA : z ∈ A := hz.1
    have hRzA : R z ∈ A := hRz.1
    apply h
    rcases lt_or_gt_of_ne hzx with hlt | hgt
    · refine ⟨x, hxA, x - z, sub_pos.mpr hlt, ?_, ?_⟩
      · rwa [show x + (x - z) = R z by dsimp [R]; ring]
      · rwa [show x - (x - z) = z by ring]
    · refine ⟨x, hxA, z - x, sub_pos.mpr hgt, ?_, ?_⟩
      · rwa [show x + (z - x) = z by ring]
      · rwa [show x - (z - x) = R z by dsimp [R]; ring]
  have hj : volume (C ∩ R ⁻¹' C) = 0 := measure_mono_null hsub (measure_singleton x)
  have hu : C ∪ R ⁻¹' C ⊆ B := by
    rintro z (hz | hz)
    · exact hz.2
    · exact (hRB z).mp hz.2
  have hadd : volume (C ∪ R ⁻¹' C) = volume C + volume C := by
    simpa only [hj, add_zero, hR.measure_preimage hC.nullMeasurableSet] using
      measure_union_add_inter (μ := (volume : Measure ℝ)) C hRC
  exact hlarge.not_ge (hadd ▸ measure_mono hu)

end MathlibExt.MeasureTheory.PositiveMeasureThreeTermProgressionWanted
