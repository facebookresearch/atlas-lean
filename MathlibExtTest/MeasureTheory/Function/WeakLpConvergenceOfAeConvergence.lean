/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.MeasureTheory.Function.WeakLpConvergenceOfAeConvergence
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.NormNum

open MeasureTheory Set Filter
open scoped ENNReal Topology
open MathlibExt.MeasureTheory.WeakLpConvergenceOfAeConvergenceWanted

private noncomputable def pulse : ℝ → ℝ := (Icc (0 : ℝ) 1).indicator (fun _ => 1)

private noncomputable def shifted (n : ℕ) : ℝ → ℝ := pulse ∘ (fun x => x - (n : ℝ))

-- The limit is nonzero and the translated summand escapes every fixed bounded set.
example (g : ℝ → ℝ) (hg : MemLp g 2 volume) :
    Tendsto (fun n : ℕ => ∫ x : ℝ, (pulse x + shifted n x) * g x) atTop
      (𝓝 (∫ x : ℝ, pulse x * g x)) := by
  have hm : Measurable pulse := measurable_const.indicator measurableSet_Icc
  have hfin : (volume : Measure ℝ) (Icc (0 : ℝ) 1) ≠ ∞ := isCompact_Icc.measure_lt_top.ne
  have hLp : MemLp pulse 2 volume := (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr <| by
    have hsq (x : ℝ) : pulse x ^ (2 : ℕ) = pulse x := by
      by_cases hx : x ∈ Icc (0 : ℝ) 1 <;> simp [pulse, hx]
    simp_rw [hsq]
    exact (integrableOn_const hfin).integrable_indicator measurableSet_Icc
  have hshift (n : ℕ) : MemLp (shifted n) 2 volume :=
    hLp.comp_measurePreserving (measurePreserving_sub_right volume (n : ℝ))
  have hseq (n : ℕ) : MemLp (fun x => pulse x + shifted n x) 2 volume := hLp.add (hshift n)
  have hB : ∃ M : ENNReal, M < ⊤ ∧
      ∀ n : ℕ, eLpNorm (fun x => pulse x + shifted n x) 2 volume ≤ M := by
    refine ⟨eLpNorm pulse 2 volume + eLpNorm pulse 2 volume,
      ENNReal.add_lt_top.mpr ⟨hLp.eLpNorm_lt_top, hLp.eLpNorm_lt_top⟩, fun n => ?_⟩
    have hn : eLpNorm (shifted n) 2 volume = eLpNorm pulse 2 volume :=
      eLpNorm_comp_measurePreserving hLp.aestronglyMeasurable
        (measurePreserving_sub_right volume (n : ℝ))
    calc
      _ ≤ eLpNorm pulse 2 volume + eLpNorm (shifted n) 2 volume :=
        eLpNorm_add_le (f := pulse) (g := shifted n) one_le_two
      _ = _ := by rw [hn]
  have hpt : ∀ᵐ x ∂(volume : Measure ℝ),
      Tendsto (fun n : ℕ => pulse x + shifted n x) atTop (𝓝 (pulse x)) := by
    filter_upwards with x
    apply tendsto_const_nhds.congr'
    have hx := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_gt_atTop x)
    filter_upwards [hx] with n hn
    have hneg : x - (n : ℝ) < 0 := sub_neg.mpr hn
    have hnot : x - (n : ℝ) ∉ Icc (0 : ℝ) 1 := fun h => hneg.not_ge h.1
    simp [shifted, pulse, hnot]
  have hconj : (1 : ENNReal) / 2 + 1 / 2 = 1 := by
    simpa only [one_div, two_mul] using
      (ENNReal.mul_inv_cancel (a := 2) two_ne_zero ENNReal.ofNat_ne_top)
  exact tendsto_integral_mul_of_ae_tendsto_of_eLpNorm_bounded 2 2 (by norm_num)
    ENNReal.ofNat_lt_top hconj pulse (fun n x => pulse x + shifted n x) hseq hLp hpt hB g hg
