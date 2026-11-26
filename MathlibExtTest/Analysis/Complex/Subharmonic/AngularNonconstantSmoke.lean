/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.Complex.Subharmonic.AngularSublevel
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Angular sublevels of a nonconstant disk function

For `u(z)=Re(z)-1`, the strict sublevel at threshold `K=1` is described by
`r cos(θ)<0` inside `(0,2π]`. Positive and negative radii give different angle sets,
each of positive finite length. Radius zero gives the empty set and length zero.
The function is upper semicontinuous and nonpositive on the unit disk, so the
actual generalized measurability theorem applies to all three radii.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace AngularNonconstantSmoke

private def u (z : ℂ) : EReal := ((z.re - 1 : ℝ) : EReal)

private theorem continuous_u : Continuous u :=
  continuous_coe_real_ereal.comp (Complex.continuous_re.sub continuous_const)

private theorem upper_u : UpperSemicontinuousOn u (Metric.ball 0 1) :=
  continuous_u.continuousOn.upperSemicontinuousOn

private theorem nonpositive_u : ∀ z ∈ Metric.ball (0 : ℂ) 1, u z ≤ 0 := by
  intro z hz
  rw [Metric.mem_ball, dist_zero_right] at hz
  have hRe : z.re < 1 := (Complex.re_le_norm z).trans_lt hz
  exact EReal.coe_nonpos.mpr (by linarith)

private theorem mem_iff (r θ : ℝ) :
    θ ∈ Complex.angularSublevelSet u r 1 ↔
      θ ∈ Ioc 0 (2 * Real.pi) ∧ r * Real.cos θ < 0 := by
  simp only [Complex.angularSublevelSet, Set.mem_inter_iff, Set.mem_ofPred_eq,
    u, circleMap_zero_re]
  constructor
  · rintro ⟨hθ, h⟩
    refine ⟨hθ, ?_⟩
    have hreal : r * Real.cos θ - 1 < (-1 : ℝ) := by exact_mod_cast h
    linarith
  · rintro ⟨hθ, h⟩
    refine ⟨hθ, ?_⟩
    exact_mod_cast (show r * Real.cos θ - 1 < (-1 : ℝ) by linarith)

private theorem positive_length (r θ : ℝ)
    (hθ : θ ∈ Ioo 0 (2 * Real.pi)) (hneg : r * Real.cos θ < 0) :
    0 < Complex.angularSublevelLength u r 1 := by
  let O : Set ℝ := Ioo 0 (2 * Real.pi) ∩ {s : ℝ | r * Real.cos s < 0}
  have hcont : Continuous (fun s : ℝ => r * Real.cos s) :=
    continuous_const.mul Real.continuous_cos
  have hopen : IsOpen O := isOpen_Ioo.inter (isOpen_lt hcont continuous_const)
  have hpos : 0 < volume O := hopen.measure_pos volume ⟨θ, hθ, hneg⟩
  have hsubset : O ⊆ Complex.angularSublevelSet u r 1 := by
    intro s hs
    exact (mem_iff r s).mpr ⟨⟨hs.1.1, hs.1.2.le⟩, hs.2⟩
  exact hpos.trans_le (measure_mono hsubset)

private theorem zero_set : Complex.angularSublevelSet u 0 1 = ∅ := by
  ext θ
  rw [mem_iff]
  simp

example :
    (0 : ℂ) ∈ Metric.ball 0 1 ∧ (1 / 2 : ℂ) ∈ Metric.ball 0 1 ∧
      u 0 ≠ u (1 / 2) := by
  refine ⟨by norm_num [Metric.mem_ball], by norm_num [Metric.mem_ball], ?_⟩
  have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  apply (EReal.coe_ne_coe_iff).mpr
  rw [hhalf, Complex.zero_re, Complex.ofReal_re]
  norm_num

example : UpperSemicontinuousOn u (Metric.ball 0 1) ∧
    (∀ z ∈ Metric.ball (0 : ℂ) 1, u z ≤ 0) := ⟨upper_u, nonpositive_u⟩

example :
    MeasurableSet (Complex.angularSublevelSet u (1 / 2) 1) ∧
      MeasurableSet (Complex.angularSublevelSet u (-1 / 2) 1) ∧
      MeasurableSet (Complex.angularSublevelSet u 0 1) := by
  exact ⟨Complex.measurableSet_angularSublevelSet upper_u (by norm_num),
    Complex.measurableSet_angularSublevelSet upper_u (by norm_num),
    Complex.measurableSet_angularSublevelSet upper_u (by norm_num)⟩

example : Real.pi ∈ Complex.angularSublevelSet u (1 / 2) 1 ∧
    Real.pi ∉ Complex.angularSublevelSet u (-1 / 2) 1 := by
  constructor
  · apply (mem_iff _ _).mpr
    refine ⟨⟨Real.pi_pos, by linarith [Real.pi_pos]⟩, ?_⟩
    rw [Real.cos_pi]
    norm_num
  · intro h
    have hneg := ((mem_iff _ _).mp h).2
    rw [Real.cos_pi] at hneg
    norm_num at hneg

example : Real.pi / 3 ∉ Complex.angularSublevelSet u (1 / 2) 1 ∧
    Real.pi / 3 ∈ Complex.angularSublevelSet u (-1 / 2) 1 := by
  constructor
  · intro h
    have hneg := ((mem_iff _ _).mp h).2
    rw [Real.cos_pi_div_three] at hneg
    norm_num at hneg
  · apply (mem_iff _ _).mpr
    refine ⟨⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩, ?_⟩
    rw [Real.cos_pi_div_three]
    norm_num

example :
    0 < Complex.angularSublevelLength u (1 / 2) 1 ∧
      Complex.angularSublevelLength u (1 / 2) 1 ≤ ENNReal.ofReal (2 * Real.pi) ∧
      0 < Complex.angularSublevelLength u (-1 / 2) 1 ∧
      Complex.angularSublevelLength u (-1 / 2) 1 ≤ ENNReal.ofReal (2 * Real.pi) := by
  refine ⟨positive_length (1 / 2) Real.pi ?_ ?_,
    Complex.angularSublevelLength_le _ _ _,
    positive_length (-1 / 2) (Real.pi / 3) ?_ ?_,
    Complex.angularSublevelLength_le _ _ _⟩
  · exact ⟨Real.pi_pos, by linarith [Real.pi_pos]⟩
  · rw [Real.cos_pi]
    norm_num
  · constructor <;> linarith [Real.pi_pos]
  · rw [Real.cos_pi_div_three]
    norm_num

example : Complex.angularSublevelSet u 0 1 = ∅ ∧
    Complex.angularSublevelLength u 0 1 = 0 := by
  refine ⟨zero_set, ?_⟩
  rw [Complex.angularSublevelLength, zero_set, measure_empty]

end AngularNonconstantSmoke
