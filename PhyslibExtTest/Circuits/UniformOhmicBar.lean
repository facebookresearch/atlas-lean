/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.UniformOhmicBar

@[expose] public section

open PhyslibExt.Circuits.UniformOhmicBar MeasureTheory Set
open MeasureTheory

namespace PhyslibExtTest.Circuits.UniformOhmicBar

/-- The rectangle computation, done here directly: a `1 × 2`
cross-section, `σ = 3`, `V = 8`, `ℓ = 4` gives current `12`. -/
example : terminalCurrent (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 2)
    (fun _ => ohmCurrentDensity 3 (uniformAxialField 8 4)) = 12 := by
  have hC : ohmCurrentDensity 3 (uniformAxialField 8 4) = 6 := by
    unfold ohmCurrentDensity uniformAxialField
    norm_num
  have hVol : volume (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 2) = ENNReal.ofReal 2 := by
    have hProd : volume (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 2)
        = (volume.prod volume) (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 2) := rfl
    rw [hProd, MeasureTheory.Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
    simp only [sub_zero]
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1)]
    congr 1
    norm_num
  have hEq : (fun _ : ℝ × ℝ => ohmCurrentDensity 3 (uniformAxialField 8 4))
      = (fun _ : ℝ × ℝ => (6 : ℝ)) := by
    rw [hC]
  have hInt : terminalCurrent (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 2)
      (fun _ : ℝ × ℝ => (6 : ℝ)) = 12 := by
    have hConst : (∫ p in (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 2), (6 : ℝ) ∂volume)
        = volume.real (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 2) • (6 : ℝ) :=
      MeasureTheory.setIntegral_const 6
    have hReal : volume.real (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 2) = 2 := by
      rw [MeasureTheory.measureReal_def, hVol, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2)]
    unfold terminalCurrent
    exact hConst.trans (by rw [hReal, smul_eq_mul]; norm_num)
  rw [hEq]
  exact hInt



/-- Headline API on the rectangle data: conductance times voltage. -/
example : terminalCurrent (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 2)
    (fun _ => ohmCurrentDensity 3 (uniformAxialField 8 4))
    = conductance 3 2 4 * 8 := by
  apply terminalCurrent_eq_conductance_mul 3 2 4 8
    (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 2) _ _
  · exact measurableSet_Icc.prod measurableSet_Icc
  · have hProd : volume (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 2)
        = (volume.prod volume) (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 2) := rfl
    rw [hProd, MeasureTheory.Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
    simp only [sub_zero]
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1)]
    congr 1
    norm_num
  · norm_num
  · norm_num
  · norm_num
  · intro p _
    rfl
  · intro p _
    rfl

/-- Resistance is positive on the physical domain. -/
example : 0 < resistance 3 2 4 (by norm_num) :=
  resistance_pos 3 2 4 (by norm_num) (by norm_num) (by norm_num)

/-- Conductance and resistance are reciprocal in the domain. -/
example : conductance 3 2 4 * resistance 3 2 4 (by norm_num) = 1 :=
  conductance_mul_resistance 3 2 4 (by norm_num) (by norm_num) (by norm_num)

end PhyslibExtTest.Circuits.UniformOhmicBar
