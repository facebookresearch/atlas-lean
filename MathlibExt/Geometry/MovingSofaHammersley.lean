/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.MovingSofa
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-!
# Hammersley's upper bound for the moving sofa

`MovingSofaWanted.hammersley_upper` bounds the optimal sofa area by twice the square root
of two, using intersections of unit strips during a passage through the corridor.
-/

open MeasureTheory Set MovingSofa
open scoped ENNReal ComplexConjugate

namespace MovingSofaWanted

-- The inverse image of a horizontal unit strip under a rotation and a translation.
private def strip (u : ℂ) (c : ℝ) : Set ℂ := {z | (u * z).im + c ∈ Icc 0 1}

-- Two strip coordinates map the intersection into a translated unit square. The determinant
-- of this coordinate change is the sine of the angle between the strips for unit rotations.
private theorem volume_strip_inter {u v : ℂ} (c d : ℝ)
    (h : Real.sqrt 2 / 2 ≤ |(v * conj u).im|) :
    volume (strip v d ∩ strip u c) ≤ ENNReal.ofReal (Real.sqrt 2) := by
  let M : Matrix (Fin 2) (Fin 2) ℝ := !![v.im, v.re; u.im, u.re]
  let box : Set (Fin 2 → ℝ) := Icc ![-d, -c] ![1 - d, 1 - c]
  have hdet : LinearMap.det M.toLin' = (v * conj u).im := by
    simp [M, LinearMap.det_toLin', Matrix.det_fin_two_of, Complex.mul_im]
    ring
  have hpos : 0 < |(v * conj u).im| := lt_of_lt_of_le (by positivity) h
  have hsub : strip v d ∩ strip u c ⊆ Complex.measurableEquivPi ⁻¹' (M.toLin' ⁻¹' box) := by
    intro z ⟨hv, hu⟩
    change 0 ≤ (v * z).im + d ∧ (v * z).im + d ≤ 1 at hv
    change 0 ≤ (u * z).im + c ∧ (u * z).im + c ≤ 1 at hu
    change M.toLin' (Complex.measurableEquivPi z) ∈ box
    constructor <;> intro i <;> fin_cases i <;>
      simp [M, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Complex.mul_im] at * <;> linarith
  have hbox : volume box = 1 := by
    simp [box, Real.volume_Icc_pi, Fin.prod_univ_two]
  apply (measure_mono hsub).trans
  rw [Complex.volume_preserving_equiv_pi.measure_preimage_equiv,
    Measure.addHaar_preimage_linearMap _ (hdet ▸ abs_pos.mp hpos), hdet, hbox, mul_one, abs_inv]
  apply ENNReal.ofReal_le_ofReal
  apply (inv_le_iff_one_le_mul₀ hpos).2
  nlinarith [mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg 2),
    Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]

-- Looking at a vertical strip amounts to measuring the imaginary part after a quarter-turn.
private theorem mem_vertical_strip (m : Motion) (t : unitInterval) (z : ℂ) :
    z ∈ strip (Complex.I * m.rotation t) (m.translation t).re ↔
      (m.position t z).re ∈ Icc 0 1 := by
  simp [strip, Motion.position, mul_assoc, Complex.mul_im]

/-- **Hammersley's upper bound for the moving sofa constant.** The moving sofa constant, the
supremum of the areas of connected Lebesgue-measurable planar shapes that a continuous rigid motion
can carry through the right-angled corridor of width $1$, is at most $2\sqrt{2}$.

Source: catalogue line 13, attributed to Hammersley (1968). Primary not retained. -/
public theorem hammersley_upper :
    MovingSofa.optimalArea ≤ ENNReal.ofReal (2 * Real.sqrt 2) := by
  apply iSup_le
  intro K
  apply iSup_le
  rintro ⟨_, _, m, hstart, hend, hpass⟩
  let u := m.rotation 0
  let c := (m.translation 0).im
  have hentry : K ⊆ strip u c := fun z hz ↦ (hstart (mem_image_of_mem _ hz)).2
  -- Track the rotation relative to the entrance orientation.
  let r (t : unitInterval) : Circle := m.rotation t * u⁻¹
  have hr (t : unitInterval) : (r t : ℂ) = (m.rotation t : ℂ) * conj (u : ℂ) := by
    rw [← Circle.coe_inv_eq_conj]
    rfl
  have hvert (t : unitInterval) (ht : Real.sqrt 2 / 2 ≤ |(r t : ℂ).re|) :
      volume (strip (Complex.I * m.rotation t) (m.translation t).re ∩ strip u c) ≤
        ENNReal.ofReal (Real.sqrt 2) := by
    apply volume_strip_inter
    simpa [mul_assoc, ← hr, Complex.mul_im] using ht
  by_cases h : Real.sqrt 2 / 2 ≤ |(r 1 : ℂ).re|
  · -- The entrance strip and the final vertical strip already bound the area.
    have hsub : K ⊆ strip (Complex.I * m.rotation 1) (m.translation 1).re ∩ strip u c := by
      intro z hz
      obtain ⟨hx, hx', _⟩ := hend (mem_image_of_mem _ hz)
      exact ⟨(mem_vertical_strip m 1 z).2 ⟨hx, hx'⟩, hentry hz⟩
    exact (measure_mono hsub).trans ((hvert 1 h).trans (ENNReal.ofReal_le_ofReal (by
      linarith [Real.sqrt_nonneg 2])))
  · -- At an intermediate orientation both arm intersections have area at most √2.
    have hcont : Continuous (fun t ↦ |(r t : ℂ).re|) := by
      dsimp [r]
      fun_prop
    have hzero : Real.sqrt 2 / 2 ≤ |(r 0 : ℂ).re| := by
      simp [r, u]
      nlinarith [Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
    obtain ⟨t, ht⟩ := intermediate_value_univ 1 0 hcont
      (show Real.sqrt 2 / 2 ∈ Icc _ _ from ⟨(not_le.mp h).le, hzero⟩)
    change |(r t : ℂ).re| = Real.sqrt 2 / 2 at ht
    have him : Real.sqrt 2 / 2 ≤ |(r t : ℂ).im| := by
      apply (sq_le_sq₀ (by positivity) (abs_nonneg _)).mp
      have hnorm := Circle.normSq_coe (r t)
      rw [Complex.normSq_apply] at hnorm
      nlinarith [sq_abs (r t : ℂ).im, sq_abs (r t : ℂ).re,
        congrArg (· ^ 2) ht, Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
    have hhor := volume_strip_inter c (m.translation t).im (hr t ▸ him)
    have hsub : K ⊆ (strip (m.rotation t) (m.translation t).im ∩ strip u c) ∪
        (strip (Complex.I * m.rotation t) (m.translation t).re ∩ strip u c) := by
      intro z hz
      rcases hpass t (mem_image_of_mem _ hz) with ⟨_, hy⟩ | ⟨hx, hx', _⟩
      · exact Or.inl ⟨hy, hentry hz⟩
      · exact Or.inr ⟨(mem_vertical_strip m t z).2 ⟨hx, hx'⟩, hentry hz⟩
    calc
      _ ≤ _ := measure_mono hsub
      _ ≤ _ := measure_union_le _ _
      _ ≤ _ := add_le_add hhor (hvert t ht.ge)
      _ = _ := by rw [two_mul, ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)]

end MovingSofaWanted
