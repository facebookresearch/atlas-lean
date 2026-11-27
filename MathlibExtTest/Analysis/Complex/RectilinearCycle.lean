/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

import MathlibExt.Analysis.Complex.RectilinearCycle
import Mathlib.Tactic

open Set

universe u

example (r : RectilinearRectangle) :
    r.carrier = Complex.Rectangle r.first r.second :=
  rfl

example (f : ℂ → ℂ) : RectilinearCycle.integral 0 f = 0 := by
  simp

example {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (Gamma Lambda : RectilinearCycle) (f : ℂ → E) :
    RectilinearCycle.integral (Gamma + Lambda) f =
      RectilinearCycle.integral Gamma f + RectilinearCycle.integral Lambda f := by
  rw [RectilinearCycle.integral_add]

example (Gamma : RectilinearCycle) (f : ℂ → ℂ) :
    RectilinearCycle.integral (-Gamma) f = -RectilinearCycle.integral Gamma f := by
  rw [RectilinearCycle.integral_neg]

example (Gamma Lambda : RectilinearCycle) (f : ℂ → ℂ) :
    RectilinearCycle.integral (Gamma - Lambda) f =
      RectilinearCycle.integral Gamma f - RectilinearCycle.integral Lambda f := by
  rw [RectilinearCycle.integral_sub]

/-! Reversing the real-coordinate bounds reverses the displayed boundary
orientation. -/
example (f : ℂ → ℂ) :
    (RectilinearRectangle.ofBounds 1 (-1) (-1) 1).boundaryIntegral f =
      -(RectilinearRectangle.ofBounds (-1) 1 (-1) 1).boundaryIntegral f := by
  have hbottom :
      (∫ x : ℝ in (1 : ℝ)..(-1),
          f ((x : ℂ) + ((-1 : ℝ) : ℂ) * Complex.I)) =
        -∫ x : ℝ in (-1 : ℝ)..1,
          f ((x : ℂ) + ((-1 : ℝ) : ℂ) * Complex.I) :=
    intervalIntegral.integral_symm (-1) 1
  have htop :
      (∫ x : ℝ in (1 : ℝ)..(-1),
          f ((x : ℂ) + ((1 : ℝ) : ℂ) * Complex.I)) =
        -∫ x : ℝ in (-1 : ℝ)..1,
          f ((x : ℂ) + ((1 : ℝ) : ℂ) * Complex.I) :=
    intervalIntegral.integral_symm (-1) 1
  unfold RectilinearRectangle.boundaryIntegral
  simp only [RectilinearRectangle.ofBounds_first_re,
    RectilinearRectangle.ofBounds_first_im, RectilinearRectangle.ofBounds_second_re,
    RectilinearRectangle.ofBounds_second_im]
  rw [hbottom, htop]
  abel

/-! A rectangle with coincident vertical sides has zero displayed boundary,
for Banach-valued integrands in any universe. -/
example {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (f : ℂ → E) :
    (RectilinearRectangle.ofBounds 0 0 (-1) 1).boundaryIntegral f = 0 := by
  simp [RectilinearRectangle.boundaryIntegral]

example :
    (RectilinearRectangle.ofBounds (-1) 1 (-1) 1).boundaryIntegral
        (fun z : ℂ ↦ z⁻¹) = (2 * Real.pi : ℂ) * Complex.I := by
  exact RectilinearRectangle.boundaryIntegral_ofBounds_inv_eq_two_pi_mul_I
    (by norm_num) (by norm_num) (by norm_num)

example :
    (RectilinearRectangle.ofBounds 1 2 (-1) 1).boundaryIntegral
        (fun z : ℂ ↦ z⁻¹) = 0 := by
  have houtside : (0 : ℂ) ∉ (RectilinearRectangle.ofBounds 1 2 (-1) 1).carrier := by
    simp [RectilinearRectangle.carrier, Complex.Rectangle,
      RectilinearRectangle.ofBounds, Complex.mem_reProdIm]
  simpa only [sub_zero] using
    (RectilinearRectangle.boundaryIntegral_inv_sub_eq_zero_of_not_mem_carrier
      (RectilinearRectangle.ofBounds 1 2 (-1) 1) houtside)

example :
    RectilinearCycle.index
        (RectilinearCycle.ofRectangle (RectilinearRectangle.ofBounds (-1) 1 (-1) 1)) 0 = 1 := by
  rw [RectilinearCycle.index_ofRectangle]
  simp only [sub_zero]
  rw [RectilinearRectangle.boundaryIntegral_ofBounds_inv_eq_two_pi_mul_I
    (by norm_num) (by norm_num) (by norm_num)]
  apply inv_mul_cancel₀
  exact mul_ne_zero
    (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    Complex.I_ne_zero

example :
    RectilinearCycle.index
        (RectilinearCycle.ofRectangle (RectilinearRectangle.ofBounds (-1) 1 (-1) 1)) 2 = 0 := by
  apply RectilinearCycle.index_ofRectangle_eq_zero_of_not_mem_carrier
  simp [RectilinearRectangle.carrier, Complex.Rectangle,
    RectilinearRectangle.ofBounds, Complex.mem_reProdIm]

#print axioms Complex.boundary_rect_one_div
#print axioms RectilinearRectangle.boundaryIntegral_ofBounds_inv_sub_eq_two_pi_mul_I
#print axioms RectilinearCycle.integral_add
#print axioms RectilinearCycle.index_ofRectangle_eq_zero_of_not_mem_carrier
