/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.GaussSum
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Analysis.SpecialFunctions.Sqrt

import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# The absolute value of a primitive Gauss sum

For a primitive Dirichlet character `χ` modulo `q` and a primitive additive character `e` of
`ZMod q`, the Gauss sum `τ(χ) = ∑_a χ a e a` has absolute value `√q`. Mathlib proves
`gaussSum_mul_gaussSum_eq_card` only over finite fields; for an arbitrary modulus it is
primitivity of `χ` that replaces the field structure, through
`gaussSum_mulShift_of_isPrimitive`.

## Main statements

* `DirichletCharacter.norm_gaussSum_of_isPrimitive`: `‖gaussSum χ e‖ = √q`.
* `DirichletCharacter.norm_gaussSum_stdAddChar_of_isPrimitive`: the same for the standard
  additive character `a ↦ exp (2 π i a / q)`.
-/

@[expose] public section

open Finset

namespace DirichletCharacter

variable {q : ℕ} [NeZero q]

/-- **The absolute value of a primitive Gauss sum.** For a primitive Dirichlet character `χ`
modulo `q` and a primitive additive character `e` of `ZMod q`, `‖gaussSum χ e‖ = √q`. -/
theorem norm_gaussSum_of_isPrimitive {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {e : AddChar (ZMod q) ℂ} (he : e.IsPrimitive) :
    ‖gaussSum χ e‖ = Real.sqrt q := by
  classical
  set τ := gaussSum χ e
  have hT : ∀ a : ZMod q, gaussSum χ (e.mulShift a) = χ⁻¹ a * τ := fun a ↦
    gaussSum_mulShift_of_isPrimitive e hχ a
  have horth : ∀ y : ZMod q, ∑ a : ZMod q, e (a * y) = if y = 0 then (q : ℂ) else 0 := by
    intro y
    simpa [ZMod.card] using AddChar.sum_mulShift y he
  -- Expand `∑_a |τ(χ, e_a)|²` in two ways.
  have hA : ∑ a : ZMod q, gaussSum χ (e.mulShift a) * starRingEnd ℂ (gaussSum χ (e.mulShift a))
      = ∑ m : ZMod q, ∑ n : ZMod q,
          starRingEnd ℂ (χ m) * χ n * ∑ a : ZMod q, e (a * (n - m)) := by
    simp only [gaussSum, AddChar.mulShift_apply, map_sum, map_mul, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ ↦ Finset.sum_congr rfl fun a _ ↦ ?_
    rw [← AddChar.map_neg_eq_conj, mul_sub, sub_eq_add_neg, AddChar.map_add_eq_mul]
    ring
  have hB : ∑ m : ZMod q, ∑ n : ZMod q,
      starRingEnd ℂ (χ m) * χ n * ∑ a : ZMod q, e (a * (n - m))
      = (q : ℂ) * ∑ m : ZMod q, χ m * starRingEnd ℂ (χ m) := by
    simp only [horth, sub_eq_zero, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ ↦ by ring
  have hC : ∑ a : ZMod q, gaussSum χ (e.mulShift a) * starRingEnd ℂ (gaussSum χ (e.mulShift a))
      = (∑ a : ZMod q, χ⁻¹ a * starRingEnd ℂ (χ⁻¹ a)) * (τ * starRingEnd ℂ τ) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [hT, map_mul]
    ring
  have hnorm : ∀ a : ZMod q, ‖χ⁻¹ a‖ = ‖χ a‖ := by
    intro a
    by_cases ha : IsUnit a
    · have h1 : ‖χ a‖ = 1 := by simpa [ha.unit_spec] using χ.unit_norm_eq_one ha.unit
      rw [MulChar.inv_apply_eq_inv', norm_inv, h1, inv_one]
    · rw [MulChar.map_nonunit _ ha, MulChar.map_nonunit _ ha]
  have hD : ∑ a : ZMod q, χ⁻¹ a * starRingEnd ℂ (χ⁻¹ a)
      = ((∑ a : ZMod q, ‖χ a‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    exact Finset.sum_congr rfl fun a _ ↦ by rw [Complex.mul_conj', hnorm]
  have hS : ∑ a : ZMod q, χ a * starRingEnd ℂ (χ a) = ((∑ a : ZMod q, ‖χ a‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    exact Finset.sum_congr rfl fun a _ ↦ Complex.mul_conj' _
  have hSpos : 0 < ∑ a : ZMod q, ‖χ a‖ ^ 2 := by
    have h1 : ‖χ 1‖ ^ 2 ≤ ∑ a : ZMod q, ‖χ a‖ ^ 2 :=
      Finset.single_le_sum (f := fun a ↦ ‖χ a‖ ^ 2) (fun a _ ↦ by positivity)
        (Finset.mem_univ 1)
    simp only [map_one, norm_one, one_pow] at h1
    linarith
  have hkey : τ * starRingEnd ℂ τ = (q : ℂ) := by
    have h := hC.symm.trans (hA.trans hB)
    rw [hD, hS] at h
    have hne : ((∑ a : ZMod q, ‖χ a‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hSpos.ne'
    exact mul_left_cancel₀ hne (by rw [h, mul_comm])
  rw [Complex.mul_conj'] at hkey
  have hreal : ‖τ‖ ^ 2 = (q : ℝ) := by exact_mod_cast hkey
  rw [← hreal, Real.sqrt_sq (norm_nonneg _)]

/-- **The absolute value of a primitive Gauss sum**, for the standard additive character
`a ↦ exp (2 π i a / q)`: `‖gaussSum χ ZMod.stdAddChar‖ = √q` for primitive `χ`. -/
theorem norm_gaussSum_stdAddChar_of_isPrimitive {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) : ‖gaussSum χ ZMod.stdAddChar‖ = Real.sqrt q :=
  norm_gaussSum_of_isPrimitive hχ (ZMod.isPrimitive_stdAddChar q)

end DirichletCharacter
