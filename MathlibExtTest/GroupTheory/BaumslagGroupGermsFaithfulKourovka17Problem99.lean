/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.BaumslagGroupGermsFaithfulKourovka17Problem99

/-!
# Tests for Baumslag's germ representation

The refutation of faithfulness in existential form, values of the letter functions (including
the value `0` of `log₂` at `0`), the word functions of `1`, of `a` and of `c = bab⁻¹`, and the
defining relator, which acts as the identity on `(0, ∞)` and is trivial in Baumslag's group.
-/

namespace MathlibExt.GroupTheory.BaumslagGroupGermsFaithfulKourovka17Problem99Wanted

/-- The refutation supplies an element of the free group on `a, b` whose word function is the
identity for all large `x` but whose image in Baumslag's group is not trivial. -/
example : ∃ w : FreeGroup (Fin 2), wordFunction w =ᶠ[Filter.atTop] id ∧
    (PresentedGroup.mk _ w : BaumslagGroup) ≠ 1 := by
  by_contra h
  refine baumslagGroupGermRepresentationFaithful_refuted fun w hw => ?_
  by_contra hne
  exact h ⟨w, hw, hne⟩

/-- `a` doubles and `a⁻¹` halves. -/
example : letterFunction (0, true) 3 = 6 ∧ letterFunction (0, false) 6 = 3 := by
  constructor <;> norm_num [letterFunction]

/-- `b` is `x ↦ 2 ^ x` and `b⁻¹` is `log₂`. -/
example : letterFunction (1, true) 3 = 8 ∧ letterFunction (1, false) 8 = 3 := by
  constructor
  · change (2 : ℝ) ^ (3 : ℝ) = 8
    norm_num
  · change Real.logb 2 8 = 3
    rw [show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num, Real.logb_rpow (by norm_num) (by norm_num)]

/-- The letter function of `b⁻¹` takes the junk value `0` at `0` and is `log₂ |x|` at negative
`x`. -/
example : letterFunction (1, false) 0 = 0 ∧ letterFunction (1, false) (-8) = 3 := by
  constructor
  · simp [letterFunction]
  · change Real.logb 2 (-8) = 3
    rw [Real.logb_neg_eq_logb, show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num,
      Real.logb_rpow (by norm_num) (by norm_num)]

/-- The identity element acts as the identity. -/
example : wordFunction 1 = id := rfl

/-- The generator `a` acts as `x ↦ 2x`. -/
example : wordFunction (FreeGroup.of 0) = fun x => 2 * x := rfl

/-- The element `c = bab⁻¹` acts as `x ↦ x²` on `(0, ∞)`. -/
example (x : ℝ) (hx : 0 < x) :
    wordFunction (FreeGroup.of 1 * FreeGroup.of 0 * (FreeGroup.of 1)⁻¹) x = x ^ 2 := by
  have hw : (FreeGroup.of 1 * FreeGroup.of 0 * (FreeGroup.of 1)⁻¹ : FreeGroup (Fin 2)).toWord =
      [(1, true), (0, true), (1, false)] := by decide
  rw [wordFunction, hw]
  change (2 : ℝ) ^ (2 * Real.logb 2 x) = x ^ 2
  rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hx]
  norm_cast

/-- The defining relator `(bab⁻¹) a (bab⁻¹)⁻¹ a⁻²` acts as the identity on `(0, ∞)`. -/
example (x : ℝ) (hx : 0 < x) :
    wordFunction ((FreeGroup.of 1 * FreeGroup.of 0 * (FreeGroup.of 1)⁻¹) * FreeGroup.of 0 *
      (FreeGroup.of 1 * FreeGroup.of 0 * (FreeGroup.of 1)⁻¹)⁻¹ * (FreeGroup.of 0 ^ 2)⁻¹) x =
      x := by
  have hw : ((FreeGroup.of 1 * FreeGroup.of 0 * (FreeGroup.of 1)⁻¹) * FreeGroup.of 0 *
      (FreeGroup.of 1 * FreeGroup.of 0 * (FreeGroup.of 1)⁻¹)⁻¹ * (FreeGroup.of 0 ^ 2)⁻¹ :
        FreeGroup (Fin 2)).toWord =
      [(1, true), (0, true), (1, false), (0, true), (1, true), (0, false), (1, false), (0, false),
        (0, false)] := by decide
  rw [wordFunction, hw]
  change (2 : ℝ) ^ (2 * Real.logb 2 (2 * (2 : ℝ) ^ (Real.logb 2 (x / 2 / 2) / 2))) = x
  have h2 : (2 : ℝ) ≠ 0 := two_ne_zero
  rw [Real.logb_div (by positivity) h2, Real.logb_div hx.ne' h2, Real.logb_self_eq_one one_lt_two,
    mul_comm (2 : ℝ) (2 ^ _), ← Real.rpow_add_one h2, Real.logb_rpow two_pos (by norm_num),
    show 2 * ((Real.logb 2 x - 1 - 1) / 2 + 1) = Real.logb 2 x by ring,
    Real.rpow_logb two_pos (by norm_num) hx]

/-- The defining relator is trivial in Baumslag's group. -/
example : (PresentedGroup.mk _ ((FreeGroup.of 1 * FreeGroup.of 0 * (FreeGroup.of 1)⁻¹) *
    FreeGroup.of 0 * (FreeGroup.of 1 * FreeGroup.of 0 * (FreeGroup.of 1)⁻¹)⁻¹ *
      (FreeGroup.of 0 ^ 2)⁻¹) : BaumslagGroup) = 1 :=
  PresentedGroup.one_of_mem rfl

end MathlibExt.GroupTheory.BaumslagGroupGermsFaithfulKourovka17Problem99Wanted
