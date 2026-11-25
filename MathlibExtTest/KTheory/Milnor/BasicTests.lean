/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.KTheory.Milnor.Basic
import Mathlib.Tactic.NormNum

/-! Concrete clients of the Milnor quotient ring and its universal lift over `ℚ`. -/

open MilnorK MilnorK.MilnorKRing

noncomputable section

private def two : ℚˣ := Units.mk0 2 (by norm_num)
private def three : ℚˣ := Units.mk0 3 (by norm_num)

example : symbol ℚ 1 = 0 := symbol_one ℚ

example : symbol ℚ (two * three) = symbol ℚ two + symbol ℚ three :=
  symbol_mul ℚ two three

-- Here the two inputs are `2` and `-1`, both different from the identity unit.
example : symbol ℚ two * symbol ℚ (-1) = 0 := by
  have complement : Units.mk0 (1 - (2 : ℚ)) (by norm_num) = (-1 : ℚˣ) := by
    apply Units.ext
    norm_num
  simpa only [two, complement] using steinberg_zero ℚ 2 (by norm_num) (by norm_num)

private def tensorAugmentation : TensorRing ℚ →+* ℤ :=
  (TensorAlgebra.lift ℤ (0 : Additive ℚˣ →ₗ[ℤ] ℤ)).toRingHom

private lemma tensorAugmentation_ι (unit : ℚˣ) :
    tensorAugmentation (TensorAlgebra.ι ℤ (Additive.ofMul unit)) = 0 := by
  simp [tensorAugmentation]

private def augmentation : MilnorKRing ℚ →+* ℤ :=
  lift ℚ tensorAugmentation fun _ _ _ => by simp [tensorAugmentation_ι]

example : augmentation (symbol ℚ two) = 0 := by
  rw [symbol, augmentation, lift_mk, tensorAugmentation_ι]

example (tensor : TensorRing ℚ) : augmentation (mk ℚ tensor) = tensorAugmentation tensor := by
  rw [augmentation, lift_mk]

example (candidate : MilnorKRing ℚ →+* ℤ) (extendsTensor : candidate.comp (mk ℚ) =
    tensorAugmentation) : candidate = augmentation := by
  unfold augmentation
  exact lift_unique ℚ tensorAugmentation _ candidate extendsTensor

-- The augmentation sends the unit to `1 : ℤ`, so the quotient is not the zero ring.
example : (1 : MilnorKRing ℚ) ≠ 0 := by
  intro equal
  have impossible : (1 : ℤ) = 0 := by simpa using congrArg augmentation equal
  exact one_ne_zero impossible

end
