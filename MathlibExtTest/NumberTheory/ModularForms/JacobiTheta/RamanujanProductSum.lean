/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ModularForms.JacobiTheta.RamanujanProductSum

open MetaMathlibExt

-- Equal parameters give a sum of squares.
example {q : ℂ} (h : ‖q * q‖ < 1) :
    ramanujanThetaRaw q q ^ 2 + ramanujanThetaRaw (-q) (-q) ^ 2 =
      2 * ramanujanThetaRaw (q ^ 2) (q ^ 2) ^ 2 := by
  simpa [pow_two, mul_assoc] using ramanujanTheta_mul_add_mul_neg (c := q) (d := q) rfl h

-- The first parameter can be zero even when the second is not.
example (b c : ℂ) :
    ramanujanThetaRaw 0 b * ramanujanThetaRaw c 0 +
        ramanujanThetaRaw 0 (-b) * ramanujanThetaRaw (-c) 0 =
      2 * ramanujanThetaRaw 0 0 * ramanujanThetaRaw 0 (b * c) := by
  simpa using ramanujanTheta_mul_add_mul_neg (a := 0) (b := b) (c := c) (d := 0)
    (by simp) (by simp)

-- Both parameters of the first theta function can vanish.
example (d : ℂ) :
    ramanujanThetaRaw 0 0 * ramanujanThetaRaw 0 d +
        ramanujanThetaRaw 0 0 * ramanujanThetaRaw 0 (-d) =
      2 * ramanujanThetaRaw 0 0 * ramanujanThetaRaw 0 0 := by
  simpa using ramanujanTheta_mul_add_mul_neg (a := 0) (b := 0) (c := 0) (d := d)
    (by simp) (by simp)

#print axioms MetaMathlibExt.ramanujanTheta_mul_add_mul_neg
