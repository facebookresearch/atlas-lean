/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ModularForms.JacobiTheta.RamanujanProduct
import Mathlib.Tactic.Ring

open MetaMathlibExt

-- With zero common product the odd-parity contribution still survives.
example (a d : ℂ) (ha : a ≠ 0) :
    ramanujanThetaRaw a 0 * ramanujanThetaRaw 0 d =
      ramanujanThetaRaw (a * d) 0 * ramanujanThetaRaw 0 0 +
        a * ramanujanThetaRaw 0 0 * ramanujanThetaRaw (d / a) 0 := by
  simpa using ramanujanTheta_mul_of_mul_eq (b := 0) (c := 0) (d := d) ha (by simp) (by simp)

-- Equal parameters specialize the addition formula to a sum of two squares.
example {q : ℂ} (hq : q ≠ 0) (h : ‖q‖ < 1) :
    ramanujanThetaRaw q q ^ 2 =
      ramanujanThetaRaw (q ^ 2) (q ^ 2) ^ 2 + q * ramanujanThetaRaw 1 (q ^ 4) ^ 2 := by
  have hqq : ‖q * q‖ < 1 := by
    rw [← sq, norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) h two_ne_zero
  simpa only [← sq, div_self hq, show q ^ 2 * q * q = q ^ 4 by ring, mul_assoc] using
    ramanujanTheta_mul_of_mul_eq (c := q) (d := q) hq hqq rfl

#print axioms MetaMathlibExt.ramanujanTheta_mul_of_mul_eq
