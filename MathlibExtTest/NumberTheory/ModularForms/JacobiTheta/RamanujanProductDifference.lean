/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ModularForms.JacobiTheta.RamanujanProductDifference
import Mathlib.Tactic.Ring

open MetaMathlibExt

-- Equal parameters give a difference of squares with a unit first argument on the right.
example {q : ℂ} (hq : q ≠ 0) (h : ‖q * q‖ < 1) :
    ramanujanThetaRaw q q ^ 2 - ramanujanThetaRaw (-q) (-q) ^ 2 =
      2 * q * ramanujanThetaRaw 1 (q ^ 4) ^ 2 := by
  have heq := ramanujanTheta_mul_sub_mul_neg (c := q) (d := q) rfl h hq hq
  rw [div_self hq, show q * q ^ 2 * q = q ^ 4 by ring,
    show q * q * q ^ 2 = q ^ 4 by ring] at heq
  simpa only [pow_two, mul_assoc] using heq

-- Opposite parameter pairs make the left-hand products cancel.
example {q : ℂ} (hq : q ≠ 0) (h : ‖q * q‖ < 1) : ramanujanThetaRaw (-1) (-(q ^ 4)) = 0 := by
  have heq := ramanujanTheta_mul_sub_mul_neg (a := q) (b := q) (c := -q) (d := -q)
    (by simp) h (neg_ne_zero.mpr hq) (neg_ne_zero.mpr hq)
  rw [neg_neg, mul_comm (ramanujanThetaRaw (-q) (-q)), sub_self, div_neg, div_self hq,
    show q * (-q) ^ 2 * -q = -(q ^ 4) by ring,
    show q * -q * (-q) ^ 2 = -(q ^ 4) by ring] at heq
  simpa [hq] using heq.symm

#print axioms MetaMathlibExt.ramanujanTheta_mul_sub_mul_neg
