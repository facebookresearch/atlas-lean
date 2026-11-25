/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ModularForms.JacobiTheta.NonicProduct
import Mathlib.Tactic.Linarith

open MetaMathlibExt

-- Recover the quotient form with the Euler factor at q³ as denominator.
example {q : ℂ} (hq : ‖q‖ < 1) (hden : ramanujanThetaRaw (-q ^ 3) (-(q ^ 3) ^ 2) ≠ 0) :
    ramanujanThetaRaw (-q) (-q ^ 8) * ramanujanThetaRaw (-q ^ 2) (-q ^ 7) *
        ramanujanThetaRaw (-q ^ 4) (-q ^ 5) =
      ramanujanThetaRaw (-q) (-q ^ 2) * ramanujanThetaRaw (-q ^ 9) (-(q ^ 9) ^ 2) ^ 3 /
        ramanujanThetaRaw (-q ^ 3) (-(q ^ 3) ^ 2) :=
  (eq_div_iff hden).2 (ramanujanTheta_order_nine_product hq)

-- At q = 0 all theta factors equal one: only the constant summand survives.
example : ramanujanThetaRaw 0 0 = 1 := by
  rw [ramanujanThetaRaw, tsum_eq_single 0, ramanujanThetaTerm_zero]
  intro n hn
  have hs : 1 ≤ n * n := by have := mul_self_pos.mpr hn; omega
  rcases lt_or_gt_of_ne hn with h | h
  · have he : 2 ≤ n * (n - 1) := by linarith
    simp [ramanujanThetaTerm, zero_pow (show (n * (n - 1) / 2).toNat ≠ 0 by omega)]
  · have he : 2 ≤ n * (n + 1) := by linarith
    simp [ramanujanThetaTerm, zero_pow (show (n * (n + 1) / 2).toNat ≠ 0 by omega)]

#print axioms MetaMathlibExt.ramanujanTheta_order_nine_product
