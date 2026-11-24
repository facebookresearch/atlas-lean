/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CohenLcmGcd
import Mathlib.Data.Fin.VecNotation

/-! # Tests for Cohen's lcm–gcd inequality -/

open MetaMathlibExt

-- The empty family is allowed for every integer exponent.
example (t : ℤ) :
    ∏ i : Fin 0, ((Fin.elim0 i : ℕ) : ℚ) ^ t ≤
      ((Finset.univ.lcm (Fin.elim0 : Fin 0 → ℕ) : ℕ) : ℚ) ^ (t * (t + 1) / 2) *
        ∏ i : Fin 0, ∏ j ∈ Finset.Ioi i, ((Nat.gcd (Fin.elim0 i) (Fin.elim0 j) : ℕ) : ℚ) :=
  prod_zpow_le_lcm_zpow_mul_prod_gcd (d := Fin.elim0) (hd := fun i => i.elim0) (t := t)

-- At `t = -2`, the lcm exponent is positive despite the negative input exponent.
example : (1 / 576 : ℚ) ≤ 24 := by
  have h := prod_zpow_le_lcm_zpow_mul_prod_gcd (d := ![4, 6])
    (hd := by decide) (t := -2)
  convert h using 1 <;> decide +kernel

-- At `t = 2`, the three gcd factors are 4, 4 and 8, and equality is attained.
example : (65536 : ℚ) ≤ 65536 := by
  have h := prod_zpow_le_lcm_zpow_mul_prod_gcd (d := ![4, 8, 8])
    (hd := by decide) (t := 2)
  convert h using 1 <;> decide +kernel

/-- info: 'MetaMathlibExt.prod_zpow_le_lcm_zpow_mul_prod_gcd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MetaMathlibExt.prod_zpow_le_lcm_zpow_mul_prod_gcd
