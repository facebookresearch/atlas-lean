/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Cyclotomic.PrimePowerDivisibility

open MetaMathlibExt Polynomial

-- At exponent zero there are no cyclotomic factors to check.
example : (2 : ℤ) ∣ 3 ^ (1 * 2 ^ 0 : ℕ) - 1 := by
  apply (prime_dvd_pow_sub_one_iff_cyclotomic (p := 2) (r := 1) (a := 0)
    (x := 3) (by decide) (by decide) (by decide)).2
  refine ⟨by decide, fun i hi => ?_⟩
  have := Finset.mem_Icc.mp hi
  omega

-- The last cyclotomic factor uses the previous exponent, not the outer exponent.
example : (2 : ℤ) ∣ (cyclotomic 2 ℤ).eval (3 ^ (1 * 2 ^ (2 - 1) : ℕ)) := by
  have h := (prime_dvd_pow_sub_one_iff_cyclotomic (p := 2) (r := 1) (a := 2)
    (x := 3) (by decide) (by decide) (by decide)).1 (by decide)
  exact h.2 2 (by decide)
