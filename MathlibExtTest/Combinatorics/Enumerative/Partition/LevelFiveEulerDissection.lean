/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import MathlibExt.Combinatorics.Enumerative.Partition.LevelFiveEulerDissection

open MetaMathlibExt PowerSeries

local notation "ι" => algebraMap ℤ⟦X⟧ (FractionRing ℤ⟦X⟧)
local notation "f" => fun k ↦ ι (qEulerProduct k)
local notation "q" => ι X

private theorem euler_ne (k : ℕ) (hk : 1 ≤ k := by decide) : f k ≠ 0 := by
  apply (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
  intro h
  simpa [h] using constantCoeff_qEulerProduct hk

-- Recover the four quotients by dividing by the Euler products, all of which are units.
example :
    1 / (f 1 ^ 3 * f 5) =
      f 4 ^ 4 / (f 2 ^ 7 * f 10) - 2 * q * f 4 ^ 6 * f 20 ^ 2 / (f 2 ^ 9 * f 10 ^ 3) +
        5 * q * f 4 ^ 3 * f 20 / f 2 ^ 8 +
        2 * q ^ 2 * f 4 ^ 9 * f 40 ^ 2 / (f 2 ^ 10 * f 8 ^ 2 * f 10 ^ 2 * f 20) := by
  have h := congrArg ι one_div_f1_cube_f5_two_dissection
  simp only [map_mul, map_pow, map_sub, map_add, map_ofNat] at h
  field_simp [euler_ne 1, euler_ne 2, euler_ne 5, euler_ne 8, euler_ne 10, euler_ne 20]
  linear_combination h

-- Recover the original quotient identity in Sarmah and Gayan, equation (17).
example :
    f 2 ^ 3 * f 5 ^ 2 / (f 1 ^ 5 * f 10 ^ 2) =
      f 5 / (f 2 ^ 2 * f 10) + 5 * q * f 10 ^ 2 / (f 1 ^ 3 * f 2) := by
  have h := congrArg ι f2_cube_f5_sq_quotient_identity
  simp only [map_mul, map_pow, map_add, map_ofNat] at h
  field_simp [euler_ne 1, euler_ne 2, euler_ne 10]
  linear_combination h
