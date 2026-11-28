/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.ZMod.Basic
import MathlibExt.NumberTheory.TruncatedLogResultantPrimePower

open MetaMathlibExt
open MetaMathlibExt.not_isSquare_discr_truncatedLog_three_five_seven_mul

example : ¬ (5 : ℤ) ∣ truncatedLogResultantProduct 5 :=
  not_dvd_truncatedLogResultantProduct_of_prime_power (p := 5) (e := 1)
    (hp := by decide) (hp4 := by decide) (he := by decide)

example : ¬ (5 : ℤ) ∣ truncatedLogResultantProduct 25 :=
  not_dvd_truncatedLogResultantProduct_of_prime_power (p := 5) (e := 2)
    (hp := by decide) (hp4 := by decide) (he := by decide)

-- The even-power theorem also applies to primes congruent to 3 modulo 4.
example : ¬ (3 : ℤ) ∣ truncatedLogResultantProduct 9 :=
  not_dvd_truncatedLogResultantProduct_of_even_power (p := 3) (e := 1)
    (hp := by decide) (hp2 := by decide) (he := by decide)

example : ¬ (5 : ℤ) ∣ truncatedLogResultantProduct 625 :=
  not_dvd_truncatedLogResultantProduct_of_even_power (p := 5) (e := 2)
    (hp := by decide) (hp2 := by decide) (he := by decide)

-- Compute the exact residue using the public formula and L₉ = 2520.
example : (truncatedLogResultantProduct 9 : ZMod 3) = 1 := by
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  rw [mod_resultant_monomial (p := 3) (e := 2) (n := 9)
    (by decide) (by decide) (by decide) (by decide), truncatedLogLcm_nine]
  decide
