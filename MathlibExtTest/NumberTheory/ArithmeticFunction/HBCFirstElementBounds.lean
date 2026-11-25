/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.HBCFirstElementBounds

open MetaMathlibExt

-- The first inequality is sharp at length one.
example : (2 : ℕ) ≤ 1 + 1 := by
  exact (hbcAdmissible_half_first_le 1 (by decide) (fun _ ↦ 2)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)).1

private def threeOdds (i : Fin 3) : ℕ := ([3, 5, 7] : List ℕ)[i.val]'i.isLt

-- Squaring the factors gives the strict bound for odd tuples.
example : (threeOdds 0 : ℚ) < 2 * (3 + 3) / 3 := by
  have hmono : StrictMono threeOdds := by
    change ∀ i j : Fin 3, i < j → threeOdds i < threeOdds j
    decide +kernel
  exact (hbcAdmissible_half_first_le 3 (by decide) threeOdds hmono
    (by decide +kernel) (by decide +kernel) (by decide +kernel)).2.1 (by decide +kernel)

private def sevenPrimes (i : Fin 7) : ℕ :=
  ([5, 7, 11, 13, 17, 19, 23] : List ℕ)[i.val]'i.isLt

-- This prefix crosses 1/2 on its last term, with first prime 5 > 3.
example : (sevenPrimes 0 : ℚ) < 3 * 7 / 7 + 3 := by
  have hmono : StrictMono sevenPrimes := by
    change ∀ i j : Fin 7, i < j → sevenPrimes i < sevenPrimes j
    decide +kernel
  exact (hbcAdmissible_half_first_le 7 (by decide) sevenPrimes hmono
    (by decide +kernel) (by decide +kernel) (by decide +kernel)).2.2 (by decide +kernel)
