/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum.Prime
import MathlibExt.NumberTheory.FermatNumberSquareFactors
import MathlibExt.NumberTheory.FermatNumbersModPrime

/-! # Tests for squared prime factors of Fermat numbers -/

open MetaMathlibExt

-- At the initial index, 3 divides F₀, but 2² is not 1 modulo 9.
example : ¬ 3 ^ 2 ∣ Nat.fermatNumber 0 := by
  apply mt (sq_dvd_fermatNumber_iff (p := 3) (n := 0) (by decide) (by decide)).mp
  decide

-- The proper prime factor 641 of F₅ occurs only once, ruling out the congruence modulo 641².
example : ¬ 2 ^ (641 - 1) ≡ 1 [MOD 641 ^ 2] := by
  apply mt (sq_dvd_fermatNumber_iff (p := 641) (n := 5) (by norm_num) (by decide)).mpr
  decide

-- The order condition holds for 3 at n = 0, so failure of square divisibility rules out Wieferich.
example : ¬ (3 : ℕ).IsWieferichPrime := by
  have hp : Nat.Prime 3 := by decide
  have horder := (prime_dvd_fermatNumber_iff_orderOf_two 0 3 hp (by decide)).mp (by decide)
  intro hw
  exact (by decide : ¬ 3 ^ 2 ∣ Nat.fermatNumber 0)
    ((sq_dvd_fermatNumber_iff_wieferich_orderOf hp (by decide)).mpr ⟨hw, horder⟩)

-- The Wieferich condition holds for 1093, but its order excludes square divisibility at n = 0.
set_option exponentiation.threshold 2048 in
set_option maxRecDepth 100000 in
example : (1093 : ℕ).IsWieferichPrime ∧ ¬ 1093 ^ 2 ∣ Nat.fermatNumber 0 := by
  have hp : Nat.Prime 1093 := by norm_num
  refine ⟨(Nat.isWieferichPrime_iff_modEq 1093).mpr ⟨hp, by decide⟩, ?_⟩
  intro h
  have horder := ((sq_dvd_fermatNumber_iff_wieferich_orderOf hp (by decide)).mp h).2
  have hpow := pow_orderOf_eq_one (2 : ZMod 1093)
  rw [horder] at hpow
  exact (by decide : (2 : ZMod 1093) ^ 2 ≠ 1) hpow
