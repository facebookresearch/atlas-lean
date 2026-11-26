/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.Partition.RegularTripartitionCongruencesQPochhammerPrimeDissection

/-!
# Tests for the Cui–Gu `p`-dissection of `f_1`

This module tests `MetaMathlibExt.qPochhammer_prime_dissection` on the concrete prime
`p = 5` at `q = 0`, deriving that the right-hand side equals `1`.
-/

@[expose] public section

namespace MathlibExtTest.Combinatorics.Enumerative.Partition.RegularTripartitionCongruencesQPochhammerPrimeDissection

open MetaMathlibExt

private theorem raw_zero : QPochhammer.qPochhammerInfRaw 0 0 = 1 := by
  have hfun : (fun n : ℕ => (1 : ℂ) - 0 * (0 : ℂ) ^ n) = fun _ => 1 := by
    funext n
    simp
  unfold QPochhammer.qPochhammerInfRaw
  rw [hfun, tprod_one]

theorem dissection_five_at_zero :
    (∑ k ∈ (Finset.Icc ((1 - (5 : ℤ)) / 2) (((5 : ℤ) - 1) / 2)).erase (-1),
          (-1 : ℂ) ^ k * (0 : ℂ) ^ (k * (3 * k + 1) / 2).toNat *
            ramanujanThetaRaw (-(0 : ℂ) ^ ((3 * (5 : ℤ) ^ 2 + (6 * k + 1) * 5) / 2).toNat)
              (-(0 : ℂ) ^ ((3 * (5 : ℤ) ^ 2 - (6 * k + 1) * 5) / 2).toNat) +
        (-1 : ℂ) ^ (-1 : ℤ) * (0 : ℂ) ^ ((5 ^ 2 - 1) / 24) *
          QPochhammer.qPochhammerInfRaw ((0 : ℂ) ^ (5 ^ 2)) ((0 : ℂ) ^ (5 ^ 2))) = 1 := by
  have hprime : Nat.Prime 5 := by decide
  have hs : (-1 : ℤ) = if 5 % 6 = 1 then ((5 : ℤ) - 1) / 6 else (-(5 : ℤ) - 1) / 6 := by
    decide
  have hq : ‖(0 : ℂ)‖ < 1 := by simp
  have hmain := MetaMathlibExt.qPochhammer_prime_dissection 5 hprime le_rfl (-1) hs 0 hq
  rw [raw_zero] at hmain
  exact hmain.symm

end MathlibExtTest.Combinatorics.Enumerative.Partition.RegularTripartitionCongruencesQPochhammerPrimeDissection
