/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum.LegendreSymbol
import MathlibExt.NumberTheory.LucasLehmerRationalSeedExistsNotMersenneEtaConditionOfMinus

namespace MathlibExtTest.NumberTheory.LucasLehmerRationalSeedExistsNotMersenneEtaConditionOfMinus

open MetaMathlibExt

-- For seed 14 both odd squarefree parts are tiny (3 and 1), so the adjusted order is two
-- and one is the only reduced residue.
example : ¬ MersenneEtaCondition 3 1 1 := by
  obtain ⟨n, hlo, hhi, _, hn⟩ :=
    exists_not_mersenneEtaCondition_of_minus 14 (hs₁ := by decide) 3 1
      ⟨by decide, Nat.prime_three.prime.squarefree, 2, 1, by decide⟩
      ⟨by decide, squarefree_one, 4, 1, by decide⟩ (by decide)
  have hord : orderOf (2 : ZMod 3) = 2 := orderOf_eq_prime (by decide) (by decide)
  have hΩ : mersenneOmega (3 * 1) = 2 := by
    rw [Nat.mul_one, mersenneOmega, hord]
    decide
  rw [hΩ] at hhi
  simpa only [show n = 1 by omega] using hn

-- For seed 5 the odd squarefree parts are 3 and 7, so the adjusted order is six and one
-- of the reduced residues 1 and 5 fails condition (etar).
example : ¬ MersenneEtaCondition 3 7 1 ∨ ¬ MersenneEtaCondition 3 7 5 := by
  obtain ⟨n, hlo, hhi, hcop, hn⟩ :=
    exists_not_mersenneEtaCondition_of_minus 5 (hs₁ := by decide) 3 7
      ⟨by decide, Nat.prime_three.prime.squarefree, 0, 1, by decide⟩
      ⟨by decide, Nat.prime_seven.prime.squarefree, 0, 1, by decide⟩ (by decide)
  have hord : orderOf (2 : ZMod 21) = 6 := by
    rw [orderOf_eq_iff (by norm_num)]
    refine ⟨by decide, fun m hm hm0 => ?_⟩
    interval_cases m <;> decide
  have hΩ : mersenneOmega (3 * 7) = 6 := by
    rw [show (3 : ℕ) * 7 = 21 by norm_num, mersenneOmega, hord]
    decide
  rw [hΩ] at hhi hcop
  interval_cases n
  · exact Or.inl hn
  · exact absurd hcop (by decide)
  · exact absurd hcop (by decide)
  · exact absurd hcop (by decide)
  · exact Or.inr hn

end MathlibExtTest.NumberTheory.LucasLehmerRationalSeedExistsNotMersenneEtaConditionOfMinus
