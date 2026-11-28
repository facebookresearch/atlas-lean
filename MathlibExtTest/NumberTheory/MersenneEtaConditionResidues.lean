/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum.LegendreSymbol
import MathlibExt.NumberTheory.MersenneEtaConditionResidues

/-! # Tests for the squarefree-part residues of Lucas–Lehmer seeds -/

open MetaMathlibExt

-- For seed 5 the minus residue alone is wrong.
example :
    {n | n ∈ Finset.Ico 1 (mersenneOmega (3 * 7)) ∧
        n.Coprime (mersenneOmega (3 * 7)) ∧ MersenneEtaCondition 3 7 n}.ncard ≠
      Nat.totient (mersenneOmega (3 * 7)) := by
  intro hq
  have h := minus_mod_four_of_mersenneEtaCondition_all 5 (by decide) 3 7
    ⟨by decide, Nat.prime_three.prime.squarefree, 0, 1, by decide⟩
    ⟨by decide, Nat.prime_seven.prime.squarefree, 0, 1, by decide⟩ hq
  exact (by decide : ¬ 3 % 4 = 1) h.1

-- For seed 3 the plus residue alone is wrong.
example :
    {n | n ∈ Finset.Ico 1 (mersenneOmega (1 * 5)) ∧
        n.Coprime (mersenneOmega (1 * 5)) ∧ MersenneEtaCondition 1 5 n}.ncard ≠
      Nat.totient (mersenneOmega (1 * 5)) := by
  intro hq
  have h := minus_mod_four_of_mersenneEtaCondition_all 3 (by decide) 1 5
    ⟨by decide, squarefree_one, 0, 1, by decide⟩
    ⟨by decide, Nat.prime_five.prime.squarefree, 0, 1, by decide⟩ hq
  exact (by decide : ¬ 5 % 4 = 3) h.2

-- For Lehmer's seed 10, the sole reduced residue modulo two qualifies.
example : (1 : ℕ) % 4 = 1 ∧ (3 : ℕ) % 4 = 3 := by
  have hΩ : mersenneOmega (1 * 3) = 2 := by
    have h : orderOf (2 : ZMod 3) = 2 := orderOf_eq_prime (by decide) (by decide)
    rw [Nat.one_mul, mersenneOmega, h]
    decide
  have hA : {n | n ∈ Finset.Ico 1 2 ∧ n.Coprime 2 ∧ MersenneEtaCondition 1 3 n} =
      ({1} : Set ℕ) := by
    ext n
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨hlo, hhi⟩, -⟩
      omega
    · rintro rfl
      exact ⟨⟨by decide, by decide⟩, by decide, by norm_num [MersenneEtaCondition, mersenne]⟩
  exact minus_mod_four_of_mersenneEtaCondition_all 10 (by decide) 1 3
    ⟨by decide, squarefree_one, 3, 1, by decide⟩
    ⟨by decide, Nat.prime_three.prime.squarefree, 2, 1, by decide⟩ (by
      rw [hΩ, hA, Set.ncard_singleton]
      decide)
