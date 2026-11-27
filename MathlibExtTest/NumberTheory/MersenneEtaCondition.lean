/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum.LegendreSymbol
import MathlibExt.NumberTheory.MersenneEtaCondition

namespace MetaMathlibExt.exists_not_mersenneEtaCondition_of_plus

-- For seed 6 both odd squarefree parts are one, so the adjusted order is two
-- and one is the only reduced residue.
example : ¬ MersenneEtaCondition 1 1 1 := by
  obtain ⟨n, hlo, hhi, _, hn⟩ :=
    exists_not_mersenneEtaCondition_of_plus 6 (hs₁ := by decide) 1 1
      ⟨by decide, squarefree_one, 2, 1, by decide⟩
      ⟨by decide, squarefree_one, 3, 1, by decide⟩ (by decide)
  have hΩ : mersenneOmega 1 = 2 := by
    rw [mersenneOmega, Subsingleton.elim (2 : ZMod 1) 1, orderOf_one]
    decide
  rw [Nat.one_mul, hΩ] at hhi
  simpa only [show n = 1 by omega] using hn

-- For seed 3 the plus part is five. Among the reduced residues modulo four,
-- one fails the condition and three satisfies it.
example : ¬ MersenneEtaCondition 1 5 1 ∧ MersenneEtaCondition 1 5 3 := by
  norm_num [MersenneEtaCondition, mersenne]

end MetaMathlibExt.exists_not_mersenneEtaCondition_of_plus

namespace MetaMathlibExt.mersenneEtaCondition_not_all_of_odd

-- For seed 3 the odd squarefree parts are one and five, the adjusted order is
-- four, and the count of reduced residues satisfying the condition is not
-- `Nat.totient 4 = 2`.
example :
    {n | n ∈ Finset.Ico 1 4 ∧ n.Coprime 4 ∧ MersenneEtaCondition 1 5 n}.ncard ≠ 2 := by
  have hΩ : mersenneOmega 5 = 4 := by
    have h : orderOf (2 : ZMod 5) = 4 := by
      rw [orderOf_eq_iff (by norm_num)]
      refine ⟨by decide, fun m hm hm0 => ?_⟩
      interval_cases m <;> decide
    rw [mersenneOmega, h]
    decide
  have h := mersenneEtaCondition_not_all_of_odd 3 (by decide) (by decide) 1 5
    ⟨by decide, squarefree_one, 0, 1, by norm_num⟩
    ⟨by decide, Nat.prime_five.prime.squarefree, 0, 1, by norm_num⟩
  have ht : Nat.totient 4 = 2 := by decide
  simp only [Nat.one_mul, hΩ, ht] at h
  exact h

end MetaMathlibExt.mersenneEtaCondition_not_all_of_odd
