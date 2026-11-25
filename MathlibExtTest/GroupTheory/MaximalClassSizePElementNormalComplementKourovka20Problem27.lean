/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.MaximalClassSizePElementNormalComplementKourovka20Problem27
import Mathlib.GroupTheory.SpecificGroups.Alternating

open MathlibExt.GroupTheory.MaximalClassSizePElementNormalComplementKourovka20Problem27Wanted

-- In S₃ the even permutations do give a normal 2-complement.
example : HasNormalPComplement 2 (Equiv.Perm (Fin 3)) := by
  obtain ⟨P⟩ := Sylow.nonempty (p := 2) (G := Equiv.Perm (Fin 3))
  have hG : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_perm, Nat.card_fin]
    decide
  have hA : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hP : Nat.card P = 2 := by
    rw [P.card_eq_multiplicity, hG]
    change 2 ^ (2 * 3).factorization 2 = 2
    rw [Nat.factorization_mul_apply_of_coprime (by decide), Nat.prime_two.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 3)]
    decide
  refine ⟨alternatingGroup (Fin 3), P, inferInstance, Subgroup.isComplement'_of_coprime ?_ ?_⟩
  · rw [hA, hP, hG]
  · rw [hA, hP]
    decide
