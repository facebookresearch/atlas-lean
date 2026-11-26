/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PseudoprimeBasesFermatNumbersFermatNumberStrongPseudoprimeBasesSubgroup

/-! # Tests for a subgroup of strong pseudoprime bases of a composite Fermat number -/

namespace MathlibExtTest.NumberTheory.PseudoprimeBasesFermatNumbersFermatNumberStrongPseudoprimeBasesSubgroup

open MetaMathlibExt

private theorem fermatNumber_five_not_prime :
    ¬(Nat.fermatNumber 5).Prime := by
  rw [show Nat.fermatNumber 5 = 641 * 6700417 by norm_num [Nat.fermatNumber]]
  exact Nat.not_prime_mul (by norm_num) (by norm_num)

-- The subgroup for `k = 5` has order `2 ^ (5 + 2) = 128`.
example :
    ∃ H : Subgroup (ZMod (Nat.fermatNumber 5))ˣ, Nat.card H = 128 := by
  obtain ⟨H, _, hcard, _⟩ :=
    fermatNumber_strongPseudoprime_bases_subgroup fermatNumber_five_not_prime
  exact ⟨H, by simpa using hcard⟩

-- `F_5` is a strong pseudoprime to the base `2`, which lies in `S_5` with `t = 1`.
example : IsStrongPseudoprime (Nat.fermatNumber 5) 2 := by
  obtain ⟨_, _, _, hspsp⟩ :=
    fermatNumber_strongPseudoprime_bases_subgroup fermatNumber_five_not_prime
  exact hspsp 2 (Or.inl ⟨1, (pow_one _).symm⟩)

-- `F_5` is a strong pseudoprime to `2 ^ 16 + 1`, which lies in `S_5` with `t = 0`.
example : IsStrongPseudoprime (Nat.fermatNumber 5) (2 ^ 16 + 1) := by
  obtain ⟨_, _, _, hspsp⟩ :=
    fermatNumber_strongPseudoprime_bases_subgroup fermatNumber_five_not_prime
  exact hspsp _ (Or.inr ⟨0, Or.inl rfl⟩)

end MathlibExtTest.NumberTheory.PseudoprimeBasesFermatNumbersFermatNumberStrongPseudoprimeBasesSubgroup
