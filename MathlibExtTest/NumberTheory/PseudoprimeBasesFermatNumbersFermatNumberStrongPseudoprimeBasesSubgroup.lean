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

-- The subgroup membership equivalence at `k = 5`: the unit `65535 = 2 ^ 16 - 1`, the base
-- `2 ^ (2 ^ 4 + 0) - 2 ^ 0` of `S_5`, lies in the returned subgroup.
example : ∃ (H : Subgroup (ZMod (Nat.fermatNumber 5))ˣ) (u : (ZMod (Nat.fermatNumber 5))ˣ),
    u ∈ H ∧ (u : ZMod (Nat.fermatNumber 5)) = 65535 := by
  obtain ⟨H, hmem, _, _⟩ :=
    fermatNumber_strongPseudoprime_bases_subgroup fermatNumber_five_not_prime
  have hcop : Nat.Coprime 65535 (Nat.fermatNumber 5) := by
    norm_num [Nat.fermatNumber]
  refine ⟨H, ZMod.unitOfCoprime 65535 hcop, ?_, by simp⟩
  rw [hmem]
  refine Or.inr ⟨0, Or.inr ?_⟩
  rw [ZMod.coe_unitOfCoprime]
  norm_num

-- The paper's `448911555` is a strong base of `F_5` outside the returned subgroup. Since `2` has
-- order `64`, it suffices to check the three expressions for each exponent from `0` through `63`.
example : ∃ H : Subgroup (ZMod (Nat.fermatNumber 5))ˣ,
    ∀ u ∈ H, (u : ZMod (Nat.fermatNumber 5)) ≠ 448911555 := by
  obtain ⟨H, hmem, _, _⟩ :=
    fermatNumber_strongPseudoprime_bases_subgroup fermatNumber_five_not_prime
  refine ⟨H, fun u hu hu' => ?_⟩
  have h64 : (2 : ZMod (Nat.fermatNumber 5)) ^ 64 = 1 := by decide +kernel
  have hper : ∀ t : ℕ, (2 : ZMod (Nat.fermatNumber 5)) ^ t = 2 ^ (t % 64) := fun t => by
    conv_lhs => rw [← Nat.div_add_mod t 64, pow_add, pow_mul, h64, one_pow, one_mul]
  have hfin : ∀ r : Fin 64,
      (2 : ZMod (Nat.fermatNumber 5)) ^ (r : ℕ) ≠ 448911555 ∧
      (2 : ZMod (Nat.fermatNumber 5)) ^ (r : ℕ) * (2 ^ 16 + 1) ≠ 448911555 ∧
      (2 : ZMod (Nat.fermatNumber 5)) ^ (r : ℕ) * (2 ^ 16 - 1) ≠ 448911555 := by
    decide +kernel
  have hS := (hmem u).mp hu
  rcases hS with ⟨t, ht⟩ | ⟨t, ht | ht⟩
  · exact (hfin ⟨t % 64, Nat.mod_lt _ (by norm_num)⟩).1 (by rw [← hu', ht, hper t])
  · refine (hfin ⟨t % 64, Nat.mod_lt _ (by norm_num)⟩).2.1 ?_
    rw [← hu', ht, pow_add, ← hper t]
    ring
  · refine (hfin ⟨t % 64, Nat.mod_lt _ (by norm_num)⟩).2.2 ?_
    rw [← hu', ht, pow_add, ← hper t]
    ring

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
