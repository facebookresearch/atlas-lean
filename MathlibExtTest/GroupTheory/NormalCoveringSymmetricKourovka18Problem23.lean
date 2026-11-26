/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Finite.Perm
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
import MathlibExt.GroupTheory.NormalCoveringSymmetricKourovka18Problem23

open MathlibExt.GroupTheory.NormalCoveringSymmetricKourovka18Problem23Wanted

-- Degenerate inputs and the four branches of the conjectured formula.
example : conjecturedValue 0 = 2 := by decide +kernel
example : conjecturedValue 1 = 2 := by decide +kernel
example : conjecturedValue 3 = 1 := by decide +kernel
example : conjecturedValue 9 = 4 := by decide +kernel
example : conjecturedValue 15 = 5 := by decide +kernel
example : conjecturedValue 45 = 14 := by decide +kernel

-- The empty covering search has the documented value in degree one.
example : normalCoveringNumber 1 = 0 := by
  unfold normalCoveringNumber
  apply Nat.sInf_eq_zero.mpr
  right
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro k ⟨H, hproper, hcover⟩
  obtain ⟨i, -⟩ := hcover 1
  exact hproper i (Subsingleton.elim _ _)

-- In degree two, the only proper subgroup is trivial and misses the transposition.
example : normalCoveringNumber 2 = 0 := by
  unfold normalCoveringNumber
  apply Nat.sInf_eq_zero.mpr
  right
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro k ⟨H, hproper, hcover⟩
  have : Fact (Nat.card (Equiv.Perm (Fin 2))).Prime :=
    ⟨by simpa only [Nat.card_perm, Nat.card_fin, Nat.factorial_two] using Nat.prime_two⟩
  obtain ⟨σ, hσ⟩ := exists_ne (1 : Equiv.Perm (Fin 2))
  obtain ⟨i, τ, hτ, hc⟩ := hcover σ
  rw [(H i).eq_bot_or_eq_top_of_prime_card.resolve_right (hproper i), Subgroup.mem_bot] at hτ
  subst τ
  exact hσ (isConj_one_left.mp hc)

example (N : ℕ) : ∃ n ≥ N, (normalCoveringNumber n : ℚ) ≠ conjecturedValue n := by
  by_contra! h
  exact normalCoveringNumberEventuallyConjectured_refuted ⟨N, h⟩
