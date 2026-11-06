/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalExactness
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalStructure
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedSubgroups
public import Mathlib.GroupTheory.Index

/-! Concrete order constraints from the local exact sequence.

The formulas count the actual kernel and embed H into the generated group.
The final helper assumes finiteness explicitly to make the generated group
order positive. No milestone theorem proof is imported. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

theorem projH_kernel_card : Nat.card projH.ker = 2 ^ 25 := by
  rw [← inclQ_range_eq_projH_ker]
  rw [← Nat.card_congr (MonoidHom.ofInjective inclQ_injective).toEquiv]
  exact q_card

/-- Counting the actual exact sequence, with the concrete extraspecial kernel. -/
theorem h_card : Nat.card H = 2 ^ 25 * Nat.card Co1 := by
  have h := projH.ker.card_mul_index
  rw [Subgroup.index_ker, (MonoidHom.range_eq_top.mpr projH_surjective),
    Subgroup.card_top, projH_kernel_card] at h
  exact h.symm

theorem h_card_dvd_generated_card : Nat.card H ∣ Nat.card G :=
  Subgroup.card_dvd_of_injective localIntoGenerated localIntoGenerated_injective

theorem extraspecial_order_dvd_generated_card : 2 ^ 25 ∣ Nat.card G := by
  rw [← q_card]
  exact Subgroup.card_dvd_of_injective qIntoGenerated qIntoGenerated_injective

/-- For a finite generated group the divisor constraints are actual positive group orders. -/
theorem generated_card_divisors [Finite G] :
    0 < Nat.card G ∧ 2 ^ 25 * Nat.card Co1 ∣ Nat.card G ∧ 2 ^ 25 ∣ Nat.card G := by
  refine ⟨Nat.card_pos, ?_, extraspecial_order_dvd_generated_card⟩
  rw [← h_card]
  exact h_card_dvd_generated_card

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
