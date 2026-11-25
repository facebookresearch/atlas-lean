/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.PGroupFormationIndecomposableKourovka10Problem72

namespace MathlibExtTest.GroupTheory.PGroupFormationIndecomposableKourovka10Problem72

open MathlibExt.GroupTheory.PGroupFormationIndecomposableKourovka10Problem72Wanted

private def exponentTwo : GroupClass :=
  fun G _ _ => ∀ g : G, g ^ 2 = 1

private theorem exponentTwo_isFormation : IsFormation exponentTwo := by
  refine ⟨?_, fun _ => Subsingleton.elim _ _, ?_, ?_⟩
  · intro G H _ _ _ _ e h g
    obtain ⟨x, rfl⟩ := e.surjective g
    rw [← map_pow, h x, map_one]
  · intro G _ _ N _ h g
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N g
    rw [← map_pow, h x, map_one]
  · intro G _ _ N₁ N₂ _ _ h₁ h₂ g
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (N₁ ⊓ N₂) g
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff (x ^ 2)).mpr
    exact ⟨(QuotientGroup.eq_one_iff _).mp (by simpa using h₁ (QuotientGroup.mk' N₁ x)),
      (QuotientGroup.eq_one_iff _).mp (by simpa using h₂ (QuotientGroup.mk' N₂ x))⟩

private theorem exponentTwo_of_orderTwo : exponentTwo (Multiplicative (ZMod 2)) := by
  intro g
  have h : Nat.card (Multiplicative (ZMod 2)) = 2 := Nat.card_zmod 2
  simpa only [h] using (pow_card_eq_one' (x := g))

private theorem not_exponentTwo_of_orderFour : ¬ exponentTwo (Multiplicative (ZMod 4)) := by
  intro h
  have hne : (Multiplicative.ofAdd (1 : ZMod 4)) ^ 2 ≠ 1 := by decide
  exact hne (h (Multiplicative.ofAdd 1))

-- An actual proper, nontrivial formation gives witnesses for both factors.
example :
    ¬ ∀ (G : Type) [Group G] [Finite G], IsPGroup 2 G ↔
      exponentTwo (residual exponentTwo G) := by
  have hp (G : Type) [Group G] [Finite G] (h : exponentTwo G) : IsPGroup 2 G :=
    fun g => ⟨1, by simpa using h g⟩
  have hnontrivial : ∃ (G : Type) (_ : Group G) (_ : Finite G),
      Nontrivial G ∧ exponentTwo G :=
    ⟨Multiplicative (ZMod 2), inferInstance, inferInstance, inferInstance, exponentTwo_of_orderTwo⟩
  have hproper : ∃ (G : Type) (_ : Group G) (_ : Finite G), IsPGroup 2 G ∧ ¬ exponentTwo G :=
    ⟨Multiplicative (ZMod 4), inferInstance, inferInstance,
      IsPGroup.of_card (n := 2) (Nat.card_zmod 4), not_exponentTwo_of_orderFour⟩
  exact pGroupFormationIndecomposable_holds 2 Nat.prime_two exponentTwo exponentTwo
    exponentTwo_isFormation exponentTwo_isFormation hp hp hnontrivial hnontrivial hproper hproper

-- The residual is trivial on a member of the formation.
example : residual exponentTwo (Multiplicative (ZMod 2)) = ⊥ := by
  apply bot_unique
  refine iInf_le_of_le ⊥ (iInf_le _ ⟨inferInstance, ?_⟩)
  intro g
  apply QuotientGroup.quotientBot.injective
  rw [map_pow, map_one]
  exact exponentTwo_of_orderTwo _

-- On the cyclic group of order four the residual contains the nonidentity square.
example :
    (Multiplicative.ofAdd (1 : ZMod 4)) ^ 2 ∈ residual exponentTwo (Multiplicative (ZMod 4)) := by
  simp only [residual, Subgroup.mem_iInf]
  intro N hN
  obtain ⟨_, h⟩ := hN
  apply (QuotientGroup.eq_one_iff _).mp
  change QuotientGroup.mk' N (_ ^ 2) = 1
  rw [map_pow]
  exact h _

end MathlibExtTest.GroupTheory.PGroupFormationIndecomposableKourovka10Problem72
