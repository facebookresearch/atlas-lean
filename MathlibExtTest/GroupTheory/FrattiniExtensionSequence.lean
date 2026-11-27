/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.FrattiniExtensionSequence

open MathlibExt.GroupTheory.FrattiniExtensionSequenceKourovka16Problem12Wanted

/-- Along the chain from the Klein four-group, every step doubles the group order. -/
example : ∃ (S : ℕ → Type) (_ : ∀ i, Group (S i)),
    Nonempty (S 0 ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ∧
    (∀ i, IsPhiExtension 2 (S (i + 1)) (S i)) ∧ ∀ i, Nat.card (S i) = 4 * 2 ^ i := by
  let G := Multiplicative (ZMod 2) × Multiplicative (ZMod 2)
  have hcard : Nat.card G = 4 := by
    simp [G, Nat.card_eq_fintype_card, ZMod.card]
  have hG : IsPGroup 2 G := IsPGroup.of_card (n := 2) hcard
  obtain ⟨S, inst, ⟨e⟩, step⟩ :=
    phiExtensionSequence_holds 2 Nat.prime_two G hG inferInstance
  refine ⟨S, inst, ⟨e⟩, step, ?_⟩
  intro i
  induction i with
  | zero => simpa using (Nat.card_congr e.toEquiv).trans hcard
  | succ i ih =>
    obtain ⟨_, _, N, _, hN, _, ⟨q⟩⟩ := step i
    rw [← N.card_mul_index, hN, N.index_eq_card, Nat.card_congr q.toEquiv, ih, pow_succ]
    ac_rfl

/-- The trivial group cannot start such a chain. Its extension kernel would be the entire
group, forcing the Frattini subgroup to be the entire group as well. -/
example {p : ℕ} (hp : p.Prime) (H G : Type) [Group H] [Group G] [Subsingleton G] :
    ¬ IsPhiExtension p H G := by
  rintro ⟨_, _, N, _, hcard, hle, ⟨e⟩⟩
  have hindex : N.index = 1 := by
    rw [N.index_eq_card, Nat.card_congr e.toEquiv, Nat.card_unique]
  have htop := Subgroup.index_eq_one.mp hindex
  have hfr : frattini H = ⊤ := top_le_iff.mp (htop ▸ hle)
  have hbot : (⊥ : Subgroup H) = ⊤ := frattini_nongenerating (by simp [hfr])
  rw [htop, ← hbot, Subgroup.card_bot] at hcard
  exact hp.ne_one hcard.symm
