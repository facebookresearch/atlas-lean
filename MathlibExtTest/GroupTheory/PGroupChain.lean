/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.PGroupChain
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.PGroup

@[expose] public section

/-!
# Examples for the composition series of finite `p`-groups

Exercises `IsPGroup.exists_chain_zmod_p_quotients` and `IsPGroup.isSolvable` on
the cyclic groups of order eight, two, and one.
-/

/-- The cyclic group of order eight is a `2`-group. -/
example : IsPGroup 2 (Multiplicative (ZMod 8)) := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  rw [IsPGroup.iff_card]
  exact ⟨3, by simp [Nat.card_eq_fintype_card, ZMod.card]⟩

/-- A finite `2`-group is solvable: the cyclic group of order eight. -/
example : Group.IsSolvable (Multiplicative (ZMod 8)) := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hG : IsPGroup 2 (Multiplicative (ZMod 8)) := by
    rw [IsPGroup.iff_card]
    exact ⟨3, by simp [Nat.card_eq_fintype_card, ZMod.card]⟩
  exact hG.isSolvable

/-- The chain for the cyclic group of order eight starts at `⊤` and ends at `⊥`. -/
example : ∃ H : Fin 4 → Subgroup (Multiplicative (ZMod 8)), H 0 = ⊤ ∧ H (Fin.last 3) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hG : IsPGroup 2 (Multiplicative (ZMod 8)) := by
    rw [IsPGroup.iff_card]
    exact ⟨3, by simp [Nat.card_eq_fintype_card, ZMod.card]⟩
  obtain ⟨H, h0, hlast, _⟩ := hG.exists_chain_zmod_p_quotients (n := 3) (by
    simp [Nat.card_eq_fintype_card, ZMod.card])
  exact ⟨H, h0, hlast⟩

/-- The first step of the chain for `C₂` gives a surjective map onto `ZMod 2`
whose kernel is the next term of the chain. -/
example : ∃ H : Fin 2 → Subgroup (Multiplicative (ZMod 2)),
    ∃ φ : ↥(H 0) →* Multiplicative (ZMod 2),
      Function.Surjective φ ∧ φ.ker = (H 1).subgroupOf (H 0) := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hG : IsPGroup 2 (Multiplicative (ZMod 2)) := by
    rw [IsPGroup.iff_card]
    exact ⟨1, by simp [Nat.card_eq_fintype_card, ZMod.card]⟩
  obtain ⟨H, _, _, hstep⟩ := hG.exists_chain_zmod_p_quotients (n := 1) (by
    simp [Nat.card_eq_fintype_card, ZMod.card])
  obtain ⟨_, _, φ, hsurj, hker⟩ := hstep 0
  exact ⟨H, φ, hsurj, hker⟩

/-- The trivial group has the empty chain (length `1`). -/
example : ∃ H : Fin 1 → Subgroup (Multiplicative (ZMod 1)), H 0 = ⊤ ∧ H (Fin.last 0) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hG : IsPGroup 2 (Multiplicative (ZMod 1)) := by
    rw [IsPGroup.iff_card]
    exact ⟨0, by simp [Nat.card_eq_fintype_card]⟩
  obtain ⟨H, h0, hlast, _⟩ := hG.exists_chain_zmod_p_quotients (n := 0) (by
    simp [Nat.card_eq_fintype_card])
  exact ⟨H, h0, hlast⟩
