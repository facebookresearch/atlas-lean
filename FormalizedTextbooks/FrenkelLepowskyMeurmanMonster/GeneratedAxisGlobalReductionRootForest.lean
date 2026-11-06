/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.GroupTheory.GroupAction.Basic

/-! A descending forest can have several roots without storing an independent
orbit label. Every path is a word in the actual acting generators. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- A multi-root forest of actual generator edges gives subgroup orbit coverage. -/
theorem generatedAxisGlobalRootForest_cover
    {Γ V κ ρ : Type*} [Group Γ] [MulAction Γ V]
    (gen : κ → Γ) (root : ρ → V) (valid : V → Prop) (rank : V → ℕ)
    (hedge : ∀ x, valid x → (∃ r, root r = x) ∨
      ∃ y k, valid y ∧ rank y < rank x ∧ gen k • y = x) :
    ∀ x, valid x → ∃ r g,
      g ∈ Subgroup.closure (Set.range gen) ∧ g • root r = x := by
  have hmain : ∀ n x, rank x = n → valid x → ∃ r g,
      g ∈ Subgroup.closure (Set.range gen) ∧ g • root r = x := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hx hv
      rcases hedge x hv with ⟨r, hr⟩ | ⟨y, k, hy, hlt, he⟩
      · exact ⟨r, 1, Subgroup.one_mem _, by rw [one_smul, hr]⟩
      · obtain ⟨r, g, hg, hgr⟩ := ih (rank y) (hx ▸ hlt) y rfl hy
        refine ⟨r, gen k * g,
          Subgroup.mul_mem _ (Subgroup.subset_closure ⟨k, rfl⟩) hg, ?_⟩
        rw [mul_smul, hgr, he]
  intro x hv
  exact hmain (rank x) x rfl hv

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
