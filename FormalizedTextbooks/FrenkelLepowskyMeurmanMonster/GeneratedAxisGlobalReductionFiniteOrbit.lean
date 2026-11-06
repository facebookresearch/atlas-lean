/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.Data.Fintype.Card

/-! Finite orbit certificates with genuine generator actions and descending
parent edges. Closure and reachability prove both inclusions in the orbit. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- A finite injective carrier preserved by each generator is preserved by their full subgroup. -/
theorem generatedAxisGlobalFiniteCarrier_preserved
    {Γ V κ : Type*} [Group Γ] [MulAction Γ V]
    {m : ℕ} (gen : κ → Γ) (v : Fin m → V) (hv : Function.Injective v)
    (hgen : ∀ k i, ∃ j, gen k • v i = v j)
    (g : Γ) (hg : g ∈ Subgroup.closure (Set.range gen)) :
    ∀ i, ∃ j, g • v i = v j := by
  induction hg using Subgroup.closure_induction with
  | mem g hg => obtain ⟨k, rfl⟩ := hg; exact hgen k
  | one => intro i; exact ⟨i, one_smul _ _⟩
  | mul g h _ _ ihg ihh =>
      intro i
      obtain ⟨j, hj⟩ := ihh i
      obtain ⟨k, hk⟩ := ihg j
      exact ⟨k, by rw [mul_smul, hj, hk]⟩
  | inv g _ ih =>
      classical
      let f : Fin m → Fin m := fun i => Classical.choose (ih i)
      have hf : ∀ i, g • v i = v (f i) := fun i => Classical.choose_spec (ih i)
      have hinj : Function.Injective f := by
        intro i j hij
        apply hv
        apply MulAction.injective g
        change g • v i = g • v j
        rw [hf, hf, hij]
      have hsurj : Function.Surjective f := Finite.surjective_of_injective hinj
      intro i
      obtain ⟨j, hj⟩ := hsurj i
      refine ⟨j, ?_⟩
      rw [← hj, ← hf, inv_smul_smul]

/-- Strictly descending parent edges give genuine reachability from the declared root. -/
theorem generatedAxisGlobalFiniteCarrier_reachable
    {Γ V κ : Type*} [Group Γ] [MulAction Γ V]
    {m : ℕ} (gen : κ → Γ) (v : Fin m → V) (base : Fin m) (rank : Fin m → ℕ)
    (hedge : ∀ i, i = base ∨ ∃ j k, rank j < rank i ∧ gen k • v j = v i) :
    ∀ i, ∃ g : Γ, g ∈ Subgroup.closure (Set.range gen) ∧ g • v base = v i := by
  have hmain : ∀ n i, rank i = n →
      ∃ g : Γ, g ∈ Subgroup.closure (Set.range gen) ∧ g • v base = v i := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i hi
      rcases hedge i with rfl | ⟨j, k, hj, he⟩
      · exact ⟨1, Subgroup.one_mem _, one_smul _ _⟩
      · obtain ⟨g, hg, hgi⟩ := ih (rank j) (hi ▸ hj) j rfl
        exact ⟨gen k * g, Subgroup.mul_mem _ (Subgroup.subset_closure ⟨k, rfl⟩) hg,
          by rw [mul_smul, hgi, he]⟩
  intro i
  exact hmain (rank i) i rfl

/-- A finite carrier with checked closure, injectivity, and descending edges is the entire orbit. -/
theorem generatedAxisGlobalFiniteCarrier_orbit
    {Γ V κ : Type*} [Group Γ] [MulAction Γ V]
    {m : ℕ} (gen : κ → Γ) (v : Fin m → V) (base : Fin m) (rank : Fin m → ℕ)
    (hv : Function.Injective v) (hgen : ∀ k i, ∃ j, gen k • v i = v j)
    (hedge : ∀ i, i = base ∨ ∃ j k, rank j < rank i ∧ gen k • v j = v i) :
    MulAction.orbit (Subgroup.closure (Set.range gen)) (v base) = Set.range v := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨i, hi⟩ := generatedAxisGlobalFiniteCarrier_preserved gen v hv hgen g.val g.property base
    exact ⟨i, hi.symm⟩
  · rintro ⟨i, rfl⟩
    obtain ⟨g, hg, he⟩ := generatedAxisGlobalFiniteCarrier_reachable gen v base rank hedge i
    exact ⟨⟨g, hg⟩, he⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
