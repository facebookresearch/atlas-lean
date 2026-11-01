/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientOrthogonal
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionPairOrbit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Finiteness
public import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-! Double counting of orthogonal pairs between two actual local orbits.

For a group action preserving a binary relation, the relation pairs between two
finite orbits are counted from either side. For the actual local group H acting
on the Griess space and the relation of orthogonality for the actual Griess form,
the number of orthogonal partners of the first axis inside the H orbit of a vector
`x` is determined by the H orbit size of `x` and the number of the 196560 actual
signed-short axes orthogonal to `x`. This is the counting step of the feasible
coverage argument; no orbit size or classification is assumed. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

section Abstract

variable {K α : Type*} [Group K] [MulAction K α]

private theorem orbit_smul_mem_iff (k : K) (x₀ x : α) :
    k • x ∈ MulAction.orbit K x₀ ↔ x ∈ MulAction.orbit K x₀ := by
  constructor
  · intro h
    simpa only [inv_smul_smul] using MulAction.mem_orbit_of_mem_orbit k⁻¹ h
  · exact MulAction.mem_orbit_of_mem_orbit k

/-- Relation pairs between two finite orbits of an invariant relation, counted from
both sides: `|K·y₀| · #{x ∈ K·x₀ | R y₀ x} = |K·x₀| · #{y ∈ K·y₀ | R y x₀}`. -/
theorem generatedFeasibleAmbient_orbit_double_count (R : α → α → Prop)
    (hR : ∀ (k : K) (y x : α), R (k • y) (k • x) ↔ R y x) (y₀ x₀ : α)
    (hy : (MulAction.orbit K y₀).Finite) (hx : (MulAction.orbit K x₀).Finite) :
    Nat.card (MulAction.orbit K y₀) * Nat.card {x | x ∈ MulAction.orbit K x₀ ∧ R y₀ x} =
      Nat.card (MulAction.orbit K x₀) * Nat.card {y | y ∈ MulAction.orbit K y₀ ∧ R y x₀} := by
  classical
  set Y := hy.toFinset with hY
  set O := hx.toFinset with hO
  have hYm (y : α) : y ∈ Y ↔ y ∈ MulAction.orbit K y₀ := Set.Finite.mem_toFinset hy
  have hOm (x : α) : x ∈ O ↔ x ∈ MulAction.orbit K x₀ := Set.Finite.mem_toFinset hx
  have habove : ∀ y ∈ Y, (O.bipartiteAbove R y).card = (O.bipartiteAbove R y₀).card := by
    intro y hy'
    obtain ⟨k, rfl⟩ := (hYm y).mp hy'
    symm
    refine Finset.card_equiv (MulAction.toPerm k) ?_
    intro x
    simp only [Finset.mem_bipartiteAbove, hOm, MulAction.toPerm_apply, orbit_smul_mem_iff, hR]
  have hbelow : ∀ x ∈ O, (Y.bipartiteBelow R x).card = (Y.bipartiteBelow R x₀).card := by
    intro x hx'
    obtain ⟨k, rfl⟩ := (hOm x).mp hx'
    symm
    refine Finset.card_equiv (MulAction.toPerm k) ?_
    intro y
    simp only [Finset.mem_bipartiteBelow, hYm, MulAction.toPerm_apply, orbit_smul_mem_iff, hR]
  have hmain := Finset.card_mul_eq_card_mul R habove hbelow
  have hcY : Nat.card (MulAction.orbit K y₀) = Y.card := by
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hy]
  have hcO : Nat.card (MulAction.orbit K x₀) = O.card := by
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hx]
  have hcA : Nat.card {x | x ∈ MulAction.orbit K x₀ ∧ R y₀ x} =
      (O.bipartiteAbove R y₀).card := by
    have hset : {x | x ∈ MulAction.orbit K x₀ ∧ R y₀ x} =
        ((O.bipartiteAbove R y₀ : Finset α) : Set α) := by
      ext x
      simp only [Finset.coe_bipartiteAbove, hOm, Set.mem_ofPred_eq]
    rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  have hcB : Nat.card {y | y ∈ MulAction.orbit K y₀ ∧ R y x₀} =
      (Y.bipartiteBelow R x₀).card := by
    have hset : {y | y ∈ MulAction.orbit K y₀ ∧ R y x₀} =
        ((Y.bipartiteBelow R x₀ : Finset α) : Set α) := by
      ext y
      simp only [Finset.coe_bipartiteBelow, hYm, Set.mem_ofPred_eq]
    rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  rw [hcY, hcO, hcA, hcB]
  exact hmain

end Abstract

/-- The number of actual signed-short axis addresses orthogonal to a given vector. -/
noncomputable def generatedFeasibleAmbientAxisZeroCount (x : GriessSpace) : ℕ :=
  Nat.card {p : GriessShortIndex × ZMod 2 // griessForm (conwayShortAxis p.1 p.2) x = 0}

/-- The actual local orbit of a signed-short axis is the whole signed-short family. -/
theorem generatedFeasibleAmbient_axis_local_orbit (r : GriessShortIndex) (c : ZMod 2) :
    MulAction.orbit H (conwayShortAxis r c) = generatedSignedShortAxes := by
  rw [← generatedAxisLocalOrbit_eq_signed r c]
  rfl

/-- The address count equals the number of actual orthogonal signed-short axes. -/
theorem generatedFeasibleAmbientAxisZeroCount_eq (x : GriessSpace) :
    Nat.card {y | y ∈ generatedSignedShortAxes ∧ griessForm y x = 0} =
      generatedFeasibleAmbientAxisZeroCount x := by
  have hset : {y | y ∈ generatedSignedShortAxes ∧ griessForm y x = 0} =
      (fun p : GriessShortIndex × ZMod 2 => conwayShortAxis p.1 p.2) ''
        {p | griessForm (conwayShortAxis p.1 p.2) x = 0} := by
    ext y
    constructor
    · rintro ⟨⟨p, rfl⟩, hp⟩
      exact ⟨p, hp, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, rfl⟩, hp⟩
  rw [hset, Nat.card_image_of_injective generatedAxis_signed_injective]
  rfl

/-- Every actual local orbit in the Griess space is finite. -/
theorem generatedFeasibleAmbient_local_orbit_finite (x : GriessSpace) :
    (MulAction.orbit H x).Finite := by
  have : Finite H := h_finite
  exact Set.finite_range _

/-- The actual local action preserves orthogonality. -/
theorem generatedFeasibleAmbient_local_orthogonal_iff (h : H) (y x : GriessSpace) :
    griessForm (h • y) (h • x) = 0 ↔ griessForm y x = 0 := by
  change griessForm (rhoLocal h y) (rhoLocal h x) = 0 ↔ _
  rw [rhoLocal_form]

/-- Actual double counting: for every vector `x` and every actual signed-short axis,
`196560 · #{x' ∈ H·x | x' ⟂ axis} = |H·x| · #{signed-short axes ⟂ x}`. -/
theorem generatedFeasibleAmbient_local_double_count (r : GriessShortIndex) (c : ZMod 2)
    (x : GriessSpace) :
    196560 * Nat.card {x' | x' ∈ MulAction.orbit H x ∧
        griessForm (conwayShortAxis r c) x' = 0} =
      Nat.card (MulAction.orbit H x) * generatedFeasibleAmbientAxisZeroCount x := by
  have h := generatedFeasibleAmbient_orbit_double_count (K := H)
    (fun y x => griessForm y x = 0) generatedFeasibleAmbient_local_orthogonal_iff
    (conwayShortAxis r c) x (generatedFeasibleAmbient_local_orbit_finite _)
    (generatedFeasibleAmbient_local_orbit_finite x)
  rw [generatedFeasibleAmbient_axis_local_orbit, generatedSignedShortAxes_card,
    generatedFeasibleAmbientAxisZeroCount_eq] at h
  exact h

/-- The orthogonal axis count is an invariant of the actual local orbit. -/
theorem generatedFeasibleAmbientAxisZeroCount_smul (h : H) (x : GriessSpace) :
    generatedFeasibleAmbientAxisZeroCount (h • x) = generatedFeasibleAmbientAxisZeroCount x := by
  have h₁ := generatedFeasibleAmbient_local_double_count (Sum.inl (0, 0)) 0 (h • x)
  have h₂ := generatedFeasibleAmbient_local_double_count (Sum.inl (0, 0)) 0 x
  rw [MulAction.orbit_smul] at h₁
  have hpos : 0 < Nat.card (MulAction.orbit H x) := by
    have := (generatedFeasibleAmbient_local_orbit_finite x).to_subtype
    exact Nat.card_pos_iff.mpr ⟨⟨⟨x, MulAction.mem_orbit_self x⟩⟩, inferInstance⟩
  exact Nat.eq_of_mul_eq_mul_left hpos (h₁.symm.trans h₂)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
