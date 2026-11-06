/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthMonomialSystemOrbitAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsMaskRecognition

/-! The actual selected-octad permutation orbit and stabilizer of the fifth frame system. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Pointwise
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Original selected-generator words reaching the fifteen displayed actual systems. -/
def generatedFifthMonomialSystemWord : Fin 15 → List (Fin 5) :=
  ![[], [0], [3], [4], [1, 0], [2, 0], [4, 0], [0, 3], [2, 3], [4, 3], [1, 4],
    [0, 1, 0], [0, 2, 0], [3, 2, 0], [0, 2, 3]]

/-- Each word acts on the genuine initial system as its displayed actual system. -/
theorem generatedFifthMonomialSystem_word_action (i : Fin 15) :
    ((generatedFifthMonomialSystemWord i).map generatedFifthSelectedOctadPermutation).prod •
        generatedFifthMonomialSystem 0 = generatedFifthMonomialSystem i := by
  fin_cases i <;> simp [generatedFifthMonomialSystemWord, mul_smul,
    generatedFifthMonomialSystem_action, generatedFifthMonomialSystemTransition]

/-- Every word representative belongs to the full original selected-octad group. -/
theorem generatedFifthMonomialSystem_word_mem (i : Fin 15) :
    ((generatedFifthMonomialSystemWord i).map generatedFifthSelectedOctadPermutation).prod ∈
      generatedFifthSelectedOctadSubgroup := by
  apply Subgroup.list_prod_mem
  intro p hp
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hp
  exact generatedFifthSelectedOctad_generator_mem k

/-- The displayed systems are genuinely distinct lattice-quotient subspaces. -/
theorem generatedFifthMonomialSystem_injective :
    Function.Injective generatedFifthMonomialSystem := by
  intro i j h
  apply generatedFifthMonomialSystemIndex_injective
  apply generatedAxisE8FrameSystemCandidate_injective
  exact Submodule.map_injective_of_injective generatedAxisE8FrameRootEmbedding_injective h

/-- Every original selected generator preserves the whole displayed set of systems. -/
theorem generatedFifthMonomialSystem_set_preserved (k : Fin 5) :
    generatedFifthSelectedOctadPermutation k • Set.range generatedFifthMonomialSystem =
      Set.range generatedFifthMonomialSystem := by
  ext W
  constructor
  · rintro ⟨V, ⟨i, rfl⟩, rfl⟩
    exact ⟨generatedFifthMonomialSystemTransition k i,
      (generatedFifthMonomialSystem_action k i).symm⟩
  · rintro ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := (generatedFifthMonomialSystemTransition_bijective k).surjective i
    exact ⟨generatedFifthMonomialSystem j, ⟨j, rfl⟩,
      (generatedFifthMonomialSystem_action k j).trans (congrArg generatedFifthMonomialSystem hj)⟩

/-- The full actual selected-octad group preserves the displayed finite orbit. -/
theorem generatedFifthMonomialSystem_full_set_preserved (p : generatedFifthSelectedOctadSubgroup) :
    p.val • Set.range generatedFifthMonomialSystem = Set.range generatedFifthMonomialSystem := by
  have h := generatedFifthSelectedOctad_le_of_generators
    (MulAction.stabilizer golayAutomorphismSubgroup (Set.range generatedFifthMonomialSystem))
    generatedFifthMonomialSystem_set_preserved
  exact h p.property

/-- The full actual selected-octad group has exactly the fifteen displayed system images. -/
theorem generatedFifthMonomialSystem_orbit :
    MulAction.orbit generatedFifthSelectedOctadSubgroup generatedFifthFrameSystem =
      Set.range generatedFifthMonomialSystem := by
  ext W
  constructor
  · rintro ⟨p, rfl⟩
    have h : p.val • generatedFifthMonomialSystem 0 ∈
        p.val • Set.range generatedFifthMonomialSystem :=
      ⟨generatedFifthMonomialSystem 0, ⟨0, rfl⟩, rfl⟩
    rw [generatedFifthMonomialSystem_full_set_preserved,
      generatedFifthMonomialSystem_zero] at h
    exact h
  · rintro ⟨i, rfl⟩
    refine ⟨⟨_, generatedFifthMonomialSystem_word_mem i⟩, ?_⟩
    change _ • generatedFifthFrameSystem = generatedFifthMonomialSystem i
    rw [← generatedFifthMonomialSystem_zero]
    exact generatedFifthMonomialSystem_word_action i

/-- The genuine monomial system orbit has fifteen elements. -/
theorem generatedFifthMonomialSystem_orbit_card :
    Nat.card (MulAction.orbit generatedFifthSelectedOctadSubgroup generatedFifthFrameSystem) =
      15 := by
  rw [generatedFifthMonomialSystem_orbit,
    ← Nat.card_congr (Equiv.ofInjective generatedFifthMonomialSystem
      generatedFifthMonomialSystem_injective)]
  norm_num

/-- The full actual octad-permutation stabilizer of the fifth system has order21504. -/
theorem generatedFifthMonomialSystem_stabilizer_card :
    Nat.card (MulAction.stabilizer generatedFifthSelectedOctadSubgroup
      generatedFifthFrameSystem) = 21504 := by
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup
    generatedFifthSelectedOctadSubgroup generatedFifthFrameSystem)
  rw [Nat.card_prod, generatedFifthMonomialSystem_orbit_card, generatedFifthSelectedOctad_card] at h
  omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
