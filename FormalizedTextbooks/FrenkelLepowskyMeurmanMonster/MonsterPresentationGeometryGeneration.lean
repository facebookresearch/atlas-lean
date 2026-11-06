/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual surjectivity of the universal geometry representation; its kernel remains open. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationGeometryPresentation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalCompletion

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The actual conjugates of the central involution generate G by the proved normal-generation
argument and the proved full-centralizer identification. -/
theorem monsterGeometryPoints_generate :
    Subgroup.closure (conjugatesOf generatedCentralInvolution) = ⊤ := by
  have hs : Group.conjugatesOfSet ({generatedCentralInvolution} : Set G) =
      conjugatesOf generatedCentralInvolution := by
    ext g
    simp only [Group.mem_conjugatesOfSet_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨a, rfl, h⟩
      exact h
    · intro h
      exact ⟨generatedCentralInvolution, rfl, h⟩
  have hn : Subgroup.normalClosure ({generatedCentralInvolution} : Set G) ≠ ⊥ := by
    intro h
    have hz := Subgroup.subset_normalClosure
      (show generatedCentralInvolution ∈ ({generatedCentralInvolution} : Set G) from rfl)
    rw [h] at hz
    have hz' : generatedCentralInvolution = 1 := by simpa using hz
    apply qCentralInvolution_ne_one
    apply qIntoGenerated_injective
    exact hz'.trans qIntoGenerated.map_one.symm
  have ht := generated_normal_eq_top_of_centralizer_le_local
    generatedCentralizer_eq_local_range.le
    (Subgroup.normalClosure ({generatedCentralInvolution} : Set G)) hn
  simpa only [Subgroup.normalClosure, hs] using ht

/-- Every actual source point lies in the canonical image of the geometry presentation. -/
theorem monsterGeometryPoint_mem_image (p : MonsterGeometryPoint) :
    p.val ∈ monsterGeometryIntoGenerated.range :=
  ⟨PresentedGroup.of p, monsterGeometryIntoGenerated_generator p⟩

/-- The source geometry maps onto the actual G. Injectivity is the remaining IPS recognition
problem and is not assumed by this theorem. -/
theorem monsterGeometryIntoGenerated_surjective :
    Function.Surjective monsterGeometryIntoGenerated := by
  have hl : Subgroup.closure (conjugatesOf generatedCentralInvolution) ≤
      monsterGeometryIntoGenerated.range := by
    apply (Subgroup.closure_le _).mpr
    intro p hp
    exact monsterGeometryPoint_mem_image ⟨p, hp⟩
  rw [monsterGeometryPoints_generate] at hl
  intro g
  exact hl (Subgroup.mem_top g)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
