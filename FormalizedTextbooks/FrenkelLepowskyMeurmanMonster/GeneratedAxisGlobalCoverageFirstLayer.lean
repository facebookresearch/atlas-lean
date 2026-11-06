/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitions

/-! Unconditional first layer of actual global axis coverage. Triality on the
entire first local orbit has precisely the three pair, octad, and odd destinations.
This is a proved layer, not an assertion of twelve-family global coverage. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Three actual representatives encountered after triality on the first local orbit. -/
noncomputable def generatedAxisGlobalFirstLayer : Fin 3 → GriessSpace :=
  ![conwayAxis 0,
    sExtra (conwayShortAxis (Sum.inr (Sum.inl (0, 0))) 0),
    sExtra (conwayShortAxis (Sum.inr (Sum.inr (0, 0))) 0)]

/-- Every actual signed-short triality image belongs to one of these three local families. -/
theorem generatedAxisGlobalFirstLayer_contains_triality (r : GriessShortIndex)
    (c : ZMod 2) :
    sExtra (conwayShortAxis r c) ∈ generatedLocalOrbitUnion generatedAxisGlobalFirstLayer := by
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, i⟩)
  · have hs := generatedAxis_triality_pair_mem_signed p s c
    rw [← generatedAxisLocalOrbit_eq_signed (Sum.inl (0, 0)) 0] at hs
    obtain ⟨h, hh⟩ := hs
    refine ⟨0, h, ?_⟩
    change rhoLocal h (conwayAxis 0) = _
    rw [← conwayShortAxis_pair_zero 0]
    exact hh
  · apply (generatedAxisGlobal_mem_union_iff _ _).mpr
    exact ⟨1, (generatedAxis_triality_octad_class_iff _ _).mpr ⟨o, e, rfl⟩⟩
  · apply (generatedAxisGlobal_mem_union_iff _ _).mpr
    exact ⟨2, (generatedAxis_triality_odd_class_iff _ _).mpr ⟨d, i, rfl⟩⟩

/-- The first global triality step is covered on every actual local element,
without any runtime classification hypothesis. -/
theorem generatedAxisGlobalFirstLayer_covers_first_step (h : H) :
    sExtra (rhoLocal h (conwayAxis 0)) ∈
      generatedLocalOrbitUnion generatedAxisGlobalFirstLayer := by
  have hs : rhoLocal h (conwayAxis 0) ∈ generatedSignedShortAxes := by
    rw [← generatedAxisLocalOrbit_eq_signed (Sum.inl (0, 0)) 0]
    refine ⟨h, ?_⟩
    rw [conwayShortAxis_pair_zero]
  obtain ⟨⟨r, c⟩, hh⟩ := hs
  rw [← hh]
  exact generatedAxisGlobalFirstLayer_contains_triality r c

/-- Every representative of the first layer is genuinely in the generated orbit. -/
theorem generatedAxisGlobalFirstLayer_in_generated_orbit (i : Fin 3) :
    generatedAxisGlobalFirstLayer i ∈ generatedVectorOrbit (conwayAxis 0) := by
  fin_cases i
  · exact ⟨1, rfl⟩
  · obtain ⟨h, hh⟩ := generatedAxis_local_signed_transitive
      (Sum.inl (0, 0)) (Sum.inr (Sum.inl (0, 0))) 0 0
    refine ⟨extraIntoGenerated * localIntoGenerated h, ?_⟩
    change sExtra (rhoLocal h (conwayAxis 0)) = _
    rw [conwayShortAxis_pair_zero] at hh
    rw [hh]
    rfl
  · obtain ⟨h, hh⟩ := generatedAxis_local_signed_transitive
      (Sum.inl (0, 0)) (Sum.inr (Sum.inr (0, 0))) 0 0
    refine ⟨extraIntoGenerated * localIntoGenerated h, ?_⟩
    change sExtra (rhoLocal h (conwayAxis 0)) = _
    rw [conwayShortAxis_pair_zero] at hh
    rw [hh]
    rfl

/-- The entire first layer consists of actual generated axes. -/
theorem generatedAxisGlobalFirstLayer_subset_generated_orbit :
    generatedLocalOrbitUnion generatedAxisGlobalFirstLayer ⊆
      generatedVectorOrbit (conwayAxis 0) := by
  rintro x ⟨i, h, rfl⟩
  obtain ⟨g, hg⟩ := generatedAxisGlobalFirstLayer_in_generated_orbit i
  refine ⟨localIntoGenerated h * g, ?_⟩
  change rhoLocal h (g.val (conwayAxis 0)) = _
  rw [hg]

/-- The three actual local classes in the first transition layer. -/
noncomputable def generatedAxisGlobalFirstLayerClass (i : Fin 3) :
    generatedAxisLocalOrbitSpace :=
  Quotient.mk (MulAction.orbitRel H GriessSpace) (generatedAxisGlobalFirstLayer i)

/-- Each first-layer class is attained by the genuine first transition map. -/
theorem generatedAxisGlobalFirstLayerClass_mem_range (i : Fin 3) :
    generatedAxisGlobalFirstLayerClass i ∈
      Set.range (generatedAxisGlobalDestination (conwayAxis 0)) := by
  fin_cases i
  · refine ⟨Quotient.mk _ (1 : H), ?_⟩
    change Quotient.mk (MulAction.orbitRel H GriessSpace)
      (sExtra (rhoLocal 1 (conwayAxis 0))) = _
    rw [rhoLocal.map_one]
    change Quotient.mk (MulAction.orbitRel H GriessSpace) (sExtra (conwayAxis 0)) = _
    rw [conwayAxis_triality]
    rfl
  · obtain ⟨h, hh⟩ := generatedAxis_local_signed_transitive
      (Sum.inl (0, 0)) (Sum.inr (Sum.inl (0, 0))) 0 0
    rw [conwayShortAxis_pair_zero] at hh
    refine ⟨Quotient.mk _ h, ?_⟩
    change Quotient.mk (MulAction.orbitRel H GriessSpace)
      (sExtra (rhoLocal h (conwayAxis 0))) = _
    rw [hh]
    rfl
  · obtain ⟨h, hh⟩ := generatedAxis_local_signed_transitive
      (Sum.inl (0, 0)) (Sum.inr (Sum.inr (0, 0))) 0 0
    rw [conwayShortAxis_pair_zero] at hh
    refine ⟨Quotient.mk _ h, ?_⟩
    change Quotient.mk (MulAction.orbitRel H GriessSpace)
      (sExtra (rhoLocal h (conwayAxis 0))) = _
    rw [hh]
    rfl

/-- The complete range of actual triality transitions from the first family. -/
theorem generatedAxisGlobalFirstLayer_destination_range :
    Set.range (generatedAxisGlobalDestination (conwayAxis 0)) =
      Set.range generatedAxisGlobalFirstLayerClass := by
  apply Set.Subset.antisymm
  · rintro x ⟨c, rfl⟩
    induction c using Quotient.inductionOn with
    | h h =>
      obtain ⟨i, hi⟩ := (generatedAxisGlobal_mem_union_iff _ _).mp
        (generatedAxisGlobalFirstLayer_covers_first_step h)
      exact ⟨i, hi.symm⟩
  · rintro x ⟨i, rfl⟩
    exact generatedAxisGlobalFirstLayerClass_mem_range i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
