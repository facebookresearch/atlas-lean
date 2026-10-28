/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthStabilizerProjection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthFrameIntersectionLocal
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthFrameSystemGeneration
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthFrameSystemCo1Order
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiFixed
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderExact

/-! The actual axis projection lies in the actual section/system stabilizer. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A genuine full-axis lift supplies its actual spatial projection to the axis image. -/
theorem generatedFifthProjectedAxisStabilizer_mem_of_lift (f : localFiberSubgroup)
    (hf : rhoLocal (localFiberIntoH f) generatedFifthAxis = generatedFifthAxis) :
    QuotientGroup.mk' signsSubgroup f.val.2 ∈ generatedFifthProjectedAxisStabilizer := by
  refine ⟨⟨localFiberIntoH f, hf⟩, ?_⟩
  rfl

/-- Every actual axis stabilizer projection preserves the genuine section and entire system. -/
theorem generatedFifthProjectedAxisStabilizer_le_system :
    generatedFifthProjectedAxisStabilizer ≤ generatedFifthFrameSystemCo1Stabilizer := by
  rintro c ⟨h, rfl⟩
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h.val
  change localFiberIntoH f = h.val at hf
  have hfix : rhoLocal (localFiberIntoH f) generatedFifthAxis = generatedFifthAxis := by
    rw [hf]
    exact h.property
  have hmem : f.val.2 ∈ generatedFifthFrameSystemStabilizer := by
    rw [generatedFifthFrameSystemStabilizer, generatedAxisE8FrameSystemStabilizer_mem]
    refine ⟨(generatedFifth_matrix_stabilizer_iff _).mp ?_,
      generatedFifthFrameSystem_local_preserved f hfix⟩
    have he := congrArg (fun x : GriessSpace => (griessConwayEncode x).1) hfix
    rw [generatedFourth_local_matrix] at he
    exact he
  refine ⟨f.val.2, hmem, ?_⟩
  change QuotientGroup.mk' signsSubgroup f.val.2 = projH h.val
  rw [← hf]
  rfl

/-- The entire corrected Xi gives an unconditional original spatial generator in the axis image. -/
theorem generatedFifthProjectedAxisStabilizer_xi_mem :
    QuotientGroup.mk' signsSubgroup co1XiIsometry ∈
      generatedFifthProjectedAxisStabilizer := by
  exact generatedFifthProjectedAxisStabilizer_mem_of_lift
    generatedFifthXiCorrectedFiber generatedFifth_xi_full_fixed

/-- Original sign and permutation lifts suffice to identify the whole actual projection image. -/
theorem generatedFifthProjectedAxisStabilizer_eq_system_of_generators
    (hs : ∀ k : Fin 12, QuotientGroup.mk' signsSubgroup (monsterCo1GeometrySignIsometry k) ∈
      generatedFifthProjectedAxisStabilizer)
    (hm : ∀ k : Fin 6, QuotientGroup.mk' signsSubgroup
      (golayPermutationIsometry (generatedFifthMonomialSpatialPermutation k)) ∈
        generatedFifthProjectedAxisStabilizer) :
    generatedFifthProjectedAxisStabilizer = generatedFifthFrameSystemCo1Stabilizer := by
  apply le_antisymm generatedFifthProjectedAxisStabilizer_le_system
  rintro c ⟨g, hg, rfl⟩
  have h := generatedFifthFrameSystemStabilizer_le_of_generators
    (generatedFifthProjectedAxisStabilizer.comap (QuotientGroup.mk' signsSubgroup))
    hs hm generatedFifthProjectedAxisStabilizer_xi_mem
  exact h hg

/-- Once those genuine generators lift, the full original H stabilizer has its forced order. -/
theorem generatedFifth_local_stabilizer_card_of_system
    (he : generatedFifthProjectedAxisStabilizer = generatedFifthFrameSystemCo1Stabilizer) :
    Nat.card generatedFifthLocalAxisStabilizer = 21139292160 := by
  rw [generatedFifth_local_stabilizer_card_range, he,
    generatedFifthFrameSystem_co1_stabilizer_card]

/-- Identifying the actual system image forces the exact genuine fifth H orbit cardinality. -/
theorem generatedFifth_local_axis_orbit_card_of_system
    (he : generatedFifthProjectedAxisStabilizer = generatedFifthFrameSystemCo1Stabilizer) :
    Nat.card (MulAction.orbit H generatedFifthAxis) = 6599645724672000 := by
  have h := generatedFifthLocalAxisStabilizer.card_mul_index
  rw [generatedFifth_local_stabilizer_card_of_system he, local_h_card_exact] at h
  have hi : generatedFifthLocalAxisStabilizer.index = 6599645724672000 := by omega
  rw [generatedFifthLocalAxisStabilizer, MulAction.index_stabilizer,
    ← Nat.card_coe_set_eq] at hi
  exact hi

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
