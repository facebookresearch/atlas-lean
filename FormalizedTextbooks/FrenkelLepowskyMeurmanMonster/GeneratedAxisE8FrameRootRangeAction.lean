/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsOrbitFamilies

/-! The actual section group preserves the entire binary root range. Two genuine
frame systems span it, so preservation follows from the action on frame systems. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private def rootSplitLeft (a : Fin 8 → ZMod 2) : Fin 4 → ZMod 2 :=
  ![a 0 + a 1 + a 2 + a 4 + a 6, a 1 + a 2 + a 3,
    a 0 + a 2 + a 3 + a 5 + a 6, a 6 + a 7]

private def rootSplitRight (a : Fin 8 → ZMod 2) : Fin 4 → ZMod 2 :=
  ![a 0 + a 1 + a 3 + a 5 + a 6, a 1 + a 2 + a 3 + a 4,
    a 0 + a 2 + a 3 + a 6, a 7]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check all 256 binary vectors against the two literal candidate bases.
private theorem rootSplit_certificate : ∀ a : Fin 8 → ZMod 2,
    generatedAxisE8FrameSystemCandidateMap 2 (rootSplitLeft a) +
      generatedAxisE8FrameSystemCandidateMap 45 (rootSplitRight a) = a := by
  decide +kernel

/-- Two displayed genuine systems span the full intrinsic binary root space. -/
theorem generatedAxisE8FrameSystemCandidate_two_sup_fortyFive :
    generatedAxisE8FrameSystemCandidate 2 ⊔ generatedAxisE8FrameSystemCandidate 45 = ⊤ := by
  apply top_unique
  intro a _
  rw [← rootSplit_certificate a]
  exact Submodule.add_mem_sup ⟨rootSplitLeft a, rfl⟩ ⟨rootSplitRight a, rfl⟩

/-- Their actual lattice-quotient images span the entire actual root range. -/
theorem generatedAxisE8ActualFrameSystemCandidate_two_sup_fortyFive :
    generatedAxisE8ActualFrameSystemCandidate 2 ⊔
      generatedAxisE8ActualFrameSystemCandidate 45 = generatedAxisE8FrameRootEmbedding.range := by
  rw [generatedAxisE8ActualFrameSystemCandidate, generatedAxisE8ActualFrameSystemCandidate,
    ← Submodule.map_sup, generatedAxisE8FrameSystemCandidate_two_sup_fortyFive,
    Submodule.map_top]

/-- Every element of the full original section group preserves the actual binary root range. -/
theorem generatedAxisE8FrameRootRange_section_action
    (a : generatedAxisE8FrameSystemSectionGroup) :
    generatedAxisE8FrameRootEmbedding.range.map (leechModTwoAction a.val).toLinearMap =
      generatedAxisE8FrameRootEmbedding.range := by
  have hs (k : Fin 270) :
      (generatedAxisE8ActualFrameSystemCandidate k).map
        (leechModTwoAction a.val).toLinearMap ≤ generatedAxisE8FrameRootEmbedding.range := by
    apply generatedAxisE8FrameSystems_le_root_range
    exact generatedAxisE8FrameSystems_orbit_subset _
      (generatedAxisE8ActualFrameSystemCandidate_mem k) ⟨a, rfl⟩
  have hle : generatedAxisE8FrameRootEmbedding.range.map
      (leechModTwoAction a.val).toLinearMap ≤ generatedAxisE8FrameRootEmbedding.range := by
    nth_rw 1 [← generatedAxisE8ActualFrameSystemCandidate_two_sup_fortyFive]
    rw [Submodule.map_sup]
    exact sup_le (hs 2) (hs 45)
  let : Finite LeechModTwo := Finite.of_injective
    leechModTwoLinearEquiv leechModTwoLinearEquiv.injective
  apply SetLike.coe_injective
  apply generatedAxisE8FrameSystems_set_eq_of_subset_card _ _ hle
  exact (Nat.card_congr (Submodule.equivMapOfInjective
    (leechModTwoAction a.val).toLinearMap (leechModTwoAction a.val).injective
    generatedAxisE8FrameRootEmbedding.range).toEquiv).symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
