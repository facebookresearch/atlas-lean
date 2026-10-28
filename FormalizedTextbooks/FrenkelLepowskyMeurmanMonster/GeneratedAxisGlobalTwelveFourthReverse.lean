/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveRootPairs

/-! Reverse bindings for the Fourth forest roots.

Let `k` be any actual local element whose binary root is carried to by an actual Fourth-axis
stabilizer element from the binary root of a forest root word `r`. Then the two triality images at
`k` are local images of the two triality images at `r`, as a pair, with equal or exchanged signs.
Consequently a single proved local class membership of one triality image at `k` (for example from
reversing an explicit transport `τ^(±1) (w vⱼ) = k v₄` of another family) binds:
* the forward image at a phase-merged root, and
* at any root, the pair of images up to exchange. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- One membership at `k` gives one of the two memberships at a related forest root. -/
theorem generatedAxisGlobalTwelveFourth_reverse_pair {ι : Type*} (u : ι → GriessSpace)
    (i : Fin 16) (k c : H) (hc : c ∈ generatedFourthLocalAxisStabilizer)
    (hroot : generatedAxisGlobalBinaryAct c (generatedAxisGlobalTwelveFourthRoot i) =
      generatedAxisGlobalBinaryRoot k)
    (hk : sExtra (rhoLocal k generatedFourthAxis) ∈ generatedLocalOrbitUnion u ∨
      sExtra⁻¹ (rhoLocal k generatedFourthAxis) ∈ generatedLocalOrbitUnion u) :
    sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal i) generatedFourthAxis) ∈
        generatedLocalOrbitUnion u ∨
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal i) generatedFourthAxis) ∈
        generatedLocalOrbitUnion u := by
  have hfix : rhoLocal c generatedFourthAxis = generatedFourthAxis := hc
  rcases generatedAxisGlobalTwelve_root_relation_pair generatedFourthAxis k
      (generatedAxisGlobalTwelveFourthRootLocal i) c hfix hroot with
    ⟨⟨k1, h1⟩, ⟨k2, h2⟩⟩ | ⟨⟨k1, h1⟩, ⟨k2, h2⟩⟩
  · rcases hk with hk | hk
    · exact Or.inl (generatedAxisGlobalTwelve_union_mem_of_local u k1 hk h1)
    · exact Or.inr (generatedAxisGlobalTwelve_union_mem_of_local u k2 hk h2)
  · rcases hk with hk | hk
    · exact Or.inr (generatedAxisGlobalTwelve_union_mem_of_local u k1 hk h1)
    · exact Or.inl (generatedAxisGlobalTwelve_union_mem_of_local u k2 hk h2)

/-- At a phase-merged root, one membership at a related `k` binds the forward image. -/
theorem generatedAxisGlobalTwelveFourth_reverse_merged {ι : Type*} (u : ι → GriessSpace)
    (j : Fin 11) (k c : H) (hc : c ∈ generatedFourthLocalAxisStabilizer)
    (hroot : generatedAxisGlobalBinaryAct c
      (generatedAxisGlobalTwelveFourthRoot (generatedAxisGlobalTwelveFourthMergedRoot j)) =
        generatedAxisGlobalBinaryRoot k)
    (hk : sExtra (rhoLocal k generatedFourthAxis) ∈ generatedLocalOrbitUnion u ∨
      sExtra⁻¹ (rhoLocal k generatedFourthAxis) ∈ generatedLocalOrbitUnion u) :
    sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal
      (generatedAxisGlobalTwelveFourthMergedRoot j)) generatedFourthAxis) ∈
        generatedLocalOrbitUnion u := by
  rcases generatedAxisGlobalTwelveFourth_reverse_pair u _ k c hc hroot hk with h | h
  · exact h
  · obtain ⟨k0, hk0⟩ := generatedAxisGlobalTwelveFourthMerged_orbit j
    rw [hk0]
    exact generatedLocalOrbitUnion_local u k0 h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
