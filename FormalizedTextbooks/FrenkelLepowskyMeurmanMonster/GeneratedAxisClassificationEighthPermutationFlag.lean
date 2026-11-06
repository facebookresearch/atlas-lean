/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayDodecadFlagTransitivity
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthFlagData

/-! Exact original Golay permutation stabilizer of the eighth dodecad and outside point. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual eighth encoder label has the actual distinguished coordinate outside its support. -/
theorem generatedEighth_dodecad_outside_label :
    (2292 : Fin 4096) ∈ golayDodecadsOutside 20 := by
  simp only [golayDodecadsOutside, golayDodecads, Finset.mem_filter,
    Finset.mem_univ, true_and]
  change golayMaskWeight (golayEncodedMask 2292) = 12 ∧
    (!(golayEncodedMask 2292).testBit 20) = true
  rw [generatedEighth_dodecad_mask]
  decide +kernel

/-- Genuine coordinate permutations preserving the actual dodecad and actual outside point. -/
def generatedEighthPermutationFlagStabilizer : Subgroup golayAutomorphismSubgroup :=
  MulAction.stabilizer golayAutomorphismSubgroup ((2292 : Fin 4096), (20 : Fin 24))

/-- Membership means fixing physical coordinate20 and the original twelve-coordinate codeword. -/
theorem generatedEighthPermutationFlagStabilizer_mem (p : golayAutomorphismSubgroup) :
    p ∈ generatedEighthPermutationFlagStabilizer ↔ p.val 20 = 20 ∧
      golayPermute p.val generatedEighthDodecadWord.val = generatedEighthDodecadWord.val := by
  rw [generatedEighthPermutationFlagStabilizer, MulAction.mem_stabilizer_iff]
  constructor
  · intro hp
    refine ⟨congrArg Prod.snd hp, ?_⟩
    have hl : p • (2292 : Fin 4096) = 2292 := congrArg Prod.fst hp
    have hw := golayLabelPermutation_word p 2292
    rw [← golayLabelAction_smul, hl] at hw
    exact hw.symm
  · rintro ⟨hp, hw⟩
    apply Prod.ext
    · change p • (2292 : Fin 4096) = 2292
      apply golayLabelCoefficients_injective
      apply golayEncoder_injective
      change golayEncoder (golayLabelCoefficients (golayLabelPermutation p 2292)) = _
      rw [golayLabelPermutation_word]
      exact hw
    · exact hp

/-- The actual eighth dodecad/outside-point permutation stabilizer has order7920. -/
theorem generatedEighthPermutationFlagStabilizer_card :
    Nat.card generatedEighthPermutationFlagStabilizer = 7920 :=
  golayDodecadFlag_stabilizer_card 2292 20 generatedEighth_dodecad_outside_label

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
