/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7PairCompanionOrbit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7CompanionTransportData

/-! The actual Tenth octad, normal pair, and companion permutation group has order720. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The entire actual octad group acts on every original Golay code label. -/
instance generatedTenthE7OctadCodeAction :
    MulAction generatedTenthE7OctadPermutationGroup (Fin 4096) :=
  MulAction.compHom (Fin 4096)
    (golayLabelActionHom.comp generatedTenthE7OctadPermutationGroup.subtype)

/-- The original first pair together with its actual source2306 companion. -/
def generatedTenthE7BasePermutationFlag : generatedTenthE7OctadPairs × Fin 4096 :=
  (generatedTenthE7OctadFirstPair, 2306)

/-- The actual standard normal pair4/5 together with its full standard companion110. -/
def generatedTenthE7StandardPermutationFlag : generatedTenthE7OctadPairs × Fin 4096 :=
  (generatedTenthE7OctadPairDataElement 22, 110)

/-- The entire actual standard permutation flag stabilizer in the whole octad group. -/
abbrev generatedTenthE7StandardFlagPermutationGroup :=
  MulAction.stabilizer generatedTenthE7OctadPermutationGroup generatedTenthE7StandardPermutationFlag

/-- Stabilizing the actual pair and then its companion is exactly the full two-object stabilizer. -/
def generatedTenthE7BaseFlagPermutationEquiv :
    MulAction.stabilizer generatedTenthE7PairPermutationGroup (2306 : Fin 4096) ≃*
      MulAction.stabilizer generatedTenthE7OctadPermutationGroup
        generatedTenthE7BasePermutationFlag where
  toFun g := ⟨g.val.val, by
    apply Prod.ext
    · exact g.val.property
    · exact g.property⟩
  invFun g := ⟨⟨g.val, congrArg Prod.fst g.property⟩, congrArg Prod.snd g.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The full original two-object permutation stabilizer has actual order720. -/
theorem generatedTenth_e7_base_flag_permutation_card :
    Nat.card (MulAction.stabilizer generatedTenthE7OctadPermutationGroup
      generatedTenthE7BasePermutationFlag) = 720 := by
  rw [← Nat.card_congr generatedTenthE7BaseFlagPermutationEquiv.toEquiv]
  exact generatedTenth_e7_pair_companion_stabilizer_card

/-- A genuine original octad automorphism transports the entire original flag
onto the entire actual standard Tenth flag. -/
theorem generatedTenth_e7_standard_flag_permutation_transport :
    ∃ a : generatedTenthE7OctadPermutationGroup,
      a • generatedTenthE7BasePermutationFlag = generatedTenthE7StandardPermutationFlag := by
  obtain ⟨p, hp⟩ := generatedTenth_e7_companion_pointwise_reaches 2343
    generatedTenth_e7_companion_transport_source
  refine ⟨generatedTenthE7OctadPairWordElement 22 * generatedTenthE7PointwiseOctadElement p, ?_⟩
  apply Prod.ext
  · change (generatedTenthE7OctadPairWordElement 22 * generatedTenthE7PointwiseOctadElement p) •
      generatedTenthE7OctadFirstPair = generatedTenthE7OctadPairDataElement 22
    have hfix : generatedTenthE7PointwiseOctadElement p • generatedTenthE7OctadFirstPair =
        generatedTenthE7OctadFirstPair := generatedTenth_e7_pointwise_pair_mem p
    rw [mul_smul, hfix, generatedTenth_e7_octad_pair_word_image]
  · change golayLabelPermutation
      (generatedTenthE7OctadPairWord 22 * p.val) 2306 = 110
    change golayLabelActionHom (generatedTenthE7OctadPairWord 22 * p.val) 2306 = 110
    rw [map_mul]
    change golayLabelPermutation (generatedTenthE7OctadPairWord 22)
      (golayLabelPermutation p.val 2306) = 110
    rw [hp, generatedTenth_e7_companion_pair_word_label]

/-- The whole actual standard flag permutation stabilizer has order720,
via a genuine transport of the complete original stabilizer. -/
theorem generatedTenth_e7_standard_flag_permutation_card :
    Nat.card generatedTenthE7StandardFlagPermutationGroup = 720 := by
  obtain ⟨a, ha⟩ := generatedTenth_e7_standard_flag_permutation_transport
  rw [← Nat.card_congr (MulAction.stabilizerEquivStabilizer ha.symm).toEquiv]
  exact generatedTenth_e7_base_flag_permutation_card

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
