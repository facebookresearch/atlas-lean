/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftCorrectedTensor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftCertificate0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftCertificate1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftCertificate2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftCertificate3

/-! The genuine extraspecial-corrected normalized flag lift fixes the entire actual tensor. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The four bounded blocks exhaust every original signed affine tensor support point. -/
theorem generatedFourth_lift_tensor_certificate :
    ∀ k : Fin 28, ∀ s : Fin 4,
      generatedFourthLiftSparseCorrectedFast (generatedFourthLiftSupportAddress k s)
        (generatedFourthQAffineTensorColumns k) =
          64 * generatedFourthLiftIntegerTensor (generatedFourthLiftSupportAddress k s)
            (generatedFourthQAffineTensorColumns k) := by
  intro k s
  by_cases h0 : k.val < 7
  · simpa only [Nat.zero_add] using generatedFourth_lift_tensor_certificate_0 ⟨k.val, h0⟩ s
  by_cases h1 : k.val < 14
  · have hh : 7 ≤ k.val := by omega
    simpa only [Nat.add_sub_of_le hh] using
      generatedFourth_lift_tensor_certificate_1 ⟨k.val - 7, by omega⟩ s
  by_cases h2 : k.val < 21
  · have hh : 14 ≤ k.val := by omega
    simpa only [Nat.add_sub_of_le hh] using
      generatedFourth_lift_tensor_certificate_2 ⟨k.val - 14, by omega⟩ s
  · have hh : 21 ≤ k.val := by omega
    simpa only [Nat.add_sub_of_le hh] using
      generatedFourth_lift_tensor_certificate_3 ⟨k.val - 21, by omega⟩ s

/-- The genuine Q-corrected local flag lift fixes the entire actual tensor. -/
theorem generatedFourth_flag_corrected_lift_tensor_fixed :
    localTensorRepresentation generatedFourthFlagCorrectedLift
      (griessConwayEncode generatedFourthAxis).2.2 =
        (griessConwayEncode generatedFourthAxis).2.2 :=
  generatedFourth_lift_tensor_fixed_of_certificate generatedFourth_lift_tensor_certificate

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
