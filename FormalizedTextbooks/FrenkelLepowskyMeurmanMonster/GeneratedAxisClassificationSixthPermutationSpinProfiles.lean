/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPermutationSpinInverse

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPermutationSpinEdges00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPermutationSpinEdges01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPermutationSpinEdges02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPermutationSpinEdges03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPermutationSpinEdges04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPermutationSpinEdges05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPermutationSpinEdges06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPermutationSpinEdges07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPermutationSpinEdges08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPermutationSpinEdges09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPermutationSpinEdges10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPermutationSpinEdges11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPermutationSpinEdges12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPermutationSpinEdges13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPermutationSpinEdges14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPermutationSpinEdges15
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPermutationSpinEdges16
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPermutationSpinEdges17
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPermutationSpinEdges18

/-! Complete actual signed spin profiles of the B, C, and swap source words. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

set_option maxHeartbeats 2000000 in
-- Assemble fifty-seven opaque checked edges into the three original signed plans.
/-- Every bounded original word plan passes the full signed coordinate checker. -/
theorem generatedSixth_permutation_profile_certificate (k : Fin 3) :
    representativeSpinPlanValid generatedSixthPermutationSpinLetterModel
      representativeSpinIdentityModel (generatedSixthPermutationSpinPlans k) := by
  fin_cases k
  · exact ⟨generatedSixth_permutation_edge_0_00,
      ⟨generatedSixth_permutation_edge_0_01,
      ⟨generatedSixth_permutation_edge_0_02,
      ⟨generatedSixth_permutation_edge_0_03,
      ⟨generatedSixth_permutation_edge_0_04,
      ⟨generatedSixth_permutation_edge_0_05,
      ⟨generatedSixth_permutation_edge_0_06,
      ⟨generatedSixth_permutation_edge_0_07,
      ⟨generatedSixth_permutation_edge_0_08,
      ⟨generatedSixth_permutation_edge_0_09,
      ⟨generatedSixth_permutation_edge_0_10,
      ⟨generatedSixth_permutation_edge_0_11,
      ⟨generatedSixth_permutation_edge_0_12,
      ⟨generatedSixth_permutation_edge_0_13,
      ⟨generatedSixth_permutation_edge_0_14, True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  · exact ⟨generatedSixth_permutation_edge_1_00,
      ⟨generatedSixth_permutation_edge_1_01,
      ⟨generatedSixth_permutation_edge_1_02,
      ⟨generatedSixth_permutation_edge_1_03,
      ⟨generatedSixth_permutation_edge_1_04,
      ⟨generatedSixth_permutation_edge_1_05,
      ⟨generatedSixth_permutation_edge_1_06,
      ⟨generatedSixth_permutation_edge_1_07,
      ⟨generatedSixth_permutation_edge_1_08,
      ⟨generatedSixth_permutation_edge_1_09,
      ⟨generatedSixth_permutation_edge_1_10,
      ⟨generatedSixth_permutation_edge_1_11,
      ⟨generatedSixth_permutation_edge_1_12, True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  · exact ⟨generatedSixth_permutation_edge_2_00,
      ⟨generatedSixth_permutation_edge_2_01,
      ⟨generatedSixth_permutation_edge_2_02,
      ⟨generatedSixth_permutation_edge_2_03,
      ⟨generatedSixth_permutation_edge_2_04,
      ⟨generatedSixth_permutation_edge_2_05,
      ⟨generatedSixth_permutation_edge_2_06,
      ⟨generatedSixth_permutation_edge_2_07,
      ⟨generatedSixth_permutation_edge_2_08,
      ⟨generatedSixth_permutation_edge_2_09,
      ⟨generatedSixth_permutation_edge_2_10,
      ⟨generatedSixth_permutation_edge_2_11,
      ⟨generatedSixth_permutation_edge_2_12,
      ⟨generatedSixth_permutation_edge_2_13,
      ⟨generatedSixth_permutation_edge_2_14,
      ⟨generatedSixth_permutation_edge_2_15,
      ⟨generatedSixth_permutation_edge_2_16,
      ⟨generatedSixth_permutation_edge_2_17,
      ⟨generatedSixth_permutation_edge_2_18,
      ⟨generatedSixth_permutation_edge_2_19,
      ⟨generatedSixth_permutation_edge_2_20,
      ⟨generatedSixth_permutation_edge_2_21,
      ⟨generatedSixth_permutation_edge_2_22,
      ⟨generatedSixth_permutation_edge_2_23,
      ⟨generatedSixth_permutation_edge_2_24,
      ⟨generatedSixth_permutation_edge_2_25,
      ⟨generatedSixth_permutation_edge_2_26,
      ⟨generatedSixth_permutation_edge_2_27,
      ⟨generatedSixth_permutation_edge_2_28, True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

private theorem word_spin (w : List (Fin 4)) :
    (leechRootedA2GeneratingWordFiber w).val.1 =
      (w.map (fun t => (leechRootedA2GeneratingLetterFiber t).val.1)).prod := by
  change representativeFiberSpin ((w.map leechRootedA2GeneratingLetterFiber).prod) = _
  rw [map_list_prod, List.map_map]
  rfl

/-- The checked word profile is the entire genuine original signed spin operator. -/
theorem generatedSixth_permutation_profile_spin (k : Fin 3) :
    representativeSpinCertificate
      (leechRootedA2GeneratingWordFiber (generatedSixthPermutationProfileWords k)).val.1
      (generatedSixthPermutationProfileModel k).coordinate
      (generatedSixthPermutationProfileModel k).phase := by
  have h := representativeSpinPlan_certificate
    (fun t => (leechRootedA2GeneratingLetterFiber t).val.1)
    generatedSixthPermutationSpinLetterModel (generatedSixthPermutationSpinPlans k)
    1 representativeSpinIdentityModel representativeSpinCertificate_one
    (fun step _ => generatedSixth_permutation_spin_letter step.1)
    (generatedSixth_permutation_profile_certificate k)
  rw [generatedSixth_permutation_profile_end,
    representativeSpinPlanEvaluate_eq_product, one_mul,
    generatedSixth_permutation_profile_letters, ← word_spin] at h
  exact h

/-- The complete signed inverse word profile is also the genuine full spin operator. -/
theorem generatedSixth_permutation_profile_inverse_spin (k : Fin 3) :
    representativeSpinCertificate
      ((leechRootedA2GeneratingWordFiber (generatedSixthPermutationProfileWords k)).val.1)⁻¹
      (generatedSixthPermutationProfileInverseModel k).coordinate
      (generatedSixthPermutationProfileInverseModel k).phase := by
  have h := representativeSpinCertificate_inv _ _ _ _
    (generatedSixth_permutation_profile_spin k)
    (generatedSixth_permutation_profile_inverse_matrix k)
  exact representativeSpinCertificate_replace _ _ _ _ h
    (generatedSixth_permutation_profile_inverse_phase k).1
    (generatedSixth_permutation_profile_inverse_phase k).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
