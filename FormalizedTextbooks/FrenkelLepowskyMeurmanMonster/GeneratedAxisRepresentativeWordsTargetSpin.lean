/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete actual spin signs of the 83 corrected compact source permutation words. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsNodeSpin
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsCocode
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsPlanCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsLeech

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Every corrected target has the recorded full spin operator, including its central sign. -/
theorem representativePermutationSpin_certificate (n : Fin 83) :
    representativeSpinCertificate (representativePermutationFiber n).val.1
      (representativeMatrix (representativePermutationCoordinateRows n))
      (representativeMatrix (representativePermutationPhaseRows n)) := by
  let δ := golayLabelCoefficients (representativePermutationCorrection n)
  let d := localFiberIncl (sourceQCocode δ)
  have hd : representativeSpinCertificate d.val.1
      (representativePermutationStartModel n).coordinate
      (representativePermutationStartModel n).phase :=
    representativeSpinCertificate_cocodeFiber δ
  have h := representativeSpinPlan_certificate
    (fun a => (representativeNodeLetterFiber a).val.1) representativeNodeSpinModel
    (representativePermutationSpinPlan n) d.val.1 (representativePermutationStartModel n) hd
    (fun step _ => representativeNodeSpin_signed_certificate step.1)
    (representativePermutationSpin_plan_certificate n)
  rw [representativePermutationSpin_plan_end,
    representativeSpinPlanEvaluate_eq_product, representativePermutationSpin_plan_letters] at h
  have hw : (representativePermutationFiber n).val.1 = d.val.1 *
      ((representativePermutationWord n).map
        (fun a => (representativeNodeLetterFiber a).val.1)).prod := by
    change representativeFiberSpin
      (d * ((representativePermutationWord n).map representativeNodeLetterFiber).prod) = _
    rw [map_mul, representativeFiberSpin_list_prod, List.map_map]
    rfl
  rw [← hw] at h
  exact h

/-- Both physical and full signed spin actions of each actual target word are certified.
The numerical source labels in the data do not assert axis-orbit membership. -/
theorem representativePermutation_full_certificate (n : Fin 83) :
    (∀ (f : SpinSpace) (t : SpinIndex),
      (representativePermutationFiber n).val.1.val f t =
        qSign (monsterMonomialQuadratic
          (representativeMatrix (representativePermutationPhaseRows n)) t) *
          f (representativeMatrix (representativePermutationCoordinateRows n) *ᵥ t)) ∧
    (∀ (f : Fin 24 → ℝ) (i : Fin 24),
      (representativePermutationFiber n).val.2.val f i =
        f (representativePermutationPhysicalImages n i)) :=
  ⟨representativePermutationSpin_certificate n, representativePermutationLeech_apply n⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
