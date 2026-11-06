/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPermutationSpinProfiles

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialSpinEdges0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialSpinEdges1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialSpinEdges2

/-! Complete actual signed spin action of the four original monomial raw generators. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every first product passes the original full coordinate and quadratic sign check. -/
theorem generatedSixth_monomial_spin_prefix_edge (j : Fin 3) :
    representativeSpinEdge (generatedSixthPermutationProfileModel 0)
      (generatedSixthMonomialSpinSource j) (generatedSixthMonomialSpinPrefix j) := by
  fin_cases j
  · exact generatedSixth_monomial_spin_prefix_0
  · exact generatedSixth_monomial_spin_prefix_1
  · exact generatedSixth_monomial_spin_prefix_2

/-- Every second product passes the complete signed inverse-conjugation check. -/
theorem generatedSixth_monomial_spin_conjugate_edge (j : Fin 3) :
    representativeSpinEdge (generatedSixthMonomialSpinPrefix j)
      (generatedSixthPermutationProfileInverseModel 0)
      (generatedSixthMonomialSpinModel (Fin.castAdd 1 j)) := by
  fin_cases j
  · exact generatedSixth_monomial_spin_conjugate_0
  · exact generatedSixth_monomial_spin_conjugate_1
  · exact generatedSixth_monomial_spin_conjugate_2

/-- The three recorded raw fibers are exactly the genuine full transporter conjugates. -/
theorem generatedSixth_monomial_raw_conjugate (j : Fin 3) :
    generatedSixthRawGenerator (Fin.castAdd 2 j) =
      generatedSixthPermutationTransportFiber *
        representativePermutationFiber (generatedSixthMonomialSpinTargets j) *
          generatedSixthPermutationTransportFiber⁻¹ := by
  fin_cases j <;> rfl

/-- The three full conjugates act by their checked signed spin models. -/
theorem generatedSixth_monomial_conjugate_spin (j : Fin 3) :
    representativeSpinCertificate
      (generatedSixthRawGenerator (Fin.castAdd 2 j)).val.1
      (generatedSixthMonomialSpinModel (Fin.castAdd 1 j)).coordinate
      (generatedSixthMonomialSpinModel (Fin.castAdd 1 j)).phase := by
  let B := generatedSixthPermutationTransportFiber
  let p := representativePermutationFiber (generatedSixthMonomialSpinTargets j)
  have hB := generatedSixth_permutation_profile_spin 0
  change representativeSpinCertificate B.val.1
    (generatedSixthPermutationProfileModel 0).coordinate
    (generatedSixthPermutationProfileModel 0).phase at hB
  have hBi := generatedSixth_permutation_profile_inverse_spin 0
  change representativeSpinCertificate B.val.1⁻¹
    (generatedSixthPermutationProfileInverseModel 0).coordinate
    (generatedSixthPermutationProfileInverseModel 0).phase at hBi
  have hp : representativeSpinCertificate p.val.1
      (generatedSixthMonomialSpinSource j).coordinate
      (generatedSixthMonomialSpinSource j).phase :=
    representativePermutationSpin_certificate (generatedSixthMonomialSpinTargets j)
  have h1 := representativeSpinEdge_certificate B.val.1 p.val.1
    (generatedSixthPermutationProfileModel 0) (generatedSixthMonomialSpinSource j)
    (generatedSixthMonomialSpinPrefix j) hB hp (generatedSixth_monomial_spin_prefix_edge j)
  have h2 := representativeSpinEdge_certificate (B.val.1 * p.val.1) B.val.1⁻¹
    (generatedSixthMonomialSpinPrefix j) (generatedSixthPermutationProfileInverseModel 0)
    (generatedSixthMonomialSpinModel (Fin.castAdd 1 j)) h1 hBi
    (generatedSixth_monomial_spin_conjugate_edge j)
  rw [generatedSixth_monomial_raw_conjugate]
  change representativeSpinCertificate (representativeFiberSpin (B * p * B⁻¹)) _ _
  rw [map_mul, map_mul, map_inv]
  exact h2

/-- All four unmodified monomial raw fibers retain their full original signed spin action. -/
theorem generatedSixth_monomial_raw_spin (j : Fin 4) :
    representativeSpinCertificate (generatedSixthRawGenerator (Fin.castAdd 1 j)).val.1
      (generatedSixthMonomialSpinModel j).coordinate
      (generatedSixthMonomialSpinModel j).phase := by
  fin_cases j
  · exact generatedSixth_monomial_conjugate_spin 0
  · exact generatedSixth_monomial_conjugate_spin 1
  · exact generatedSixth_monomial_conjugate_spin 2
  · change representativeSpinCertificate
      (leechRootedA2GeneratingWordFiber leechRootedA2SixthPermutationSwapWord).val.1
      (generatedSixthMonomialSpinModel 3).coordinate
      (generatedSixthMonomialSpinModel 3).phase
    rw [generatedSixth_monomial_spin_swap_model]
    exact generatedSixth_permutation_profile_spin 2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
