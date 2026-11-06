/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialSpinModelAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialTensorCertificate0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialTensorCertificate1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialTensorCertificate2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialTensorCertificate3

/-! Exact support certificates and original orthogonality fix all four entire tensors. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- All four compact evaluators preserve every actual nonzero tensor support coefficient. -/
theorem generatedFourth_monomial_tensor_model_certificates (k : Fin 4) :
    ∀ j : Fin 28, ∀ s : Fin 4,
      generatedFourthMonomialTensorModelNumerator k (generatedFourthLiftSupportAddress j s)
        (generatedFourthQAffineTensorColumns j) =
          generatedFourthLiftIntegerTensor (generatedFourthLiftSupportAddress j s)
            (generatedFourthQAffineTensorColumns j) := by
  fin_cases k
  · exact generatedFourth_monomial_tensor_certificate_0
  · exact generatedFourth_monomial_tensor_certificate_1
  · exact generatedFourth_monomial_tensor_certificate_2
  · exact generatedFourth_monomial_tensor_certificate_3

/-- The entire genuine tensor is fixed by each of the four actual corrected monomial lifts. -/
theorem generatedFourth_monomial_tensor_fixed (k : Fin 4) :
    localTensorRepresentation (generatedFourthMonomialCorrectedFiber k)
      (griessConwayEncode generatedFourthAxis).2.2 =
        (griessConwayEncode generatedFourthAxis).2.2 := by
  apply generatedFourth_monomial_tensor_fixed_of_certificate
  intro j s
  rw [generatedFourth_monomial_tensor_numerators_eq k
    (generatedFourth_monomial_spin_plans_valid k)]
  exact generatedFourth_monomial_tensor_model_certificates k j s

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
