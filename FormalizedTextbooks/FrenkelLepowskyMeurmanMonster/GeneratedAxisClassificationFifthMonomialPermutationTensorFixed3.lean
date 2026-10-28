/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationTensorCertificate3

/-! Actual tensor fixation by the corrected original monomial word. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every original signed tensor coordinate is fixed by this corrected fiber. -/
theorem generatedFifth_monomial_permutation_tensor_fixed_3 :
    localTensorRepresentation (generatedFifthMonomialPermutationCorrectedFiber 3)
      (griessConwayEncode generatedFifthAxis).2.2 =
        (griessConwayEncode generatedFifthAxis).2.2 :=
  generatedFifth_monomial_permutation_tensor_fixed_of_certificate 3
    generatedFifth_monomial_permutation_spin_plan_3
    (generatedFifthMonomialPermutationTensorSource 3)
    (generatedFifthMonomialPermutationTensorBit 3)
    generatedFifth_monomial_permutation_tensor_certificate_3

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
