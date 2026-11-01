/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationTensorCertificate5

/-! Actual tensor fixation by the corrected original monomial word. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every original signed tensor coordinate is fixed by this corrected fiber. -/
theorem generatedFifth_monomial_permutation_tensor_fixed_5 :
    localTensorRepresentation (generatedFifthMonomialPermutationCorrectedFiber 5)
      (griessConwayEncode generatedFifthAxis).2.2 =
        (griessConwayEncode generatedFifthAxis).2.2 :=
  generatedFifth_monomial_permutation_tensor_fixed_of_certificate 5
    generatedFifth_monomial_permutation_spin_plan_5
    (generatedFifthMonomialPermutationTensorSource 5)
    (generatedFifthMonomialPermutationTensorBit 5)
    generatedFifth_monomial_permutation_tensor_certificate_5

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
