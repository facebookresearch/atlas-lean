/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationTensorCertificate0

/-! Actual tensor fixation by the first corrected original monomial word. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every original signed tensor coordinate is fixed by this corrected fiber. -/
theorem generatedFifth_monomial_permutation_tensor_fixed_0 :
    localTensorRepresentation (generatedFifthMonomialPermutationCorrectedFiber 0)
      (griessConwayEncode generatedFifthAxis).2.2 =
        (griessConwayEncode generatedFifthAxis).2.2 :=
  generatedFifth_monomial_permutation_tensor_fixed_of_certificate 0
    generatedFifth_monomial_permutation_spin_plan_0
    (generatedFifthMonomialPermutationTensorSource 0)
    (generatedFifthMonomialPermutationTensorBit 0)
    generatedFifth_monomial_permutation_tensor_certificate_0

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
