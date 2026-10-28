/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialTensorModel

/-! Bounded exact original tensor certificate for corrected monomial word 1. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
-- Check the original112 signed affine tensor addresses using the explicit final matrix and full signed phase.
/-- Every original tensor support address is fixed with its actual Parker phase. -/
theorem generatedFourth_monomial_tensor_certificate_1 :
    ∀ j : Fin 28, ∀ s : Fin 4,
      generatedFourthMonomialTensorModelNumerator 1 (generatedFourthLiftSupportAddress j s)
        (generatedFourthQAffineTensorColumns j) =
          generatedFourthLiftIntegerTensor (generatedFourthLiftSupportAddress j s)
            (generatedFourthQAffineTensorColumns j) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
