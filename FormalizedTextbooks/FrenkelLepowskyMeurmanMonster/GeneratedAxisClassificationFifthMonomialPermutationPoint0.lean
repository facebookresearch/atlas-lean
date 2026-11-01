/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShort0Assembly
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationTensorFixed0

/-! The first corrected original spatial word fixes the complete actual fifth axis. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The genuine matrix, short and tensor coordinates of the original fifth axis are all fixed. -/
theorem generatedFifth_monomial_permutation_full_fixed_0 :
    rhoLocal (localFiberIntoH (generatedFifthMonomialPermutationCorrectedFiber 0))
      generatedFifthAxis = generatedFifthAxis :=
  generatedFifth_monomial_permutation_full_fixed_of_blocks 0
    (generatedFifth_monomial_permutation_short_fixed_0
      generatedFifth_monomial_permutation_spin_plan_0)
    generatedFifth_monomial_permutation_tensor_fixed_0

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
