/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationCorrection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthMonomialFrames
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMatrixRecognition

/-! The original six spatial words preserve the actual fifth watermark, including Q corrections. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every actual corrected monomial fiber fixes the entire original fifth matrix block. -/
theorem generatedFifth_monomial_permutation_matrix_fixed (k : Fin 6) :
    (griessConwayEncode (rhoLocal
      (localFiberIntoH (generatedFifthMonomialPermutationCorrectedFiber k)) generatedFifthAxis)).1 =
        (griessConwayEncode generatedFifthAxis).1 := by
  rw [generatedFourth_local_matrix, generatedFifth_monomial_permutation_corrected_spatial]
  exact (generatedFifth_matrix_stabilizer_iff _).mpr (generatedFifthMonomial_section_preserved k)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
