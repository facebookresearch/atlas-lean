/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneGaussianPackedData

/-! Complete original Pauli and diagonal coefficients are retained by the packed evaluator. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Every original full-phase Pauli summand is checked, with no omitted bits.
/-- All packed shifts, modulations, and central signs equal their actual source-bound labels. -/
theorem generatedSeventhXiGaussianPacked_pauli : ∀ a : Fin 64,
    generatedSeventhXiGaussianPackedShift a = generatedSeventhXiPlaneGaussianTranslationLabel a ∧
    generatedSeventhXiGaussianPackedModulation a =
      (generatedSeventhXiPlaneGaussianModulationLabel a).val ∧
    generatedSeventhXiGaussianPackedCentral a = generatedSeventhXiPlaneGaussianCentralSign a := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The complete source diagonal is retained at every one of its 4096 coordinates.
/-- Every packed diagonal coefficient is the full actual source-conjugated Gaussian coefficient. -/
theorem generatedSeventhXiGaussianPacked_gamma : ∀ d : Fin 4096,
    generatedSeventhXiGaussianPackedGamma d = generatedSeventhXiPlaneConjugateGammaBit d := by
  decide +kernel

/-- Compact Pauli phases retain the complete original binary and central source phase. -/
theorem generatedSeventhXiGaussianPacked_phase (a : Fin 64) (d : Fin 4096) :
    generatedSeventhXiGaussianPackedPhase a d = generatedSeventhXiPlaneGaussianBitPhase a d := by
  simp only [generatedSeventhXiGaussianPackedPhase, generatedSeventhXiPlaneGaussianBitPhase,
    (generatedSeventhXiGaussianPacked_pauli a).2.1,
    (generatedSeventhXiGaussianPacked_pauli a).2.2]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
