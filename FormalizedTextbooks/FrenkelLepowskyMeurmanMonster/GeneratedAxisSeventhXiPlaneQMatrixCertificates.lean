/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneQMatrixData

/-! Ordinary-kernel certificates for the original corrected Xi action and full Q cocycle. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
open Multiplicative

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exhaustive finite source-image and cocycle checks are replayed by the ordinary kernel.
/-- Every original preferred basis image has its full certified binary image and central phase. -/
theorem generatedSeventhXiPlaneQMatrix_basis : ∀ j : Fin 24,
    toAdd (generatedSeventhXiPlaneQImage (xiSpinBinaryBasisLift j)).base =
        generatedSeventhXiPlaneQMatrix *ᵥ Pi.single j 1 ∧
      toAdd (generatedSeventhXiPlaneQImage (xiSpinBinaryBasisLift j)).coeff =
        generatedFourthLiftQMatrixPhase generatedSeventhXiPlaneQPhaseMatrix (Pi.single j 1) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exhaustive finite source-image and cocycle checks are replayed by the ordinary kernel.
/-- All original basis cocycle pairs retain the genuine extraspecial multiplication. -/
theorem generatedSeventhXiPlaneQMatrix_cocycle : ∀ i j : Fin 24,
    qBeta (generatedSeventhXiPlaneQMatrix *ᵥ Pi.single i 1)
        (generatedSeventhXiPlaneQMatrix *ᵥ Pi.single j 1) =
      qBeta (Pi.single i 1) (Pi.single j 1) +
        generatedSeventhXiPlaneQPhaseMatrix i j + generatedSeventhXiPlaneQPhaseMatrix j i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
