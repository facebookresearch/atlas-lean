/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneGaussianQData

/-! The literal Pauli data is checked against the original complete extraspecial action. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- All sixty-four genuine source elements retain both coordinates and their central coefficients.
/-- Every literal Gaussian retains the complete original binary and central coordinates. -/
theorem generatedSeventhXiPlaneGaussianQ_coordinates : ∀ a : Fin 64,
    toAdd (generatedSeventhXiPlaneGaussianQLiteral a).base =
      toAdd (generatedSeventhXiPlaneGaussianQ (monsterNortonGrayCoefficients a)).base ∧
    toAdd (generatedSeventhXiPlaneGaussianQLiteral a).coeff =
      toAdd (generatedSeventhXiPlaneGaussianQ (monsterNortonGrayCoefficients a)).coeff := by
  decide +kernel

/-- Every literal Gaussian Q element is the full actual corrected source element. -/
theorem generatedSeventhXiPlaneGaussianQLiteral_actual (a : Fin 64) :
    generatedSeventhXiPlaneGaussianQLiteral a =
      generatedSeventhXiPlaneGaussianQ (monsterNortonGrayCoefficients a) := by
  have h := generatedSeventhXiPlaneGaussianQ_coordinates a
  apply NormalizedCocycleExtension.Extension.ext
  · exact toAdd.injective h.1
  · exact toAdd.injective h.2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
