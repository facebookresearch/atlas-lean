/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialQMatrixData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.XiSpinBinaryAction

/-! Full original binary and central basis-image checks for corrected monomial word 3. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped Matrix

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
-- Check24 genuine basis images, retaining the exact preferred central coefficients.
/-- Every actual basis lift has its complete original Q image certified. -/
theorem generatedFourth_monomial_q_basis_certificate_3 : ∀ j : Fin 24,
    toAdd (generatedFourthMonomialCorrectedQImage 3 (xiSpinBinaryBasisLift j)).base =
      (generatedFourthMonomialQBinaryMatrix 3).col j ∧
    toAdd (generatedFourthMonomialCorrectedQImage 3 (xiSpinBinaryBasisLift j)).coeff =
      generatedFourthMonomialQPhaseMatrix 3 j j := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
