/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortFastImage
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortMatrixData

/-! Bounded full-Q basis-image certificate block 4 for the corrected actual spin action. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option maxRecDepth 100000

set_option maxHeartbeats 16000000 in
-- Four actual basis lifts retain their complete original central and binary images.
/-- Actual corrected-Q images for binary basis coordinates 16 through 19. -/
theorem generatedFourth_lift_short_basis_certificate_4 :
    ∀ k : Fin 4,
      let j : Fin 24 := ⟨16 + k.val, by omega⟩
      toAdd (generatedFourthLiftShortQFast (xiSpinBinaryBasisLift j)).base =
          generatedFourthLiftQBinaryMatrix.col j ∧
        toAdd (generatedFourthLiftShortQFast (xiSpinBinaryBasisLift j)).coeff =
          generatedFourthLiftQPhaseMatrix j j := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
