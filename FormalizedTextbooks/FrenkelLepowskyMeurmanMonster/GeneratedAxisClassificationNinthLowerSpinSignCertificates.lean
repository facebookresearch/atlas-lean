/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsYAllConjugation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometrySignActions

/-! Independent finite original low-Y source compatibility and code-basis certificates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
open Multiplicative
set_option maxRecDepth 100000

set_option maxHeartbeats 12000000 in
-- Check every original low-code source normalizer on the twenty-four actual Q coordinates.
/-- The actual low-code source spin candidates have the complete genuine sign binary columns. -/
theorem generatedNinth_lower_spin_sign_generator_certificate : ∀ (k : Fin 11) (j : Fin 24),
    toAdd (monsterNortonYImage (generatedNinthLowerSpinCode k)
      (xiSpinBinaryBasisLift j)).base =
        (monsterCo1GeometrySignBinary (Fin.castAdd 1 k)).col j := by
  decide +kernel

/-- Each literal low-code label is precisely its original source basis coordinate. -/
theorem generatedNinth_lower_spin_code_basis : ∀ k : Fin 11,
    golayLabelCoefficients (⟨(generatedNinthLowerSpinCode k).val, by omega⟩ : Fin 4096) =
      (Pi.single (Fin.castAdd 1 k) 1 : SpinIndex) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
