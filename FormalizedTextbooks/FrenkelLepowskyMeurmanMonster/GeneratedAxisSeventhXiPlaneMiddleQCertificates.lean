/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneMiddleQData

/-! Ordinary kernel checks bind the compact middle Q formula to all original source phases. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped Matrix

/-- The seven original source letters, in application order. -/
def generatedSeventhXiMiddleQLetters : Fin 7 → Fin 3 := ![2, 0, 1, 0, 2, 1, 2]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite certificate binds all twenty-four original extraspecial basis lifts.
/-- All initial preferred basis states are the genuine original basis lifts. -/
theorem generatedSeventhXiMiddleQ_start : ∀ j : Fin 24,
    toAdd (generatedSeventhXiMiddleQState 0 j).base = toAdd (xiSpinBinaryBasisLift j).base ∧
      toAdd (generatedSeventhXiMiddleQState 0 j).coeff = toAdd (xiSpinBinaryBasisLift j).coeff := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Each finite stage checks the actual source automorphism, including central phases.
/-- Every original middle word step agrees with the complete cached Q state. -/
theorem generatedSeventhXiMiddleQ_step : ∀ r : Fin 7, ∀ j : Fin 24,
    let q := generatedSeventhQGenerator (generatedSeventhXiMiddleQLetters r)
      (generatedSeventhXiMiddleQState r.castSucc j)
    toAdd q.base = toAdd (generatedSeventhXiMiddleQState r.succ j).base ∧
      toAdd q.coeff = toAdd (generatedSeventhXiMiddleQState r.succ j).coeff := by
  intro r
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The 576 basis-pair equations certify the actual cocycle, rather than only the polar form.
/-- The full compact central correction satisfies the original Q cocycle identity. -/
theorem generatedSeventhXiMiddleQ_cocycle : ∀ i j : Fin 24,
    qBeta (generatedSeventhXiMiddleQMatrix *ᵥ Pi.single i 1)
      (generatedSeventhXiMiddleQMatrix *ᵥ Pi.single j 1) =
    qBeta (Pi.single i 1) (Pi.single j 1) +
      generatedSeventhXiMiddleQPhase i j + generatedSeventhXiMiddleQPhase j i := by
  decide +kernel

/-- The certified finite matrices define a homomorphism on the genuine extraspecial group. -/
def generatedSeventhXiMiddleQHom : Q →* Q :=
  generatedFourthLiftQMatrixHom generatedSeventhXiMiddleQMatrix
    generatedSeventhXiMiddleQPhase generatedSeventhXiMiddleQ_cocycle

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Every full compact basis image is compared with its original checked source state.
/-- The compact homomorphism has exactly the checked full preferred-basis images. -/
theorem generatedSeventhXiMiddleQHom_basis : ∀ j : Fin 24,
    toAdd (generatedSeventhXiMiddleQHom (xiSpinBinaryBasisLift j)).base =
      toAdd (generatedSeventhXiMiddleQState 7 j).base ∧
    toAdd (generatedSeventhXiMiddleQHom (xiSpinBinaryBasisLift j)).coeff =
      toAdd (generatedSeventhXiMiddleQState 7 j).coeff := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
