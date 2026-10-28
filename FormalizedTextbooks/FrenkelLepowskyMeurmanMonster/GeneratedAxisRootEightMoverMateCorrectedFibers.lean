/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverMateMatrixFixation

/-! Genuine explicitly corrected positive mover and mate with all original Q coordinates retained. -/
@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

/-- Complete original translations of the two actual corrected positive generators. -/
def generatedRootEightMoverMateTranslation : Fin 2 → ℕ := ![4073, 2528]

/-- Complete original modulations of the two actual corrected positive generators. -/
def generatedRootEightMoverMateModulation : Fin 2 → ℕ := ![500, 433]

/-- The actual original Q correction, including its genuine central coefficient zero. -/
def generatedRootEightMoverMateCorrection (j : Fin 2) : Q :=
  ⟨ofAdd (fun i => if i.val < 12 then
      if (generatedRootEightMoverMateTranslation j).testBit i.val then 1 else 0
    else if (generatedRootEightMoverMateModulation j).testBit (i.val - 12) then 1 else 0),
    ofAdd 0⟩

/-- The actual corrected positive mover in the genuine local fiber group. -/
def generatedRootEightMoverCorrectedFiber : localFiberSubgroup :=
  localFiberIncl (generatedRootEightMoverMateCorrection 0) * generatedRootEightMoverPositiveFiber

/-- The actual corrected positive mate in the genuine local fiber group. -/
def generatedRootEightMateCorrectedFiber : localFiberSubgroup :=
  localFiberIncl (generatedRootEightMoverMateCorrection 1) * generatedRootEightMatePositiveFiber

/-- The genuine original local mover element represented by the entire corrected fiber. -/
def generatedRootEightMoverCorrectedLocal : H := localFiberIntoH generatedRootEightMoverCorrectedFiber

/-- The genuine original local mate element represented by the entire corrected fiber. -/
def generatedRootEightMateCorrectedLocal : H := localFiberIntoH generatedRootEightMateCorrectedFiber

/-- The complete corrected mover spin is the actual Q correction followed by its exact compact operator. -/
theorem generatedRootEight_mover_corrected_spin : generatedRootEightMoverCorrectedFiber.val.1 =
    spinHolomorphIncl (generatedRootEightMoverMateCorrection 0) * generatedRootEightCompactSpin 10 := rfl

/-- The complete corrected mate spin is the actual Q correction followed by its exact compact operator. -/
theorem generatedRootEight_mate_corrected_spin : generatedRootEightMateCorrectedFiber.val.1 =
    spinHolomorphIncl (generatedRootEightMoverMateCorrection 1) * generatedRootEightCompactSpin 11 := rfl

/-- The entire actual canonical matrix is fixed by the genuine corrected mover. -/
theorem generatedRootEight_mover_corrected_canonical_matrix :
    localMatrixRepresentation generatedRootEightMoverCorrectedFiber
      (griessConwayEncode generatedRootEightCanonicalPositiveAxis).1 =
        (griessConwayEncode generatedRootEightCanonicalPositiveAxis).1 :=
  generatedRootEight_mover_corrected_matrix _

/-- The entire actual canonical matrix is fixed by the genuine corrected mate. -/
theorem generatedRootEight_mate_corrected_canonical_matrix :
    localMatrixRepresentation generatedRootEightMateCorrectedFiber
      (griessConwayEncode generatedRootEightCanonicalPositiveAxis).1 =
        (griessConwayEncode generatedRootEightCanonicalPositiveAxis).1 :=
  generatedRootEight_mate_corrected_matrix _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
