/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparisonActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthRepresentative

/-! Four literal actual local comparison words for the original root-two/root-four transition images. Complete vector recognition is proved separately. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option autoImplicit false

/-- Original root index for each actual comparison word. -/
def generatedAxisGlobalOddFourthComparisonRoot : Fin 4 → Fin 9 := ![2, 2, 4, 4]

/-- The negative entries use the genuine inverse of original triality. -/
def generatedAxisGlobalOddFourthComparisonInverse : Fin 4 → Bool := ![false, true, false, true]

/-- Literal original source letters in group-product order, including the final sign-sixteen operation. -/
def generatedAxisGlobalOddFourthComparisonLetters : Fin 4 → List (Fin 10) := ![
    [2, 8, 6, 8, 6, 6, 8, 6, 6, 6, 8, 7, 7, 7, 1, 6, 6],
    [2, 6, 8, 7, 8, 7, 8, 6, 8, 6, 8, 6, 6, 8, 6, 6, 8, 0, 6, 6],
    [2, 6, 6, 6, 8, 7, 8, 7, 7, 8, 6, 6, 6, 8, 6, 8, 7, 8, 0],
    [2, 6, 6, 6, 8, 7, 8, 7, 7, 8, 6, 6, 6, 8, 6, 8, 7, 8, 1]]

/-- Exact original extraspecial binary correction masks. -/
def generatedAxisGlobalOddFourthComparisonQMask : Fin 4 → ℕ := ![3303028, 8422760, 32809, 2097744]

/-- Original central phases of the full extraspecial corrections. -/
def generatedAxisGlobalOddFourthComparisonPhase : Fin 4 → ZMod 2 := ![1, 0, 1, 1]

/-- The complete correction is an actual element of the fixed original extraspecial group. -/
def generatedAxisGlobalOddFourthComparisonQ (k : Fin 4) : Q :=
  ⟨ofAdd (monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalOddFourthComparisonQMask k)),
    generatedAxisGlobalOddFourthComparisonPhase k⟩

/-- Genuine original local letters and the full extraspecial correction define an actual fiber. -/
def generatedAxisGlobalOddFourthComparisonFiber (k : Fin 4) : localFiberSubgroup :=
  localFiberIncl (generatedAxisGlobalOddFourthComparisonQ k) *
    ((generatedAxisGlobalOddFourthComparisonLetters k).map
      generatedAxisGlobalOddSourceFiberLetter).prod

/-- The exact local transporter is the image of that complete actual fiber. -/
def generatedAxisGlobalOddFourthComparisonLocal (k : Fin 4) : H :=
  localFiberIntoH (generatedAxisGlobalOddFourthComparisonFiber k)

/-- The source transition is literally original forward or inverse triality after the genuine root word. -/
def generatedAxisGlobalOddFourthComparisonAction (k : Fin 4) : ↥G :=
  (if generatedAxisGlobalOddFourthComparisonInverse k then extraIntoGenerated⁻¹
    else extraIntoGenerated) *
      localIntoGenerated (generatedAxisGlobalOddSourceRootLocalWord
        (generatedAxisGlobalOddFourthComparisonRoot k))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
