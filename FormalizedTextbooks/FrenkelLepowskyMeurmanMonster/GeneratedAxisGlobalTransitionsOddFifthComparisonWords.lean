/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparisonActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsCanonicalFifthRationalPacket

/-! Two literal genuine full-fiber comparison words for the root-three transition images. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option autoImplicit false

/-- The genuine positive and inverse triality choices. -/
def generatedAxisGlobalOddFifthComparisonInverse : Fin 2 → Bool := ![false, true]

/-- The original source permutation product before the exact Golay sign. -/
def generatedAxisGlobalOddFifthComparisonPreLetters : List (Fin 10) := [8, 6, 8, 7, 8, 6]

/-- The genuine original Golay sign labels. -/
def generatedAxisGlobalOddFifthComparisonSign : Fin 2 → Fin 4096 := ![1024, 0]

/-- The original post-Xi permutation product includes the complete outside-pair matching word. -/
def generatedAxisGlobalOddFifthComparisonPostLetters : Fin 2 → List (Fin 10) :=
  ![[7, 8, 7, 8, 6, 8, 6, 8, 6, 6, 8, 6, 8, 6, 8, 6, 6, 6, 8],
    [7, 7, 8, 7, 7, 7, 8, 6, 8, 6, 6, 8, 6, 6, 6, 6, 8, 6, 8, 7, 8]]

/-- Full exact original extraspecial correction masks. -/
def generatedAxisGlobalOddFifthComparisonQMask : Fin 2 → ℕ := ![11540315, 10024298]

/-- Actual central phases of the complete corrections. -/
def generatedAxisGlobalOddFifthComparisonPhase : Fin 2 → ZMod 2 := ![1, 0]

/-- These corrections belong to the fixed original extraspecial group. -/
def generatedAxisGlobalOddFifthComparisonQ (k : Fin 2) : Q :=
  ⟨ofAdd (monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalOddFifthComparisonQMask k)),
    ofAdd (generatedAxisGlobalOddFifthComparisonPhase k)⟩

/-- The entire genuine local frame, retaining all spin phases and the original sign action. -/
def generatedAxisGlobalOddFifthComparisonFiber (k : Fin 2) : localFiberSubgroup :=
  localFiberIncl (generatedAxisGlobalOddFifthComparisonQ k) *
    ((generatedAxisGlobalOddFifthComparisonPostLetters k).map
      generatedAxisGlobalOddSourceFiberLetter).prod * xiSpinLocalFiber *
        generatedFifthSignFiber (generatedAxisGlobalOddFifthComparisonSign k) 0 *
          (generatedAxisGlobalOddFifthComparisonPreLetters.map
            generatedAxisGlobalOddSourceFiberLetter).prod

/-- The exact original local image of the complete comparison fiber. -/
def generatedAxisGlobalOddFifthComparisonLocal (k : Fin 2) : H :=
  localFiberIntoH (generatedAxisGlobalOddFifthComparisonFiber k)

/-- Actual root-three source transition with original forward or inverse triality. -/
def generatedAxisGlobalOddFifthComparisonAction (k : Fin 2) : ↥G :=
  (if generatedAxisGlobalOddFifthComparisonInverse k then extraIntoGenerated⁻¹
    else extraIntoGenerated) * localIntoGenerated (generatedAxisGlobalOddSourceRootLocalWord 3)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
