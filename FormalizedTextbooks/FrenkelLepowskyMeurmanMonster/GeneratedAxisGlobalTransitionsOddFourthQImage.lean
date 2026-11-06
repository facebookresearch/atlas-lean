/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthComparisonWords
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortCoordinateCertificate

/-! The full genuine extraspecial conjugation of the four actual Fourth comparison words. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Complete original signed word conjugation followed by its genuine extraspecial correction. -/
def generatedAxisGlobalOddFourthQImage (k : Fin 4) (q : Q) : Q :=
  let r := generatedAxisGlobalOddSourceFastWord
    (generatedAxisGlobalOddFourthComparisonLetters k) q
  generatedAxisGlobalOddFourthComparisonQ k * r *
    (generatedAxisGlobalOddFourthComparisonQ k)⁻¹

/-- This finite formula equals the actual full original spin conjugation. -/
theorem generatedAxisGlobalOddFourthQImage_actual (k : Fin 4) (q : Q) :
    spinConjugation (generatedAxisGlobalOddFourthComparisonFiber k).val.1 q =
      generatedAxisGlobalOddFourthQImage k q := by
  change spinConjugation (spinHolomorphIncl (generatedAxisGlobalOddFourthComparisonQ k) *
    (((generatedAxisGlobalOddFourthComparisonLetters k).map
      generatedAxisGlobalOddSourceFiberLetter).prod).val.1) q = _
  rw [map_mul]
  change spinConjugation (spinHolomorphIncl (generatedAxisGlobalOddFourthComparisonQ k))
    (spinConjugation
      (((generatedAxisGlobalOddFourthComparisonLetters k).map
        generatedAxisGlobalOddSourceFiberLetter).prod).val.1 q) = _
  rw [spinConjugation_incl, generatedAxisGlobalOddSourceFastWord_actual]
  rfl

/-- A complete source-derived Q image gives the actual target short coefficient. -/
theorem generatedAxisGlobalOddFourthShort_coordinate (k : Fin 4)
    (r s : GriessShortIndex) (c : ZMod 2)
    (hc : generatedAxisGlobalOddFourthQImage k (griessShortQ r) =
      qCentral c * griessShortQ s) (x : GriessSpace) :
    (griessConwayEncode (rhoLocal (generatedAxisGlobalOddFourthComparisonLocal k) x)).2.1 s =
      qSign c * (griessConwayEncode x).2.1 r := by
  apply generatedAxisGlobalGriessShort_coordinate_of_QImage
    (generatedAxisGlobalOddFourthComparisonFiber k) r s c
  rw [generatedAxisGlobalOddFourthQImage_actual]
  exact hc

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
