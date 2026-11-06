/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthComparisonWords
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortCoordinateCertificate

/-! Complete original extraspecial conjugation by both genuine Fifth comparison fibers. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The entire original full-phase finite conjugation of each actual comparison. -/
def generatedAxisGlobalOddFifthQImage (k : Fin 2) (q : Q) : Q :=
  let r := generatedAxisGlobalOddSourceFastWord
    (generatedAxisGlobalOddFifthComparisonPostLetters k)
      (generatedAxisGlobalOddSourceFastLetter 0
        (generatedAxisGlobalSignFullImage (generatedAxisGlobalOddFifthComparisonSign k)
          (generatedAxisGlobalOddSourceFastWord generatedAxisGlobalOddFifthComparisonPreLetters q)))
  generatedAxisGlobalOddFifthComparisonQ k * r *
    (generatedAxisGlobalOddFifthComparisonQ k)⁻¹

/-- Every finite output is genuine conjugation by the original local source fiber. -/
theorem generatedAxisGlobalOddFifthQImage_actual (k : Fin 2) (q : Q) :
    spinConjugation (generatedAxisGlobalOddFifthComparisonFiber k).val.1 q =
      generatedAxisGlobalOddFifthQImage k q := by
  change spinConjugation
    (spinHolomorphIncl (generatedAxisGlobalOddFifthComparisonQ k) *
      (((generatedAxisGlobalOddFifthComparisonPostLetters k).map
        generatedAxisGlobalOddSourceFiberLetter).prod).val.1 * xiSpinLocalFiber.val.1 *
          (generatedFifthSignFiber (generatedAxisGlobalOddFifthComparisonSign k) 0).val.1 *
            ((generatedAxisGlobalOddFifthComparisonPreLetters.map
              generatedAxisGlobalOddSourceFiberLetter).prod).val.1) q = _
  rw [map_mul, map_mul, map_mul, map_mul]
  change spinConjugation (spinHolomorphIncl (generatedAxisGlobalOddFifthComparisonQ k))
    (spinConjugation (((generatedAxisGlobalOddFifthComparisonPostLetters k).map
      generatedAxisGlobalOddSourceFiberLetter).prod).val.1
      (spinConjugation xiSpinLocalFiber.val.1
        (spinConjugation (generatedFifthSignFiber (generatedAxisGlobalOddFifthComparisonSign k) 0).val.1
          (spinConjugation ((generatedAxisGlobalOddFifthComparisonPreLetters.map
            generatedAxisGlobalOddSourceFiberLetter).prod).val.1 q)))) = _
  rw [spinConjugation_incl, generatedAxisGlobalOddSourceFastWord_actual,
    generatedAxisGlobalSignFull_QImage]
  have hxi (r : Q) : spinConjugation xiSpinLocalFiber.val.1 r =
      generatedAxisGlobalOddSourceFastLetter 0 r :=
    generatedAxisGlobalOddSourceFastLetter_actual 0 r
  rw [hxi, generatedAxisGlobalOddSourceFastWord_actual]
  rfl

/-- A full original Q certificate gives the exact selected target short coefficient. -/
theorem generatedAxisGlobalOddFifthShort_coordinate (k : Fin 2)
    (r s : GriessShortIndex) (c : ZMod 2)
    (hc : generatedAxisGlobalOddFifthQImage k (griessShortQ r) = qCentral c * griessShortQ s)
    (x : GriessSpace) :
    (griessConwayEncode (rhoLocal (generatedAxisGlobalOddFifthComparisonLocal k) x)).2.1 s =
      qSign c * (griessConwayEncode x).2.1 r := by
  apply generatedAxisGlobalGriessShort_coordinate_of_QImage
    (generatedAxisGlobalOddFifthComparisonFiber k) r s c
  rw [generatedAxisGlobalOddFifthQImage_actual]
  exact hc

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
