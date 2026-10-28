/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortCoordinateCertificate

/-! Complete original inverse preferred-Q certificates determine the selected actual framed short coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem selected_central_square (c : ZMod 2) : qCentral c * qCentral c = 1 := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply Multiplicative.toAdd.injective
    funext i
    change (0 : ZMod 2) + 0 = 0
    norm_num
  · apply Multiplicative.toAdd.injective
    change c + c + qBeta 0 0 = 0
    rw [qBeta_zero_left, add_zero, CharTwo.add_self_eq_zero]

/-- Both checked complete bit identities give the actual full original inverse preferred-Q image. -/
theorem generatedAxisGlobalOddFourthSelectedInverseQ_actual (k : Fin 4) (j : Fin 4584)
    (hb : generatedAxisGlobalQMaskVector (generatedAxisGlobalOddFourthInverseMaskColumns k)
      (generatedAxisGlobalShortMask (generatedAxisGlobalOddFourthSelectedTarget j)) =
        generatedAxisGlobalShortMask (generatedAxisGlobalOddFourthSelectedSource k j))
    (hc : (if (generatedAxisGlobalQMaskCentral (generatedAxisGlobalOddFourthInverseMaskRows k)
      (generatedAxisGlobalOddFourthInverseMaskCoefficients k)
      (generatedAxisGlobalShortMask (generatedAxisGlobalOddFourthSelectedTarget j))).testBit 0
      then (1 : ZMod 2) else 0) = generatedAxisGlobalOddFourthSelectedPhase k j) :
    spinConjugation ((generatedAxisGlobalOddFourthComparisonFiber k)⁻¹).val.1
      (griessShortQ (generatedAxisGlobalOddFourthSelectedTarget j)) =
      qCentral (generatedAxisGlobalOddFourthSelectedPhase k j) *
        griessShortQ (generatedAxisGlobalOddFourthSelectedSource k j) := by
  rw [← generatedAxisGlobalShortQFinite_actual, generatedAxisGlobalShortMask_Q_actual,
    generatedAxisGlobalOddFourthInverseMaskAction_actual]
  conv_rhs => rw [← generatedAxisGlobalShortQFinite_actual,
    generatedAxisGlobalShortMask_Q_actual]
  exact generatedAxisGlobalQMaskImage_certificate _ _ _ _ _ _ hb hc

/-- The inverse certificate implies the complete actual forward preferred-Q image with the same central bit. -/
theorem generatedAxisGlobalOddFourthSelectedForwardQ_actual (k : Fin 4) (j : Fin 4584)
    (hq : spinConjugation ((generatedAxisGlobalOddFourthComparisonFiber k)⁻¹).val.1
      (griessShortQ (generatedAxisGlobalOddFourthSelectedTarget j)) =
      qCentral (generatedAxisGlobalOddFourthSelectedPhase k j) *
        griessShortQ (generatedAxisGlobalOddFourthSelectedSource k j)) :
    spinConjugation (generatedAxisGlobalOddFourthComparisonFiber k).val.1
      (griessShortQ (generatedAxisGlobalOddFourthSelectedSource k j)) =
      qCentral (generatedAxisGlobalOddFourthSelectedPhase k j) *
        griessShortQ (generatedAxisGlobalOddFourthSelectedTarget j) := by
  let a := spinConjugation (generatedAxisGlobalOddFourthComparisonFiber k).val.1
  change a (griessShortQ (generatedAxisGlobalOddFourthSelectedSource k j)) = _
  change spinConjugation ((generatedAxisGlobalOddFourthComparisonFiber k).val.1)⁻¹ _ = _ at hq
  rw [map_inv] at hq
  change a.symm _ = _ at hq
  apply a.symm.injective
  rw [a.symm_apply_apply, map_mul, co1NonsplitAut_central, hq,
    ← mul_assoc, selected_central_square, one_mul]

/-- Each actual selected framed short coefficient is the full original source coefficient and central phase. -/
theorem generatedAxisGlobalOddFourthSelectedShort_actual (k : Fin 4) (j : Fin 4584)
    (hq : spinConjugation ((generatedAxisGlobalOddFourthComparisonFiber k)⁻¹).val.1
      (griessShortQ (generatedAxisGlobalOddFourthSelectedTarget j)) =
      qCentral (generatedAxisGlobalOddFourthSelectedPhase k j) *
        griessShortQ (generatedAxisGlobalOddFourthSelectedSource k j))
    (x : GriessSpace) :
    (griessConwayEncode (rhoLocal (generatedAxisGlobalOddFourthComparisonLocal k) x)).2.1
      (generatedAxisGlobalOddFourthSelectedTarget j) =
      qSign (generatedAxisGlobalOddFourthSelectedPhase k j) *
        (griessConwayEncode x).2.1 (generatedAxisGlobalOddFourthSelectedSource k j) :=
  generatedAxisGlobalGriessShort_coordinate_of_QImage _ _ _ _
    (generatedAxisGlobalOddFourthSelectedForwardQ_actual k j hq) x

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
