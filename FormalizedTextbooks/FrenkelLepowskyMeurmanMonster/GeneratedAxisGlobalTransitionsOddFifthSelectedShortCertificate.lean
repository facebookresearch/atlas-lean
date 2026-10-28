/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthSelectedShortData
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
theorem generatedAxisGlobalOddFifthSelectedInverseQ_actual (k : Fin 2) (j : Fin 4136)
    (hb : generatedAxisGlobalQMaskVector (generatedAxisGlobalOddFifthInverseMaskColumns k)
      (generatedAxisGlobalShortMask (generatedAxisGlobalOddFifthSelectedTarget j)) =
        generatedAxisGlobalShortMask (generatedAxisGlobalOddFifthSelectedSource k j))
    (hc : (if (generatedAxisGlobalQMaskCentral (generatedAxisGlobalOddFifthInverseMaskRows k)
      (generatedAxisGlobalOddFifthInverseMaskCoefficients k)
      (generatedAxisGlobalShortMask (generatedAxisGlobalOddFifthSelectedTarget j))).testBit 0
      then (1 : ZMod 2) else 0) = generatedAxisGlobalOddFifthSelectedPhase k j) :
    spinConjugation ((generatedAxisGlobalOddFifthComparisonFiber k)⁻¹).val.1
      (griessShortQ (generatedAxisGlobalOddFifthSelectedTarget j)) =
      qCentral (generatedAxisGlobalOddFifthSelectedPhase k j) *
        griessShortQ (generatedAxisGlobalOddFifthSelectedSource k j) := by
  rw [← generatedAxisGlobalShortQFinite_actual, generatedAxisGlobalShortMask_Q_actual,
    generatedAxisGlobalOddFifthInverseMaskAction_actual]
  conv_rhs => rw [← generatedAxisGlobalShortQFinite_actual,
    generatedAxisGlobalShortMask_Q_actual]
  exact generatedAxisGlobalQMaskImage_certificate _ _ _ _ _ _ hb hc

/-- The inverse certificate implies the complete actual forward preferred-Q image with the same central bit. -/
theorem generatedAxisGlobalOddFifthSelectedForwardQ_actual (k : Fin 2) (j : Fin 4136)
    (hq : spinConjugation ((generatedAxisGlobalOddFifthComparisonFiber k)⁻¹).val.1
      (griessShortQ (generatedAxisGlobalOddFifthSelectedTarget j)) =
      qCentral (generatedAxisGlobalOddFifthSelectedPhase k j) *
        griessShortQ (generatedAxisGlobalOddFifthSelectedSource k j)) :
    spinConjugation (generatedAxisGlobalOddFifthComparisonFiber k).val.1
      (griessShortQ (generatedAxisGlobalOddFifthSelectedSource k j)) =
      qCentral (generatedAxisGlobalOddFifthSelectedPhase k j) *
        griessShortQ (generatedAxisGlobalOddFifthSelectedTarget j) := by
  let a := spinConjugation (generatedAxisGlobalOddFifthComparisonFiber k).val.1
  change a (griessShortQ (generatedAxisGlobalOddFifthSelectedSource k j)) = _
  change spinConjugation ((generatedAxisGlobalOddFifthComparisonFiber k).val.1)⁻¹ _ = _ at hq
  rw [map_inv] at hq
  change a.symm _ = _ at hq
  apply a.symm.injective
  rw [a.symm_apply_apply, map_mul, co1NonsplitAut_central, hq,
    ← mul_assoc, selected_central_square, one_mul]

/-- Each actual selected framed short coefficient is the full original source coefficient and central phase. -/
theorem generatedAxisGlobalOddFifthSelectedShort_actual (k : Fin 2) (j : Fin 4136)
    (hq : spinConjugation ((generatedAxisGlobalOddFifthComparisonFiber k)⁻¹).val.1
      (griessShortQ (generatedAxisGlobalOddFifthSelectedTarget j)) =
      qCentral (generatedAxisGlobalOddFifthSelectedPhase k j) *
        griessShortQ (generatedAxisGlobalOddFifthSelectedSource k j))
    (x : GriessSpace) :
    (griessConwayEncode (rhoLocal (generatedAxisGlobalOddFifthComparisonLocal k) x)).2.1
      (generatedAxisGlobalOddFifthSelectedTarget j) =
      qSign (generatedAxisGlobalOddFifthSelectedPhase k j) *
        (griessConwayEncode x).2.1 (generatedAxisGlobalOddFifthSelectedSource k j) :=
  generatedAxisGlobalGriessShort_coordinate_of_QImage _ _ _ _
    (generatedAxisGlobalOddFifthSelectedForwardQ_actual k j hq) x

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
