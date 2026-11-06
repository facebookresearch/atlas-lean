/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthInverseMasksCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthMaskAction

/-! Whole original inverse extraspecial action from checked complete forward images. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem fourth_inverse_mask_unit (i : Fin 24) :
    generatedAxisGlobalQMask (2 ^ i.val) = qCoordinateGenerator i := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    exact co1NonsplitMask_unit i
  · rfl

private theorem fourth_inverse_central_square (c : ZMod 2) :
    qCentral c * qCentral c = 1 := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    funext j
    change (0 : ZMod 2) + 0 = 0
    norm_num
  · apply toAdd.injective
    change c + c + qBeta 0 0 = 0
    rw [qBeta_zero_left, add_zero, CharTwo.add_self_eq_zero]

/-- Each candidate inverse column and its actual central bit return the true original generator. -/
theorem generatedAxisGlobalOddFourthInverseMaskGenerator_forward (k : Fin 4) (i : Fin 24) :
    spinConjugation (generatedAxisGlobalOddFourthComparisonFiber k).val.1
      (generatedAxisGlobalQMask (generatedAxisGlobalOddFourthInverseMaskColumns k i)) =
    qCentral (generatedAxisGlobalOddFourthInverseMaskPhases k i) * qCoordinateGenerator i := by
  rw [generatedAxisGlobalOddFourthQImage_actual,
    generatedAxisGlobalOddFourthMaskAction_actual]
  rw [generatedAxisGlobalQMaskImage_certificate _ _ _ _ _ _
    (generatedAxisGlobalOddFourthInverseMaskColumn_checked k i)
    (generatedAxisGlobalOddFourthInverseMaskPhase_checked k i), fourth_inverse_mask_unit]

/-- All full inverse generator images are derived from the actual original forward automorphism. -/
theorem generatedAxisGlobalOddFourthInverseMaskGenerator_actual (k : Fin 4) (i : Fin 24) :
    spinConjugation ((generatedAxisGlobalOddFourthComparisonFiber k)⁻¹).val.1
      (qCoordinateGenerator i) = generatedAxisGlobalOddFourthInverseMaskGenerator k i := by
  change spinConjugation ((generatedAxisGlobalOddFourthComparisonFiber k).val.1)⁻¹
    (qCoordinateGenerator i) = _
  rw [map_inv]
  let a := spinConjugation (generatedAxisGlobalOddFourthComparisonFiber k).val.1
  change a.symm (qCoordinateGenerator i) = _
  apply a.injective
  rw [a.apply_symm_apply, generatedAxisGlobalOddFourthInverseMaskGenerator, map_mul,
    co1NonsplitAut_central]
  change qCoordinateGenerator i = qCentral (generatedAxisGlobalOddFourthInverseMaskPhases k i) *
    spinConjugation (generatedAxisGlobalOddFourthComparisonFiber k).val.1
      (generatedAxisGlobalQMask (generatedAxisGlobalOddFourthInverseMaskColumns k i))
  rw [generatedAxisGlobalOddFourthInverseMaskGenerator_forward,
    ← mul_assoc, fourth_inverse_central_square, one_mul]

/-- Each inverse cached lift retains its complete original binary base. -/
theorem generatedAxisGlobalOddFourthInverseMaskGenerator_base (k : Fin 4) (i : Fin 24) :
    toAdd (generatedAxisGlobalOddFourthInverseMaskGenerator k i).base =
      monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalOddFourthInverseMaskColumns k i) := by
  ext j
  change (0 : ZMod 2) +
    monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalOddFourthInverseMaskColumns k i) j = _
  exact zero_add _

/-- Each inverse cached lift retains its complete original central coefficient. -/
theorem generatedAxisGlobalOddFourthInverseMaskGenerator_coeff (k : Fin 4) (i : Fin 24) :
    toAdd (generatedAxisGlobalOddFourthInverseMaskGenerator k i).coeff =
      generatedAxisGlobalOddFourthInverseMaskPhases k i := by
  change generatedAxisGlobalOddFourthInverseMaskPhases k i + 0 +
    qBeta 0 (monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalOddFourthInverseMaskColumns k i)) = _
  rw [add_zero, qBeta_zero_left, add_zero]

/-- Every actual inverse original automorphism preserves the original square form. -/
theorem generatedAxisGlobalOddFourthInverseMaskAction_square (k : Fin 4)
    (v : Fin 24 → ZMod 2) :
    squareQuad (qBinaryAction
      (spinConjugation ((generatedAxisGlobalOddFourthComparisonFiber k)⁻¹).val.1) v) = squareQuad v := by
  change squareQuad (spinBinaryAction ((generatedAxisGlobalOddFourthComparisonFiber k)⁻¹).val.1 v) = _
  rw [((generatedAxisGlobalOddFourthComparisonFiber k)⁻¹).property]
  exact leechBinaryAction_squareQuad _ v

/-- The complete original inverse Q action is the checked original inverse polynomial mask action. -/
theorem generatedAxisGlobalOddFourthInverseMaskAction_actual (k : Fin 4) (v : ℕ) :
    spinConjugation ((generatedAxisGlobalOddFourthComparisonFiber k)⁻¹).val.1
      (generatedAxisGlobalQMask v) =
    generatedAxisGlobalQMaskImage (generatedAxisGlobalOddFourthInverseMaskColumns k)
      (generatedAxisGlobalOddFourthInverseMaskRows k)
      (generatedAxisGlobalOddFourthInverseMaskCoefficients k) v := by
  let a := spinConjugation ((generatedAxisGlobalOddFourthComparisonFiber k)⁻¹).val.1
  have hi (i : Fin 24) : a (qCoordinateGenerator i) =
      generatedAxisGlobalOddFourthInverseMaskGenerator k i :=
    generatedAxisGlobalOddFourthInverseMaskGenerator_actual k i
  have hb (i : Fin 24) : qBinaryAction a (Pi.single i 1) =
      monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalOddFourthInverseMaskColumns k i) := by
    have h := qBinaryAction_apply a (qCoordinateGenerator i)
    change qBinaryAction a (Pi.single i 1) = toAdd (a (qCoordinateGenerator i)).base at h
    rw [hi] at h
    exact h.trans (generatedAxisGlobalOddFourthInverseMaskGenerator_base k i)
  have hr : qCorrectionMatrix (qBinaryAction a) =
      monsterCo1GeometryBinaryMaskMatrix (generatedAxisGlobalOddFourthInverseMaskRows k) := by
    ext i j
    change (if i < j then qCocycleDifference (qBinaryAction a)
      (Pi.single i 1) (Pi.single j 1) else 0) = _
    simp only [qCocycleDifference_apply, hb]
    exact (generatedAxisGlobalOddFourthInverseMaskRows_checked k i j).symm
  have hc (i : Fin 24) : co1NonsplitAutPhase a (Pi.single i 1) =
      monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalOddFourthInverseMaskCoefficients k) i := by
    change toAdd (a (qCoordinateGenerator i)).coeff = _
    rw [hi, generatedAxisGlobalOddFourthInverseMaskGenerator_coeff]
    exact (generatedAxisGlobalOddFourthInverseMaskCoefficients_checked k i).symm
  exact generatedAxisGlobalQMaskImage_actual a
    (generatedAxisGlobalOddFourthInverseMaskAction_square k) _ _ _ hb hr hc v

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
