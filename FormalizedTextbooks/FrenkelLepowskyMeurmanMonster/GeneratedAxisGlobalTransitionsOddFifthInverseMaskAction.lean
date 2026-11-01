/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthInverseMasksCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMaskAction

/-! Whole original inverse extraspecial action from checked complete forward images. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem fifth_inverse_mask_unit (i : Fin 24) :
    generatedAxisGlobalQMask (2 ^ i.val) = qCoordinateGenerator i := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    exact co1NonsplitMask_unit i
  · rfl

private theorem fifth_inverse_central_square (c : ZMod 2) :
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
theorem generatedAxisGlobalOddFifthInverseMaskGenerator_forward (k : Fin 2) (i : Fin 24) :
    spinConjugation (generatedAxisGlobalOddFifthComparisonFiber k).val.1
      (generatedAxisGlobalQMask (generatedAxisGlobalOddFifthInverseMaskColumns k i)) =
    qCentral (generatedAxisGlobalOddFifthInverseMaskPhases k i) * qCoordinateGenerator i := by
  rw [generatedAxisGlobalOddFifthQImage_actual,
    generatedAxisGlobalOddFifthMaskAction_actual]
  rw [generatedAxisGlobalQMaskImage_certificate _ _ _ _ _ _
    (generatedAxisGlobalOddFifthInverseMaskColumn_checked k i)
    (generatedAxisGlobalOddFifthInverseMaskPhase_checked k i), fifth_inverse_mask_unit]

/-- All full inverse generator images are derived from the actual original forward automorphism. -/
theorem generatedAxisGlobalOddFifthInverseMaskGenerator_actual (k : Fin 2) (i : Fin 24) :
    spinConjugation ((generatedAxisGlobalOddFifthComparisonFiber k)⁻¹).val.1
      (qCoordinateGenerator i) = generatedAxisGlobalOddFifthInverseMaskGenerator k i := by
  change spinConjugation ((generatedAxisGlobalOddFifthComparisonFiber k).val.1)⁻¹
    (qCoordinateGenerator i) = _
  rw [map_inv]
  let a := spinConjugation (generatedAxisGlobalOddFifthComparisonFiber k).val.1
  change a.symm (qCoordinateGenerator i) = _
  apply a.injective
  rw [a.apply_symm_apply, generatedAxisGlobalOddFifthInverseMaskGenerator, map_mul,
    co1NonsplitAut_central]
  change qCoordinateGenerator i = qCentral (generatedAxisGlobalOddFifthInverseMaskPhases k i) *
    spinConjugation (generatedAxisGlobalOddFifthComparisonFiber k).val.1
      (generatedAxisGlobalQMask (generatedAxisGlobalOddFifthInverseMaskColumns k i))
  rw [generatedAxisGlobalOddFifthInverseMaskGenerator_forward,
    ← mul_assoc, fifth_inverse_central_square, one_mul]

/-- Each inverse cached lift retains its complete original binary base. -/
theorem generatedAxisGlobalOddFifthInverseMaskGenerator_base (k : Fin 2) (i : Fin 24) :
    toAdd (generatedAxisGlobalOddFifthInverseMaskGenerator k i).base =
      monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalOddFifthInverseMaskColumns k i) := by
  ext j
  change (0 : ZMod 2) +
    monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalOddFifthInverseMaskColumns k i) j = _
  exact zero_add _

/-- Each inverse cached lift retains its complete original central coefficient. -/
theorem generatedAxisGlobalOddFifthInverseMaskGenerator_coeff (k : Fin 2) (i : Fin 24) :
    toAdd (generatedAxisGlobalOddFifthInverseMaskGenerator k i).coeff =
      generatedAxisGlobalOddFifthInverseMaskPhases k i := by
  change generatedAxisGlobalOddFifthInverseMaskPhases k i + 0 +
    qBeta 0 (monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalOddFifthInverseMaskColumns k i)) = _
  rw [add_zero, qBeta_zero_left, add_zero]

/-- Every actual inverse original automorphism preserves the original square form. -/
theorem generatedAxisGlobalOddFifthInverseMaskAction_square (k : Fin 2)
    (v : Fin 24 → ZMod 2) :
    squareQuad (qBinaryAction
      (spinConjugation ((generatedAxisGlobalOddFifthComparisonFiber k)⁻¹).val.1) v) = squareQuad v := by
  change squareQuad (spinBinaryAction ((generatedAxisGlobalOddFifthComparisonFiber k)⁻¹).val.1 v) = _
  rw [((generatedAxisGlobalOddFifthComparisonFiber k)⁻¹).property]
  exact leechBinaryAction_squareQuad _ v

/-- The complete original inverse Q action is the checked original inverse polynomial mask action. -/
theorem generatedAxisGlobalOddFifthInverseMaskAction_actual (k : Fin 2) (v : ℕ) :
    spinConjugation ((generatedAxisGlobalOddFifthComparisonFiber k)⁻¹).val.1
      (generatedAxisGlobalQMask v) =
    generatedAxisGlobalQMaskImage (generatedAxisGlobalOddFifthInverseMaskColumns k)
      (generatedAxisGlobalOddFifthInverseMaskRows k)
      (generatedAxisGlobalOddFifthInverseMaskCoefficients k) v := by
  let a := spinConjugation ((generatedAxisGlobalOddFifthComparisonFiber k)⁻¹).val.1
  have hi (i : Fin 24) : a (qCoordinateGenerator i) =
      generatedAxisGlobalOddFifthInverseMaskGenerator k i :=
    generatedAxisGlobalOddFifthInverseMaskGenerator_actual k i
  have hb (i : Fin 24) : qBinaryAction a (Pi.single i 1) =
      monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalOddFifthInverseMaskColumns k i) := by
    have h := qBinaryAction_apply a (qCoordinateGenerator i)
    change qBinaryAction a (Pi.single i 1) = toAdd (a (qCoordinateGenerator i)).base at h
    rw [hi] at h
    exact h.trans (generatedAxisGlobalOddFifthInverseMaskGenerator_base k i)
  have hr : qCorrectionMatrix (qBinaryAction a) =
      monsterCo1GeometryBinaryMaskMatrix (generatedAxisGlobalOddFifthInverseMaskRows k) := by
    ext i j
    change (if i < j then qCocycleDifference (qBinaryAction a)
      (Pi.single i 1) (Pi.single j 1) else 0) = _
    simp only [qCocycleDifference_apply, hb]
    exact (generatedAxisGlobalOddFifthInverseMaskRows_checked k i j).symm
  have hc (i : Fin 24) : co1NonsplitAutPhase a (Pi.single i 1) =
      monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalOddFifthInverseMaskCoefficients k) i := by
    change toAdd (a (qCoordinateGenerator i)).coeff = _
    rw [hi, generatedAxisGlobalOddFifthInverseMaskGenerator_coeff]
    exact (generatedAxisGlobalOddFifthInverseMaskCoefficients_checked k i).symm
  exact generatedAxisGlobalQMaskImage_actual a
    (generatedAxisGlobalOddFifthInverseMaskAction_square k) _ _ _ hb hr hc v

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
