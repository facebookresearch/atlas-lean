/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignOctadAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadProductPhase

/-! Efficient exact preferred-Q phases: a family constant plus its physical sign character. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The physical negative-position character of an actual code on an outgoing octad row. -/
def generatedFifthSignNegativeCharacter (a : Fin 4096) (j : Fin 56) (e : Fin 64) : ZMod 2 :=
  ∑ i : Fin 24, golayBooleanCast ((generatedFifthXiShortCachedSignMask j e).testBit i.val) *
    golayBooleanCast ((golayEncodedMask a.val).testBit i.val)

/-- The phase constant depends on the genuine code, actual modulation and actual family. -/
def generatedFifthSignFamilyConstant (a : Fin 4096) (m : SpinIndex) (j : Fin 56) : ZMod 2 :=
  spinDot (golayLabelCoefficients a) (sourceWordTheta (generatedFifthEvenRootCode j)) +
    spinDot m (golayLabelCoefficients (generatedFifthEvenRootCode j))

/-- The full actual conjugation phase splits into a family constant and physical character. -/
theorem generatedFifth_sign_short_phase_formula (q : Q) (a : Fin 4096)
    (ha : spinTranslation q = golayLabelCoefficients a)
    (ho : spinDot (spinModulation q) (Pi.single 11 1) = 0) (j : Fin 56) (e : Fin 64) :
    generatedFifthSignCachedShortPhase q (Sum.inr (j, e)) =
      generatedFifthSignFamilyConstant a (spinModulation q) j +
        generatedFifthSignNegativeCharacter a j e := by
  simp only [generatedFifthSignCachedShortPhase, qBeta_spin_coordinates,
    generatedFifthXiShortCachedQ, generatedAxisFourthQFromSpin_translation,
    generatedAxisFourthQFromSpin_modulation, ha]
  rw [spinDot_add_right, spinDot_add_left]
  rw [spinDot_comm (griessOctadOmegaCoefficient e • Pi.single 11 1) (spinModulation q),
    spinDot_smul_right, ho, mul_zero, add_zero]
  rw [spinDot_comm (golayLabelCoefficients a) (golaySyndrome _), golaySyndrome_spinDot,
    spinDot_comm (golayLabelCoefficients (generatedFifthEvenRootCode j))]
  have hn : (∑ i : Fin 24,
      integerParity (fun i =>
        if (generatedFifthXiShortCachedSignMask j e).testBit i.val then (1 : ℤ) else 0) i *
          golayEncoder (golayLabelCoefficients a) i) =
      generatedFifthSignNegativeCharacter a j e := by
    apply Finset.sum_congr rfl
    intro i _
    rw [golayLabelEncoder_boolean]
    cases h : (generatedFifthXiShortCachedSignMask j e).testBit i.val <;>
      simp [integerParity, h, golayBooleanCast]
  rw [hn]
  exact add_right_comm _ _ _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
