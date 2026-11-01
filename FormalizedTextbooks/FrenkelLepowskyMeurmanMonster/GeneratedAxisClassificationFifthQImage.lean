/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthRepresentative

/-! The full actual four-factor inverse Q action, retaining every preferred central phase. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual inverse word Xi*P1*P0*Xi applied to Q, with its central coordinate. -/
def generatedFifthInverseQImage (q : Q) : Q :=
  xiSpinGImage (xiSpinGammaImage (monsterSourcePermutationImage 1
    (monsterSourcePermutationImage 0 (xiSpinGImage (xiSpinGammaImage q)))))

/-- The explicit four-factor formula is genuine conjugation in the original spin normalizer. -/
theorem generatedFifthInverseQImage_eq (q : Q) :
    spinConjugation (generatedFifthLocalFiber⁻¹).val.1 q =
      generatedFifthInverseQImage q := by
  change spinConjugation ((xiSpinHolomorph⁻¹ * (monsterSourcePermutationSpin 0)⁻¹ *
    (monsterSourcePermutationSpin 1)⁻¹ * xiSpinHolomorph⁻¹)⁻¹) q = _
  simp only [mul_inv_rev, inv_inv, map_mul]
  change spinConjugation xiSpinHolomorph (spinConjugation (monsterSourcePermutationSpin 1)
    (spinConjugation (monsterSourcePermutationSpin 0) (spinConjugation xiSpinHolomorph q))) = _
  rw [xiSpinHolomorph_conjugation, monsterSourcePermutationSpin_conjugation,
    monsterSourcePermutationSpin_conjugation, xiSpinHolomorph_conjugation]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
