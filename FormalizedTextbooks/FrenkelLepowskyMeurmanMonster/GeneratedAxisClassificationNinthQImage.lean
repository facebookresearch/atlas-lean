/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthRepresentative

/-! The original nine-factor preferred-Q conjugation retains every central coefficient. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- Actual forward conjugation follows the nine original local factors. -/
def generatedNinthQImage (q : Q) : Q :=
  xiSpinGImage (xiSpinGammaImage (xiSpinGImage (xiSpinGammaImage (
    monsterSourcePermutationImage 1 (monsterSourcePermutationImage 0 (xiSpinGImage (
    xiSpinGammaImage (monsterSourcePermutationImage 1 (monsterSourcePermutationImage 0 (
    xiSpinGImage (xiSpinGammaImage (monsterSourcePermutationImage 1 (q)))))))))))))

/-- The explicit formula is conjugation by the literal original local spin word. -/
theorem generatedNinthQImage_eq (q : Q) :
    spinConjugation generatedNinthLocalFiber.val.1 q = generatedNinthQImage q := by
  change spinConjugation (xiSpinHolomorph *
    xiSpinHolomorph *
    monsterSourcePermutationSpin 1 *
    monsterSourcePermutationSpin 0 *
    xiSpinHolomorph *
    monsterSourcePermutationSpin 1 *
    monsterSourcePermutationSpin 0 *
    xiSpinHolomorph *
    monsterSourcePermutationSpin 1) q = _
  simp only [map_mul, MulAut.mul_apply]
  rw [xiSpinHolomorph_conjugation,
    xiSpinHolomorph_conjugation,
    monsterSourcePermutationSpin_conjugation,
    monsterSourcePermutationSpin_conjugation,
    xiSpinHolomorph_conjugation,
    monsterSourcePermutationSpin_conjugation,
    monsterSourcePermutationSpin_conjugation,
    xiSpinHolomorph_conjugation,
    monsterSourcePermutationSpin_conjugation]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
