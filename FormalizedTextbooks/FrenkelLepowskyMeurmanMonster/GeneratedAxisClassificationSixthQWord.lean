/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthQData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthQPreferred

/-! The three cached transitions are conjugations of the original preferred short lifts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Restriction of the genuine spin conjugation homomorphism to the original local fiber. -/
def generatedSixthLocalQAction : localFiberSubgroup →* MulAut Q :=
  spinConjugation.comp ((MonoidHom.fst SpinHolomorph leechIsomSubgroup).comp
    localFiberSubgroup.subtype)

/-- The coordinate formula is the conjugation of the original eight-factor spin normalizer. -/
theorem generatedSixth_spin_conjugation (q : Q) :
    spinConjugation generatedSixthLocalFiber.val.1 q = generatedSixthQImage q := by
  change generatedSixthLocalQAction generatedSixthLocalFiber q = _
  have hm : generatedSixthLocalQAction generatedSixthLocalFiber =
      generatedSixthLocalQAction xiSpinLocalFiber *
      generatedSixthLocalQAction (monsterSourcePermutationFiber 1) *
      generatedSixthLocalQAction xiSpinLocalFiber *
      generatedSixthLocalQAction (monsterSourcePermutationFiber 0) *
      generatedSixthLocalQAction (monsterSourcePermutationFiber 1) *
      generatedSixthLocalQAction (monsterSourcePermutationFiber 0) *
      generatedSixthLocalQAction xiSpinLocalFiber *
      generatedSixthLocalQAction (monsterSourcePermutationFiber 0) := by
    simp only [generatedSixthLocalFiber, map_mul]
  rw [hm]
  simp only [MulAut.mul_apply]
  have hxi (x : Q) : generatedSixthLocalQAction xiSpinLocalFiber x =
      xiSpinGImage (xiSpinGammaImage x) := xiSpinHolomorph_conjugation x
  have hp (k : Fin 2) (x : Q) :
      generatedSixthLocalQAction (monsterSourcePermutationFiber k) x =
        monsterSourcePermutationImage k x := monsterSourcePermutationSpin_conjugation k x
  simp only [hxi, hp]
  unfold generatedSixthQImage generatedSixthQWord
  simp only [List.foldl_cons, List.foldl_nil]
  simp only [generatedSixthQGenerator, show (0 : Fin 3) ≠ 1 from by decide,
    show (1 : Fin 3) ≠ 0 from by decide, show (2 : Fin 3) ≠ 0 from by decide,
    show (2 : Fin 3) ≠ 1 from by decide, ite_true, ite_false]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
