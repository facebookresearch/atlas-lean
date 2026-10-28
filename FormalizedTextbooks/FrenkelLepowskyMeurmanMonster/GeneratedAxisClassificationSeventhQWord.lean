/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhQData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhQPreferred

/-! The three cached transitions are conjugations of the original preferred short lifts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Restriction of the genuine spin conjugation homomorphism to the original local fiber. -/
def generatedSeventhLocalQAction : localFiberSubgroup →* MulAut Q :=
  spinConjugation.comp ((MonoidHom.fst SpinHolomorph leechIsomSubgroup).comp
    localFiberSubgroup.subtype)

/-- The coordinate formula is the conjugation of the original seven-factor spin normalizer. -/
theorem generatedSeventh_spin_conjugation (q : Q) :
    spinConjugation generatedSeventhLocalFiber.val.1 q = generatedSeventhQImage q := by
  change generatedSeventhLocalQAction generatedSeventhLocalFiber q = _
  have hm : generatedSeventhLocalQAction generatedSeventhLocalFiber =
      generatedSeventhLocalQAction xiSpinLocalFiber *
      generatedSeventhLocalQAction (monsterSourcePermutationFiber 1) *
      generatedSeventhLocalQAction xiSpinLocalFiber *
      generatedSeventhLocalQAction (monsterSourcePermutationFiber 0) *
      generatedSeventhLocalQAction (monsterSourcePermutationFiber 1) *
      generatedSeventhLocalQAction (monsterSourcePermutationFiber 0) *
      generatedSeventhLocalQAction xiSpinLocalFiber := by
    simp only [generatedSeventhLocalFiber, map_mul]
  rw [hm]
  simp only [MulAut.mul_apply]
  have hxi (x : Q) : generatedSeventhLocalQAction xiSpinLocalFiber x =
      xiSpinGImage (xiSpinGammaImage x) := xiSpinHolomorph_conjugation x
  have hp (k : Fin 2) (x : Q) :
      generatedSeventhLocalQAction (monsterSourcePermutationFiber k) x =
        monsterSourcePermutationImage k x := monsterSourcePermutationSpin_conjugation k x
  simp only [hxi, hp]
  unfold generatedSeventhQImage generatedSeventhQWord
  simp only [List.foldl_cons, List.foldl_nil]
  simp only [generatedSeventhQGenerator, show (0 : Fin 3) ≠ 1 from by decide,
    show (1 : Fin 3) ≠ 0 from by decide, show (2 : Fin 3) ≠ 0 from by decide,
    show (2 : Fin 3) ≠ 1 from by decide, ite_true, ite_false]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
