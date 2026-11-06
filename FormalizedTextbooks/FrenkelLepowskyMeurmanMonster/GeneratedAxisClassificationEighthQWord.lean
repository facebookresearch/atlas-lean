/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthRepresentative
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthQWord

/-! Full original preferred-Q action of the seven-factor eighth local word. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Each primitive is the genuine original permutation or Xi preferred-Q image. -/
def generatedEighthQGenerator (k : Fin 3) (q : Q) : Q := generatedSixthQGenerator k q

/-- The seven original factors in actual application order. -/
def generatedEighthQWord : List (Fin 3) := [2, 0, 1, 2, 0, 1, 2]

/-- The full original preferred-Q action, including its central coefficient. -/
def generatedEighthQImage (q : Q) : Q :=
  generatedEighthQWord.foldl (fun x k => generatedEighthQGenerator k x) q

/-- The finite coordinate action is exactly conjugation by the genuine local spin word. -/
theorem generatedEighth_spin_conjugation (q : Q) :
    spinConjugation generatedEighthLocalFiber.val.1 q = generatedEighthQImage q := by
  change generatedSixthLocalQAction generatedEighthLocalFiber q = _
  have hm : generatedSixthLocalQAction generatedEighthLocalFiber =
      generatedSixthLocalQAction xiSpinLocalFiber *
      generatedSixthLocalQAction (monsterSourcePermutationFiber 1) *
      generatedSixthLocalQAction (monsterSourcePermutationFiber 0) *
      generatedSixthLocalQAction xiSpinLocalFiber *
      generatedSixthLocalQAction (monsterSourcePermutationFiber 1) *
      generatedSixthLocalQAction (monsterSourcePermutationFiber 0) *
      generatedSixthLocalQAction xiSpinLocalFiber := by
    simp only [generatedEighthLocalFiber, map_mul]
  rw [hm]
  simp only [MulAut.mul_apply]
  have hxi (x : Q) : generatedSixthLocalQAction xiSpinLocalFiber x =
      xiSpinGImage (xiSpinGammaImage x) := xiSpinHolomorph_conjugation x
  have hp (k : Fin 2) (x : Q) :
      generatedSixthLocalQAction (monsterSourcePermutationFiber k) x =
        monsterSourcePermutationImage k x := monsterSourcePermutationSpin_conjugation k x
  simp only [hxi, hp]
  unfold generatedEighthQImage generatedEighthQWord
  simp only [List.foldl_cons, List.foldl_nil, generatedEighthQGenerator]
  simp only [generatedSixthQGenerator, show (0 : Fin 3) ≠ 1 from by decide,
    show (1 : Fin 3) ≠ 0 from by decide, show (2 : Fin 3) ≠ 0 from by decide,
    show (2 : Fin 3) ≠ 1 from by decide, ite_true, ite_false]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
