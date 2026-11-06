/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortImage
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftYPhaseFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftPPhaseFast

/-! Literal phase matrices evaluate the unchanged actual preferred-Q conjugation. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The genuine y82 full-Q action evaluated using its certified literal phase matrix. -/
def generatedFourthLiftYQFast (q : Q) : Q :=
  monsterSpinHadamardImage
    (monsterMonomialDiagonalImage generatedFourthLiftYPhaseMatrix
      (monsterMonomialPermutationImage monsterSourceY82Shear
        (monsterSourceY82Translation * monsterSpinHadamardImage q *
          monsterSourceY82Translation⁻¹)))

/-- No quadratic or central phase changes under the literal y82 evaluation. -/
theorem generatedFourth_lift_y_q_fast (q : Q) :
    monsterSourceY82Image q = generatedFourthLiftYQFast q := by
  simp only [monsterSourceY82Image, generatedFourthLiftYQFast,
    generatedFourth_lift_y_phase_matrix]

/-- The corrected Parker permutation evaluated using its genuine literal phase matrix. -/
def generatedFourthLiftPQFast (q : Q) : Q :=
  monsterMonomialPermutationImage generatedFourthFlagLiftCode
    (monsterMonomialDiagonalImage generatedFourthLiftPPhaseMatrix q)

/-- The literal Parker evaluation retains the full actual Q image. -/
theorem generatedFourth_lift_p_q_fast (q : Q) :
    generatedFourthFlagLiftQImage q = generatedFourthLiftPQFast q := by
  simp only [generatedFourthFlagLiftQImage, generatedFourthLiftPQFast,
    generatedFourth_lift_p_phase_matrix]

/-- The exact corrected conjugation evaluated through the certified literal matrices. -/
noncomputable def generatedFourthLiftShortQFast (q : Q) : Q :=
  generatedFourthFlagXiCorrection *
    generatedFourthLiftYQFast (generatedFourthLiftPQFast
      (xiSpinGImage (xiSpinGammaImage (generatedFourthLiftYQFast q)))) *
        generatedFourthFlagXiCorrection⁻¹

/-- The literal evaluation is the actual corrected preferred-Q conjugation everywhere. -/
theorem generatedFourth_lift_short_q_fast (q : Q) :
    generatedFourthLiftCorrectedQImage q = generatedFourthLiftShortQFast q := by
  simp only [generatedFourthLiftCorrectedQImage, generatedFourthFlagNormalizedQImage,
    generatedFourthLiftShortQFast, generatedFourth_lift_y_q_fast, generatedFourth_lift_p_q_fast]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
