/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The literal Norton u word in the actual generated group, with its triality label explicit.
Numerical source: public mmgroup bimm/p3_to_mm.py at commit
728688938a1c9fd27f3aee9b63464ea6b8d17965 (BSD-2-Clause), discovery runtime 1.0.8.
The word is y_52 x_1801 d_70f p_154721763 l_2 p_1460160 l_2.
Our left-action assignment uses the inverse permutation lifts and l_2 = xiSpinGenerated.
The parameter tau must still be compared with the source t_1 operator before a source
presentation relation can be transported. This file asserts no such relation.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationMonomialP1Operator
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.XiSpinLeechCompatibility

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The source y label interpreted through a specified actual triality element. -/
noncomputable def y555NortonY (tau : ↥G) (d : Fin 4096) (ε : ZMod 2) : ↥G :=
  tau⁻¹ * sourceGeneratedCode d ε * tau

/-- The literal seven-factor u word, including the central sign in x_1801. -/
noncomputable def y555NortonU (tau : ↥G) : ↥G :=
  y555NortonY tau 82 0 * sourceGeneratedCode 2049 1 *
    sourceGeneratedCocode (golayLabelCoefficients 1807) *
      (monsterSourcePermutationGenerated 0)⁻¹ * xiSpinGenerated *
        (monsterSourcePermutationGenerated 1)⁻¹ * xiSpinGenerated

/-- The same actual word with the checked Parker inverse correction exposed. -/
theorem y555NortonU_corrected_word (tau : ↥G) :
    y555NortonU tau =
      y555NortonY tau 82 0 * sourceGeneratedCode 2049 1 *
        sourceGeneratedCocode (golayLabelCoefficients 1807) *
          (monsterSourcePermutationGenerated 0)⁻¹ * xiSpinGenerated *
            (sourceGeneratedCocode (golayLabelCoefficients 515) *
              monsterSourcePermutationGenerated 1) * xiSpinGenerated := by
  rw [y555NortonU, monsterSourcePermutationP1_generated_inverse]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
