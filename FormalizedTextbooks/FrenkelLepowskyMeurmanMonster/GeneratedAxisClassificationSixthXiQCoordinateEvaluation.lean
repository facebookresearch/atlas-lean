/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiQCoordinateData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQCoordinateEvaluation

/-! Checked coordinate images evaluate the full original Q automorphism
with its central correction. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 30000000 in
-- Bind24 original positive coordinate lifts to the actual corrected original Xi-word Q automorphism.
/-- Every coordinate-image table entry equals the literal original Q conjugation. -/
theorem generatedSixth_xi_coordinate_image_certificate : ∀ i : Fin 24,
    generatedSixthXiQImage (qCoordinateGenerator i) = generatedSixthXiCoordinateImage i := by
  have hb : ∀ i : Fin 24,
      (fun j : Fin 24 => Multiplicative.toAdd
        (generatedSixthXiQImage (qCoordinateGenerator i)).base j) =
      (fun j : Fin 24 => Multiplicative.toAdd (generatedSixthXiCoordinateImage i).base j) := by
    decide +kernel
  have hc : ∀ i : Fin 24,
      Multiplicative.toAdd (generatedSixthXiQImage (qCoordinateGenerator i)).coeff =
        Multiplicative.toAdd (generatedSixthXiCoordinateImage i).coeff := by
    decide +kernel
  intro i
  apply NormalizedCocycleExtension.Extension.ext
  · apply Multiplicative.toAdd.injective
    exact hb i
  · apply Multiplicative.toAdd.injective
    exact hc i

/-- The exact ordered generator-image evaluator retains the original central correction. -/
def generatedSixthXiQCoordinateEvaluation (q : Q) : Q :=
  monsterNortonCoordinateEvaluation generatedSixthXiCoordinateImage q

/-- The finite coordinate evaluator is the actual corrected original Xi-word
Q automorphism on every element. -/
theorem generatedSixth_xi_QCoordinateEvaluation_eq (q : Q) :
    generatedSixthXiQImage q = generatedSixthXiQCoordinateEvaluation q := by
  have hi (i : Fin 24) :
      spinConjugation (generatedSixthCorrectedGenerator 4).val.1 (qCoordinateGenerator i) =
        generatedSixthXiCoordinateImage i := by
    rw [generatedSixth_xi_QImage]
    exact generatedSixth_xi_coordinate_image_certificate i
  have h := monsterNortonCoordinateEvaluation_eq (generatedSixthCorrectedGenerator 4).val.1
    generatedSixthXiCoordinateImage hi q
  rw [generatedSixth_xi_QImage] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
