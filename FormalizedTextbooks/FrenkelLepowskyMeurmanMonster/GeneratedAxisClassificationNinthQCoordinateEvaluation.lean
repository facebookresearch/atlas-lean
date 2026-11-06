/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthQCoordinateData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQCoordinateEvaluation

/-! Checked coordinate images evaluate the full original Q automorphism
with its central correction. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 30000000 in
-- Bind24 original positive coordinate lifts to the actual nine-factor Q automorphism.
/-- Every coordinate-image table entry equals the literal original Q conjugation. -/
theorem generatedNinth_coordinate_image_certificate : ∀ i : Fin 24,
    generatedNinthQImage (qCoordinateGenerator i) = generatedNinthCoordinateImage i := by
  have hb : ∀ i : Fin 24,
      (fun j : Fin 24 => Multiplicative.toAdd
        (generatedNinthQImage (qCoordinateGenerator i)).base j) =
      (fun j : Fin 24 => Multiplicative.toAdd (generatedNinthCoordinateImage i).base j) := by
    decide +kernel
  have hc : ∀ i : Fin 24,
      Multiplicative.toAdd (generatedNinthQImage (qCoordinateGenerator i)).coeff =
        Multiplicative.toAdd (generatedNinthCoordinateImage i).coeff := by
    decide +kernel
  intro i
  apply NormalizedCocycleExtension.Extension.ext
  · apply Multiplicative.toAdd.injective
    exact hb i
  · apply Multiplicative.toAdd.injective
    exact hc i

/-- The exact ordered generator-image evaluator retains the original central correction. -/
def generatedNinthQCoordinateEvaluation (q : Q) : Q :=
  monsterNortonCoordinateEvaluation generatedNinthCoordinateImage q

/-- The finite coordinate evaluator is the actual nine-factor Q automorphism on every element. -/
theorem generatedNinth_QCoordinateEvaluation_eq (q : Q) :
    generatedNinthQImage q = generatedNinthQCoordinateEvaluation q := by
  have hi (i : Fin 24) :
      spinConjugation generatedNinthLocalFiber.val.1 (qCoordinateGenerator i) =
        generatedNinthCoordinateImage i := by
    rw [generatedNinthQImage_eq]
    exact generatedNinth_coordinate_image_certificate i
  have h := monsterNortonCoordinateEvaluation_eq generatedNinthLocalFiber.val.1
    generatedNinthCoordinateImage hi q
  rw [generatedNinthQImage_eq] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
