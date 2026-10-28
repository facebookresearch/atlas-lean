/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhInverseCoordinates

/-! A certified coordinate separates every other inverse pair image from the genuine pair family. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The three selected genuine minus-pair labels, expressed in physical coordinates. -/
def generatedSeventhPairExceptional (s : Fin 2) (a b : Fin 24) : Prop :=
  s = 0 ∧ ((a = 16 ∧ b = 17) ∨ (a = 16 ∧ b = 19) ∨ (a = 17 ∧ b = 19))

instance (s : Fin 2) (a b : Fin 24) : Decidable (generatedSeventhPairExceptional s a b) := by
  unfold generatedSeventhPairExceptional
  infer_instance

/-- A coordinate whose inverse integer numerator cannot belong to a shortest pair vector. -/
def generatedSeventhPairWitness : Fin 2 → Fin 24 → Fin 24 → Fin 24 :=
  ![![![0, 0, 0, 4, 0, 1, 1, 0,
        0, 1, 1, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 6, 0, 1, 0, 0, 1,
        1, 0, 0, 1, 0, 0, 0, 0,
        1, 1, 0, 1, 1, 1, 1, 1],
      ![0, 0, 0, 0, 1, 0, 0, 1,
        1, 0, 0, 1, 0, 0, 0, 0,
        1, 1, 0, 1, 1, 1, 1, 1],
      ![0, 0, 0, 0, 0, 1, 1, 0,
        0, 1, 1, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 4,
        2, 0, 0, 2, 0, 0, 0, 0,
        3, 3, 0, 3, 3, 3, 3, 3],
      ![0, 0, 0, 0, 0, 0, 6, 0,
        0, 2, 2, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0,
        0, 2, 2, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0,
        2, 0, 0, 2, 0, 0, 0, 0,
        3, 3, 0, 3, 3, 3, 3, 3],
      ![0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 4, 0, 0, 0, 0,
        2, 2, 0, 2, 2, 2, 2, 2],
      ![0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 6, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0,
        2, 2, 0, 2, 2, 2, 2, 2],
      ![0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 4,
        0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 6, 0,
        0, 0, 1, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 1, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 8, 4, 12, 12],
      ![0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 8, 4, 12, 12],
      ![0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 8, 4, 12, 12],
      ![0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 4, 8, 8],
      ![0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 4, 4],
      ![0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 16],
      ![0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 4, 4, 0, 1, 0, 0, 1,
        1, 0, 0, 1, 0, 0, 0, 0,
        1, 1, 0, 1, 1, 1, 1, 1],
      ![0, 0, 0, 5, 0, 1, 1, 0,
        0, 1, 1, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 5, 0, 1, 1, 0,
        0, 1, 1, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 1, 0, 0, 1,
        1, 0, 0, 1, 0, 0, 0, 0,
        1, 1, 0, 1, 1, 1, 1, 1],
      ![0, 0, 0, 0, 0, 5, 5, 0,
        0, 2, 2, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 4,
        2, 0, 0, 2, 0, 0, 0, 0,
        3, 3, 0, 3, 3, 3, 3, 3],
      ![0, 0, 0, 0, 0, 0, 0, 4,
        2, 0, 0, 2, 0, 0, 0, 0,
        3, 3, 0, 3, 3, 3, 3, 3],
      ![0, 0, 0, 0, 0, 0, 0, 0,
        0, 2, 2, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0,
        0, 5, 5, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 4, 0, 0, 0, 0,
        2, 2, 0, 2, 2, 2, 2, 2],
      ![0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 4, 0, 0, 0, 0,
        2, 2, 0, 2, 2, 2, 2, 2],
      ![0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 4, 4, 0,
        0, 0, 1, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 5,
        0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 5,
        0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 1, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0]]]

/-- The original inverse numerator applied to the signed pair at its selected coordinate. -/
def generatedSeventhPairWitnessNumerator (s : Fin 2) (a b : Fin 24) : ℤ :=
  4 * (generatedSeventhInverseNumerator (generatedSeventhPairWitness s a b) a +
    (if s = 0 then -1 else 1) *
      generatedSeventhInverseNumerator (generatedSeventhPairWitness s a b) b)

/-- The certified numerator squares exclude zero and the only nonzero pair-coordinate square. -/
theorem generatedSeventh_pair_witness_certificate : ∀ s : Fin 2, ∀ a b : Fin 24,
    a < b → ¬ generatedSeventhPairExceptional s a b →
      generatedSeventhPairWitnessNumerator s a b ^ 2 ≠ 0 ∧
        generatedSeventhPairWitnessNumerator s a b ^ 2 ≠ 1024 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
