/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthInverseCoordinates

/-! A certified coordinate separates every other inverse pair image from the genuine pair family. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The three selected genuine minus-pair labels, expressed in physical coordinates. -/
def generatedSixthPairExceptional (s : Fin 2) (a b : Fin 24) : Prop :=
  s = 0 ∧ ((a = 16 ∧ b = 17) ∨ (a = 16 ∧ b = 19) ∨ (a = 17 ∧ b = 19))

instance (s : Fin 2) (a b : Fin 24) : Decidable (generatedSixthPairExceptional s a b) := by
  unfold generatedSixthPairExceptional
  infer_instance

/-- A coordinate whose inverse integer numerator cannot belong to a shortest pair vector. -/
def generatedSixthPairWitness : Fin 2 → Fin 24 → Fin 24 → Fin 24 :=
  ![![![0, 0, 0, 2, 0, 1, 1, 0, 0, 3, 5, 0, 9, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 4, 0, 1, 0, 0, 1, 6, 0, 0, 2, 0, 3, 2, 0, 0, 0, 1, 0, 4, 5, 3, 2],
      ![0, 0, 0, 0, 1, 0, 0, 1, 4, 0, 0, 2, 0, 3, 2, 0, 0, 0, 1, 0, 8, 4, 3, 2],
      ![0, 0, 0, 0, 0, 1, 1, 0, 0, 2, 2, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 3, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 4, 0, 1, 1, 1, 1],
      ![0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 3, 0, 1, 1, 1, 1],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 2, 0, 0, 0, 1, 0, 4, 5, 3, 2],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 0, 1, 0, 2, 2, 2, 4],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 3, 3, 4, 2],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 2, 8],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 3, 2],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 2],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 5, 4, 0, 1, 0, 0, 1, 5, 0, 0, 2, 0, 3, 2, 0, 0, 0, 1, 0, 4, 6, 3, 2],
      ![0, 0, 0, 2, 0, 1, 1, 0, 0, 3, 10, 0, 5, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 2, 0, 1, 1, 0, 0, 3, 4, 0, 4, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 1, 0, 0, 1, 2, 0, 0, 3, 0, 2, 3, 0, 0, 0, 1, 0, 2, 2, 2, 3],
      ![0, 0, 0, 0, 0, 4, 2, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 3, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 8, 0, 1, 1, 1, 1],
      ![0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 2, 0, 1, 1, 1, 1],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 6, 0, 5, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 4, 2, 0, 0, 0, 1, 0, 3, 3, 8, 2],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 2, 0, 0, 0, 1, 0, 4, 5, 3, 2],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 2, 0, 0, 0, 1, 0, 4, 6, 3, 2],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 4, 5, 3, 2],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]]

/-- The original inverse numerator applied to the signed pair at its selected coordinate. -/
def generatedSixthPairWitnessNumerator (s : Fin 2) (a b : Fin 24) : ℤ :=
  4 * (generatedSixthInverseNumerator (generatedSixthPairWitness s a b) a +
    (if s = 0 then -1 else 1) *
      generatedSixthInverseNumerator (generatedSixthPairWitness s a b) b)

set_option maxHeartbeats 4000000 in
-- Every one of the 549 excluded original pair labels gets a genuine integer-coordinate check.
/-- The certified numerator squares exclude zero and the only nonzero pair-coordinate square. -/
theorem generatedSixth_pair_witness_certificate : ∀ s : Fin 2, ∀ a b : Fin 24,
    a < b → ¬ generatedSixthPairExceptional s a b →
      generatedSixthPairWitnessNumerator s a b ^ 2 ≠ 0 ∧
        generatedSixthPairWitnessNumerator s a b ^ 2 ≠ 1024 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
