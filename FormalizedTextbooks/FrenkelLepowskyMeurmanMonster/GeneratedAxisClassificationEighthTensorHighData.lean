/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthSpatial
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthQSupportSquares
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthHighPairCoefficients
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.CentralizerGeometryShortLines

/-! Literal source addresses and physical labels for twelve candidate high odd rows.
Their actual permutation and coefficient bindings are proved separately. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Actual source sign and nonzero physical coordinate for each selected pair. -/
def generatedEighthHighSourceCoordinates : Fin 12 → Fin 2 × Fin 24 :=
  ![(0, 4), (0, 10), (0, 11), (0, 14), (0, 15), (0, 18),
    (0, 23), (1, 5), (1, 12), (1, 13), (1, 17), (1, 21)]

/-- Original odd-code labels, with exceptional physical coordinate twenty. -/
def generatedEighthHighOddCode : Fin 12 → Fin 2048 :=
  ![1270, 1337, 1735, 53, 203, 235, 117, 1802, 0, 6, 232, 120]

/-- Literal physical signs, which are distinct from preferred-Q central phases. -/
def generatedEighthHighPhysicalSign : Fin 12 → ℤ :=
  ![1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1]

/-- Every selected physical source coordinate differs from zero. -/
theorem generatedEighth_high_source_ne_zero : ∀ j : Fin 12,
    (generatedEighthHighSourceCoordinates j).2 ≠ 0 := by decide +kernel

/-- The actual coordinate-pair catalogue address, with no discovery index assumption. -/
def generatedEighthHighSourcePair (j : Fin 12) : Fin 276 :=
  griessPairIndex 0 (generatedEighthHighSourceCoordinates j).2
    (generatedEighth_high_source_ne_zero j).symm

/-- The corresponding actual preferred source label. -/
def generatedEighthHighSource (j : Fin 12) : GriessShortIndex :=
  Sum.inl ((generatedEighthHighSourceCoordinates j).1, generatedEighthHighSourcePair j)

/-- The actual preferred target label on the original odd dictionary. -/
def generatedEighthHighTarget (j : Fin 12) : GriessShortIndex :=
  Sum.inr (Sum.inr (generatedEighthHighOddCode j, 20))

/-- The genuine source catalogue has the intended ordered coordinates. -/
theorem generatedEighth_high_source_coordinates (j : Fin 12) :
    griessCoordinatePair (generatedEighthHighSourcePair j) =
      (0, (generatedEighthHighSourceCoordinates j).2) := by
  rw [generatedEighthHighSourcePair, griessPairIndex_coordinates]
  have h : (0 : Fin 24) < (generatedEighthHighSourceCoordinates j).2 := by
    have hn := generatedEighth_high_source_ne_zero j
    have hv : (generatedEighthHighSourceCoordinates j).2.val ≠ 0 := by
      intro he
      apply hn
      exact Fin.ext he
    omega
  simp only [h, ite_true]

set_option maxHeartbeats 4000000 in
-- Compare all 288 original forward coordinates with the genuine odd catalogue formula.
/-- Each literal candidate is the exact signed original forward physical pair image. -/
theorem generatedEighth_high_physical_certificate : ∀ j : Fin 12, ∀ i : Fin 24,
    generatedEighthFrameVectorData 7 0 i +
      (if (generatedEighthHighSourceCoordinates j).1 = 0 then -1 else 1) *
        generatedEighthFrameVectorData 7 (generatedEighthHighSourceCoordinates j).2 i =
      2 * generatedEighthHighPhysicalSign j *
        griessShortIntegral (generatedEighthHighTarget j) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
