/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotsData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthShortRowNumeratorFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.NortonUIntegerSpinBasic

/-! Candidate eight-slot numerator signs derived from the original integer source data.
Separate certificates compare every bit to the original signed numerator. The full source
word phase is supplied by the independent six-field source-row certificates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Candidate negative-numerator bits for the eight chronological slots in each octad. -/
def generatedNinthOctadSlotNegativeWords : Array ℕ := #[
  1, 13, 0, 2, 13, 0, 3, 1, 3, 4, 0, 14, 3, 3, 0, 0,
  0, 14, 2, 2, 0, 8, 0, 7, 4, 8, 0, 4, 2, 2, 13, 1,
  3, 4, 0, 8, 1, 3, 3, 3, 3, 2, 3, 11, 2, 14, 0, 1,
  2, 7, 1, 2, 7, 8, 3, 14, 8, 3, 3, 14, 3, 3, 13, 0,
  11, 14, 1, 2, 2, 3, 8, 0, 1, 0, 0, 8, 4, 13, 7, 3,
  3, 3, 1, 0, 2, 7, 1, 0, 13, 1, 3, 1, 7, 3, 0, 3,
  0, 0, 2, 1, 0, 2, 13, 0, 0, 2, 3, 13, 11, 3, 11, 8,
  1, 1, 1, 2, 0, 1, 3, 0, 2, 3, 0, 2, 11, 1, 3, 2,
  8, 2, 0, 1, 14, 0, 2, 7, 11, 8, 11, 4, 3, 1, 3, 11,
  8, 14, 1, 2, 2, 3, 3, 7, 0, 3, 1, 2, 1, 2, 1, 1,
  2, 3, 3, 2, 2, 1, 7, 2, 7, 2, 2, 2, 14, 1, 3, 4,
  1, 8, 1, 2, 8, 2, 3, 1, 3, 3, 0, 1, 2, 8, 2, 4,
  4, 1, 1, 3, 2, 1, 4, 8, 4, 3, 0, 0, 4, 1, 7, 3,
  2, 8, 0, 2, 1, 1, 0, 13, 1, 2, 0, 3, 3, 14, 1, 1,
  13, 2, 0, 2, 2, 2, 0, 1, 1, 2, 0, 2, 0, 2, 2, 1,
  11, 1, 0, 1, 0, 2, 0, 8, 2, 2, 1, 2, 1, 1, 7, 13,
  1, 4, 1, 14, 0, 1, 2, 1, 0, 4, 2, 2, 1, 3, 3, 7,
  1, 2, 1, 3, 2, 0, 1, 3, 0, 2, 1, 1, 1, 2, 0, 2,
  2, 1, 0, 1, 1, 4, 0, 3, 8, 3, 2, 1, 0, 2, 4, 2,
  13, 1, 3, 2, 2, 1, 1, 3, 0, 2, 0, 1, 14, 0, 0, 0,
  0, 2, 7, 3, 2, 0, 2, 2, 13, 14, 2, 1, 2, 1, 1, 2,
  1, 0, 2, 1, 1, 3, 0, 1, 1, 3, 3, 2, 1, 2, 2, 2,
  2, 2, 1, 1, 1, 2, 1, 2, 0, 1, 3, 3, 11, 2, 2, 1,
  2, 14, 8, 8, 13, 1, 2, 2, 1, 0, 3, 0, 0, 8, 3, 2,
  1, 7, 3, 11, 0, 11, 1, 0, 3, 0, 2, 2, 2, 0, 3, 4,
  0, 0, 3, 2, 3, 2, 1, 3, 3, 1, 1, 1, 0, 0, 13, 14,
  7, 3, 0, 1, 2, 1, 2, 1, 1, 1, 1, 1, 2, 2, 14, 4,
  4, 2, 1, 2, 0, 0, 3, 2, 3, 0, 4, 11, 13, 0, 11, 2,
  1, 1, 13, 14, 13, 13, 4, 3, 1, 7, 2, 170, 7, 3, 0, 11,
  13, 1, 3, 1, 2, 2, 11, 0, 0, 13, 13, 7, 13, 0, 0, 1,
  2, 8, 4, 0, 13, 13, 0, 2, 2, 2, 11, 3, 3, 1, 13, 4,
  7, 3, 1, 1, 3, 1, 2, 7, 8, 14, 7, 0, 1, 0, 2, 0,
  0, 3, 1, 2, 1, 0, 0, 3, 1, 2, 1, 0, 3, 3, 14, 2,
  0, 2, 0, 0, 3, 7, 3, 2, 3, 3, 0, 1, 1, 1, 0, 3,
  2, 1, 0, 0, 1, 11, 3, 1, 0, 0, 3, 3, 0, 3, 7, 3,
  0, 14, 1, 0, 3, 3, 11, 3, 0, 2, 1, 1, 0, 0, 2, 2,
  0, 1, 0, 3, 4, 2, 1, 0, 2, 3, 0, 14, 3, 1, 2, 0,
  0, 2, 4, 8, 11, 3, 14, 3, 8, 1, 1, 0, 3, 7, 13, 0,
  2, 1, 3, 3, 7, 14, 1, 11, 3, 3, 3, 3, 13, 7, 3, 3,
  1, 1, 1, 14, 2, 8, 0, 4, 0, 13, 3, 11, 3, 3, 1, 0,
  0, 1, 0, 0, 0, 4, 3, 1, 0, 0, 0, 1, 2, 3, 4, 3,
  3, 4, 2, 3, 1, 1, 14, 3, 0, 3, 3, 3, 11, 7, 8, 1,
  2, 3, 0, 2, 3, 1, 13, 14, 3, 0, 1, 3, 0, 3, 0, 3,
  3, 1, 0, 1, 1, 1, 0, 3, 3, 3, 3, 0, 1, 0, 0, 8,
  0, 3, 0, 11, 2, 3, 14, 1, 3, 1, 1, 2, 1, 3, 1, 0,
  0, 0, 13, 13, 1, 1, 0, 0, 2, 2, 2, 11, 8, 0, 3, 8,
  3, 1, 3, 1, 1, 3, 2, 2, 2, 0, 1, 1, 0, 2, 1, 3,
  1, 0, 3, 0, 1, 0, 2
]

/-- The candidate signed integer numerator in one nonempty original source slot. -/
def generatedNinthOctadSlotNumeratorFast (o : Fin 759) (j : Fin 8) : ℤ :=
  if generatedNinthOctadSourceSlotWord o j = 0 then 0
  else if (generatedNinthOctadSlotNegativeWords[o.val]!).testBit j.val then -2 else 2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
