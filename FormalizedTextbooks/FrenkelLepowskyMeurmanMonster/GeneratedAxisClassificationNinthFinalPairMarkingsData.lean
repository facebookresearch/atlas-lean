/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthFinalPairInteger

/-! Candidate signed-pair markings for comparison with the actual original integer formulas. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The eight displayed labels in the actual preferred signed-pair coordinate catalogue. -/
def generatedNinthFinalPairMarkings : Finset (Fin 2 × Fin 276) :=
  {(1, 22), (0, 37), (0, 46), (1, 133), (0, 154), (1, 187), (1, 231), (0, 267)}

/-- The displayed preferred signed-pair labels are eight distinct genuine catalogue indices. -/
theorem generatedNinth_final_pair_markings_card : generatedNinthFinalPairMarkings.card = 8 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
