/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthShortRowNonzero

/-! The actual original signed numerator uses the checked preferred pair enumeration and the
original octad formula. No input coefficient or phase is inferred from a binary mask. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Actual original signed numerator evaluated with the checked preferred pair coordinates. -/
def generatedNinthShortRowNumeratorFast (k : Fin 4136) : ℤ :=
  if h : k.val < 552 then
    let p : Fin 276 := ⟨k.val % 276, Nat.mod_lt _ (by decide)⟩
    generatedFifthFinalPairNumerator (⟨k.val / 276, by omega⟩ : Fin 2)
      (generatedNinthCoordinatePairData p).1 (generatedNinthCoordinatePairData p).2
  else
    generatedFifthFinalOctadNumerator (⟨(k.val - 552) / 64, by omega⟩ : Fin 56)
      (⟨(k.val - 552) % 64, Nat.mod_lt _ (by decide)⟩ : Fin 64)

/-- The integer formula agrees with the original actual source numerator for every address. -/
theorem generatedNinth_short_row_numerator_fast_actual (k : Fin 4136) :
    generatedNinthOriginalShortNumerator (generatedNinthShortRowSource k) =
      generatedNinthShortRowNumeratorFast k := by
  unfold generatedNinthShortRowSource generatedNinthShortRowNumeratorFast
  split_ifs with h
  · simp only [generatedNinthOriginalShortNumerator, generatedNinth_coordinate_pair_actual]
  · rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
