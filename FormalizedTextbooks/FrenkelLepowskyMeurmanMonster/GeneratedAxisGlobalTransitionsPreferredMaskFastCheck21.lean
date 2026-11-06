/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPreferredMaskFastData

/-! Bounded kernel checks against the complete original preferred octad catalogue. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 100000000

/-- Original code labels and all eight increasing physical coordinates are checked together. -/
theorem generatedAxisGlobalPreferredMaskFastCheck21 (i : Fin 32) :
    generatedAxisGlobalPreferredMaskOctadCode ⟨672+i.val, by omega⟩ =
      generatedAxisGlobalOctadCodeData ⟨672+i.val, by omega⟩ ∧
    ∀ k : Fin 8, generatedAxisGlobalPreferredMaskOctadCoordinate ⟨672+i.val, by omega⟩ k =
      generatedAxisGlobalOctadCoordinatesData ⟨672+i.val, by omega⟩ k := by
  have h : ∀ i : Fin 32,
      generatedAxisGlobalPreferredMaskOctadCode ⟨672+i.val, by omega⟩ =
        generatedAxisGlobalOctadCodeData ⟨672+i.val, by omega⟩ ∧
      ∀ k : Fin 8, generatedAxisGlobalPreferredMaskOctadCoordinate ⟨672+i.val, by omega⟩ k =
        generatedAxisGlobalOctadCoordinatesData ⟨672+i.val, by omega⟩ k := by
    decide +kernel
  exact h i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
