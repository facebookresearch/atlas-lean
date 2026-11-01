/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthInverseSpatialCacheData

/-! Six complete original inverse physical columns, with every sign and zero coefficient. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option maxRecDepth 20000
-- Normalize only six complete original physical inverse columns.
set_option maxHeartbeats 1000000000

/-- Each coefficient is the genuine full original inverse source-word coefficient. -/
theorem generatedAxisGlobalOddFourthInverseSpatialCacheCheck02_03
    (i : Fin 24) (j : Fin 6) :
    generatedAxisGlobalRationalSpatialInverseMatrix (generatedAxisGlobalOddFourthComparisonLetters 2)
      i ⟨18+j.val, by omega⟩ =
        (generatedAxisGlobalOddFourthInverseSpatialNumerator 2 i ⟨18+j.val, by omega⟩ : ℚ) / 2 := by
  have h : ∀ (i : Fin 24) (j : Fin 6),
      generatedAxisGlobalRationalSpatialInverseMatrix (generatedAxisGlobalOddFourthComparisonLetters 2)
        i ⟨18+j.val, by omega⟩ =
          (generatedAxisGlobalOddFourthInverseSpatialNumerator 2 i ⟨18+j.val, by omega⟩ : ℚ) / 2 := by
    decide +kernel
  exact h i j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
